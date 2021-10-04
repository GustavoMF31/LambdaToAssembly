module Compile (Expr(..), toDeBruijn, compile, asmToString) where

import Numeric.Natural (Natural)
import Data.Bifunctor (second)
import Data.List.NonEmpty (NonEmpty ((:|)))

import Asm
import Control.Monad.State (State, MonadState (get, put), runState)

elemIndexNat :: Eq a => a -> [a] -> Maybe Natural 
elemIndexNat _ [] = Nothing
elemIndexNat a (x : xs) = if a == x
    then Just 0
    else fmap (+1) (elemIndexNat a xs)

data Expr
    = Lambda String Expr
    | App Expr Expr
    | IfThenElse Expr Expr Expr
    | Var String
    | Int Int
    deriving Show

data DeBruijExpr
    = DBLambda DeBruijExpr
    | DBApp DeBruijExpr DeBruijExpr
    | DBIfThenElse DeBruijExpr DeBruijExpr DeBruijExpr
    | DBVar Natural
    | DBInt Int
    | DBBuiltIn BuiltInFunction
    deriving Show

data BuiltInFunction
    = BuiltInAdd
    | BuiltInEq
    deriving (Show, Enum, Bounded)

builtInName :: BuiltInFunction -> String
builtInName BuiltInAdd = "add"
builtInName BuiltInEq  = "eq"

builtIns :: [BuiltInFunction]
builtIns = [minBound .. maxBound]

builtInNames :: [String]
builtInNames = map builtInName builtIns

asBuiltInFunction :: String -> Maybe BuiltInFunction
asBuiltInFunction = flip lookup $ zip builtInNames builtIns

-- In case of Left, returns the name of the unbound variable that caused the problem
toDeBruijn :: Expr -> Either String DeBruijExpr
toDeBruijn = go []
  where
    go :: [String] -> Expr -> Either String DeBruijExpr
    go vars (Lambda varName body) = second DBLambda $ go (varName:vars) body
    go vars (App f x) = DBApp <$> go vars f <*> go vars x
    go vars (IfThenElse bool thenBranch elseBranch) =
        DBIfThenElse <$> go vars bool <*> go vars thenBranch <*> go vars elseBranch
    -- The call to `elemIndexNat` comes first because the global name might be shadowed
    go vars (Var varName) = case elemIndexNat varName vars of
        Nothing -> case asBuiltInFunction varName of
            Just builtIn -> Right $ DBBuiltIn builtIn
            Nothing -> Left varName -- Unbound variable
        Just i -> Right $ DBVar i
    go _ (Int i) = Right $ DBInt i

heapRegister :: Operand
heapRegister = Rcx

writeToPtr :: Operand -> Operand -> Instruction
writeToPtr = Mov . Dereference

writeToHeap :: Operand -> Instruction
writeToHeap = writeToPtr heapRegister

advanceHeapPtr :: Int -> Instruction
advanceHeapPtr = Add heapRegister . NumOperand

createLambda :: Asm -> State (Asm, Int, Int) ()
createLambda newLambda = do
    (lambdas, lambdaCount, localVarCount) <- get
    put (newLambda ++ lambdas, lambdaCount + 1, localVarCount)

increaseLambdaCount :: State (Asm, Int, Int) ()
increaseLambdaCount = do
    (lambdas, lambdaCount, localVarCount) <- get
    put (lambdas, lambdaCount + 1, localVarCount)

increaseLocalVarCount :: State (Asm, Int, Int) ()
increaseLocalVarCount = do
    (lambdas, lambdaCount, localVarCount) <- get
    put (lambdas, lambdaCount, localVarCount + 1)

getLambdaCount :: State (Asm, Int, Int) Int
getLambdaCount = do
    (_, lambdaCount, _) <- get
    pure lambdaCount

getLocalVarCount :: State (Asm, Int, Int) Int
getLocalVarCount = do
    (_, _, localVarCount) <- get
    pure localVarCount

getCompilationResults :: State (Asm, Int, Int) Asm -> (Asm, Asm)
getCompilationResults state =
    let (asm, (lambdas, _, _)) = runState state ([], 0, 0)
    in (lambdas, asm)

-- Use of each register:
--   rax ; Holds the return value of a compiled expression
--   rbx ; Miscelaneous use
--   rcx ; Points at the first byte of free memory in the heap
--   rdx ; Points at a closure or works as a counter in `copy_env`
--   r10 ; Holds the argument to `copy_env`
--   r9  ; Holds the current environment pointer
compile :: DeBruijExpr -> Asm
compile = uncurry assembleAsm . getCompilationResults . go
  where
    go :: DeBruijExpr -> State (Asm, Int, Int) Asm
    go (DBLambda body) = do
        increaseLocalVarCount
        compiledBody <- go body

        lambdaCount <- getLambdaCount
        let lambdaName :: String
            lambdaName = "lambda_" ++ show lambdaCount

            newLambda :: Asm
            newLambda = subroutine lambdaName compiledBody

        createLambda newLambda
        code lambdaName <$> getLocalVarCount
      where
        -- Builds a closure on the heap and returns its address through rax
        code :: String -> Int -> Asm
        code lambdaName localVarCount = [ Comment "Building Closure" ]
            ++ map Inst
            [ Mov Rax heapRegister -- Get the address of the closure
            , writeToHeap (Symbol lambdaName) -- Write the code pointer to the closure
            , advanceHeapPtr 16 -- Leave room for the argument to the lambda (it is filled in before a call)

            -- Capture the current environment and its variables
            , Mov R10 (NumOperand localVarCount)
            , Call (Symbol "copy_env")
            ] ++ [ EmptyLine ]

    go (DBApp f x) = code <$> go x <*> go f
      where
        code :: Asm -> Asm -> Asm
        code compiledArg compiledFunction = [ Comment "Compiling function for call {" ]
         ++ compiledFunction
         ++ [ Comment "} Saving closure pointer {" ]
         ++ [ Inst $ Push Rax ] -- Save the closure pointer on the stack
         ++ [ Comment "} Compiling argument for call {" ]
         ++ compiledArg -- Put the argument on rax
         ++ [ Comment "} Performing the call {" ]
         ++ [ Inst $ Pop Rdx -- Get the function pointer from the stack
            , Inst $ Mov (AddressSum Rdx $ NumOperand 8) Rax -- Write the argument to the closure's environment
            -- Save the current environment pointer and
            -- send to the lambda its environment pointer through r9
            , Inst $ Push R9
            , Inst $ Lea R9 (AddressSum Rdx $ NumOperand 8)
            -- Make the actual call
            , Inst $ Call (Dereference Rdx)
            -- Restore the environment pointer
            , Inst $ Pop R9
            , Comment "}"
            , EmptyLine
            ]

    go (DBIfThenElse bool trueBranch falseBranch) = do
        compiledBool        <- go bool
        compiledTrueBranch  <- go trueBranch
        compiledFalseBranch <- go falseBranch

        -- The lambda count serves as a way to generate unique labels
        -- for lambdas and `if-then-else`s
        labelCount <- getLambdaCount
        increaseLambdaCount

        let thenLabel = "then_" ++ show labelCount
            elseLabel = "else_" ++ show labelCount
            doneLabel = "done_" ++ show labelCount

        pure $
            compiledBool
         ++ [ Inst $ Cmp Rax $ NumOperand 0
            , Inst $ Je $ Symbol elseLabel
            ]
         ++ [ Label thenLabel ]
         ++ compiledTrueBranch
         ++ [ Inst $ Jmp $ Symbol doneLabel]

         ++ [ Label elseLabel ]
         ++ compiledFalseBranch

         ++ [ Label doneLabel ]

    go (DBVar index) = pure
        -- Read the variable from the current environment
        -- (The environment pointer is in r9)
        [ Inst $ Mov Rax $ AddressSum R9 (NumOperand $ fromIntegral $ index * 8)
        , EmptyLine
        ]

    go (DBInt i) = pure [ Inst $ Mov Rax (NumOperand i) ]

    go (DBBuiltIn builtIn) = pure [ Inst $ Mov Rax $ Symbol $ builtInName builtIn ++ "_curried_0" ]

subroutine :: String -> Asm -> Asm
subroutine name instructions = Label name : (instructions ++ [Inst Ret])

compileBuiltIn :: BuiltInFunction -> Asm
compileBuiltIn BuiltInAdd =
    [ Inst $ Mov Rax $ Dereference R9
    , Inst $ Mov Rbx $ AddressSum R9 $ NumOperand 8
    , Inst $ Add Rax Rbx
    ]
compileBuiltIn BuiltInEq =
    [ Inst $ Mov Rax $ Dereference R9
    , Inst $ Mov Rbx $ AddressSum R9 $ NumOperand 8
    , Inst $ Cmp Rax Rbx
    -- Zero and one represent false and true, respectively (at least for now)
    , Inst $ Mov Rbx $ NumOperand 1
    , Inst $ CmoveE  Rax Rbx
    , Inst $ Mov Rbx $ NumOperand 0
    , Inst $ CmoveNE Rax Rbx
    ]

builtInArity :: BuiltInFunction -> Natural
builtInArity BuiltInAdd = 2
builtInArity BuiltInEq = 2

createCurryingSubroutine :: BuiltInFunction -> Natural -> Asm
createCurryingSubroutine builtIn n =
    subroutine (curried ++ "_" ++ show n)
    [ Inst $ Mov Rax heapRegister                     -- Save the address to return
    , Inst $ writeToHeap $ Symbol $ curried ++ "_" ++ show (n + 1)       -- Write the code pointer
    , Inst $ advanceHeapPtr 16
    , Inst $ Mov R10 $ NumOperand $ fromIntegral n -- TODO: Perhaps n-1?
    , Inst $ Call $ Symbol "copy_env"                         -- Make room for both arguments
    ]
  where
    name = builtInName builtIn
    curried = name ++ "_curried"

compileCurriedBuiltIn :: BuiltInFunction -> Asm
compileCurriedBuiltIn builtIn =
    concatMap (createCurryingSubroutine builtIn) [1 .. arity - 1]
 ++ subroutine (name ++ "_curried_" ++ show arity) (compileBuiltIn builtIn)
  where
    name = builtInName builtIn
    arity = builtInArity builtIn

assembleAsm :: Asm -> Asm -> Asm
assembleAsm lambdas start =
    [ TopLevelComment "Header"
    , Global "main"
    , Extern $ pure "printf"
    , EmptyLine
    , Section "text"
    , EmptyLine
    ]
    ++ [ TopLevelComment "Subroutines" ]
    -- Define the `copy_env` subroutine to copy the variables currently
    -- in scope to the environment of a closure being created
    ++ subroutine "copy_env"
       [ Inst $ Xor Rdx Rdx -- Zero rdx (Will be our increasing counter)
       , LocalLabel "loop"
       -- Return if we are done
       , Inst $ Cmp Rdx R10
       , Inst $ Je $ LocalSymbol "done"
       -- Move one 8 byte block
       -- (R9 holds the environment pointer)
       , Inst $ Mov Rbx $ AddressSumMult R9 Rdx (NumOperand 8)
       , Inst $ writeToHeap Rbx
       , Inst $ advanceHeapPtr 8
       -- Increment the counter
       , Inst $ Inc Rdx
       -- Loop again
       , Inst $ Jmp $ LocalSymbol "loop"
       , LocalLabel "done"
       ]
    ++ [ EmptyLine ]

    -- Define the built in functions
    ++ concatMap compileCurriedBuiltIn builtIns

    ++ [ Comment "lambdas" | not (null lambdas) ]
    ++ lambdas
    ++ [ EmptyLine ]

    ++ [ Label "main" ]
    ++ [ Comment "Initialize the heap pointer register"
       , Inst $ Mov heapRegister $ Symbol "heap_base"
       ]
    ++ [ Comment "Create the closures for the built in functions" ]
        -- Since they are always the same, there is no need to create them every time the functions get called,
        -- so let's create them once and point to them when necessary
    ++ concat [ [ Inst $ Mov (Dereference $ Symbol $ name ++ "_curried_0") $ Symbol $ name ++ "_curried_1"] | name <- builtInNames ]
    ++ [ EmptyLine ]
    ++ start
    ++ [ Comment "Print the top of the stack" ]
    ++ map Inst
       [ Mov Rdi $ Symbol "digit_formatter"
       , Mov Rsi Rax
       , Xor Rax Rax
       , Call (Symbol "printf")
       , Ret -- Exit by returning
       ]
    ++ [ EmptyLine ]
    ++ [ TopLevelComment "Put the string for printf in the data segment" ]
    ++ [ Section "data"
       , Label "digit_formatter"
       , Inst $ Db $ StringOperand "%llu" :| [NumOperand 10]

       , Section "bss"
       , TopLevelComment "Closures for built in functions"
       ]

    ++ concat [ [Label (name ++ "_curried_0"), Inst $ Resb 16] | name <- builtInNames ]

       -- Allocate memory for the heap in the .bss segment
    ++ [ Label "heap_base"
       , Inst $ Resb $ 100 * 8 -- TODO: More memory (And garbage collection)
       ]

