module Compile (Expr(..), Type(..), toDeBruijn, compile, asmToString, checkMain) where

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

atIndex :: Natural -> [a] -> Maybe a
atIndex _ [] = Nothing
atIndex 0 (x : _) = Just x
atIndex n (_ : xs) = atIndex (n - 1) xs

data Type
    = ArrowType Type Type
    | BoolType
    | IntType
    deriving (Eq, Show)

prettyType :: Type -> String
prettyType BoolType = "Bool"
prettyType IntType = "Int"
prettyType (ArrowType a b) = prettyType a ++ " -> " ++ prettyType b

data Expr
    = Lambda String Expr
    | App Expr Expr
    | IfThenElse Expr Expr Expr
    | TrueExpr
    | FalseExpr
    | Ann Expr Type
    -- Let optionally holds a type annotation
    -- (Though without one, it can't be recursive and still typecheck) 
    | Let (Maybe Type) String Expr Expr -- Let is allowed to be recursive
    | Var String
    | Int Int
    deriving Show

data DeBruijExpr
    = DBLambda DeBruijExpr
    | DBApp DeBruijExpr DeBruijExpr
    | DBLet (Maybe Type) DeBruijExpr DeBruijExpr
    | DBIfThenElse DeBruijExpr DeBruijExpr DeBruijExpr
    | DBTrue
    | DBFalse
    | DBAnn DeBruijExpr Type
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
    go vars (Let ty varName definition body) =
        -- Since "let" can be recursive, both the definition and the body
        -- have access to variable it binds
        DBLet ty <$> go (varName : vars) definition <*> go (varName : vars) body
    go vars (Var varName) = case elemIndexNat varName vars of
        Nothing -> case asBuiltInFunction varName of
            Just builtIn -> Right $ DBBuiltIn builtIn
            Nothing -> Left varName -- Unbound variable
        Just i -> Right $ DBVar i
    go _ (Int i) = Right $ DBInt i
    go _ TrueExpr = Right DBTrue
    go _ FalseExpr = Right DBFalse
    go vars (Ann expr ty) = DBAnn <$> go vars expr <*> pure ty

heapRegister :: Operand
heapRegister = Rcx

writeToPtr :: Operand -> Operand -> Instruction
writeToPtr = Mov . Dereference

writeToHeap :: Operand -> Instruction
writeToHeap = writeToPtr heapRegister

advanceHeapPtr :: Int -> Instruction
advanceHeapPtr = Add heapRegister . NumOperand

createLambda :: Asm -> State (Asm, Int) ()
createLambda newLambda = do
    (lambdas, lambdaCount) <- get
    put (newLambda ++ lambdas, lambdaCount + 1)

increaseLambdaCount :: State (Asm, Int) ()
increaseLambdaCount = do
    (lambdas, lambdaCount) <- get
    put (lambdas, lambdaCount + 1)

getLambdaCount :: State (Asm, Int) Int
getLambdaCount = do
    (_, lambdaCount) <- get
    pure lambdaCount

getCompilationResults :: State (Asm, Int) Asm -> (Asm, Asm)
getCompilationResults state =
    let (asm, (lambdas, _)) = runState state ([], 0)
    in (lambdas, asm)

-- Use of each register:
--   rax ; Holds the return value of a compiled expression
--   rbx ; Miscelaneous use
--   rcx ; Points at the first byte of free memory in the heap
--   rdx ; Points at a closure or works as a counter in `copy_env`
--   r10 ; Holds the argument to `copy_env`
--   r9  ; Holds the current environment pointer
compile :: DeBruijExpr -> Asm
compile = uncurry assembleAsm . getCompilationResults . go 0
  where
    -- v represents the number of local variables currently in scope
    go :: Natural -> DeBruijExpr -> State (Asm, Int) Asm
    go v (DBLambda body) = do
        compiledBody <- go (v + 1) body

        lambdaCount <- getLambdaCount
        let lambdaName :: String
            lambdaName = "lambda_" ++ show lambdaCount

            newLambda :: Asm
            newLambda = subroutine lambdaName compiledBody

        createLambda newLambda
        pure $ code lambdaName v
      where
        -- Builds a closure on the heap and returns its address through rax
        code :: String -> Natural -> Asm
        code lambdaName localVarCount = [ Comment "Building Closure" ]
            ++ map Inst
            [ Mov Rax heapRegister -- Get the address of the closure
            , writeToHeap (Symbol lambdaName) -- Write the code pointer to the closure
            , advanceHeapPtr 16 -- Leave room for the argument to the lambda (it is filled in before a call)

            -- Capture the current environment and its variables
            , Mov R10 $ NumOperand $ fromIntegral localVarCount
            , Call (Symbol "copy_env")
            ] ++ [ EmptyLine ]

    go v (DBApp f x) = code <$> go v x <*> go v f
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
            -- Preserve what was previously the lambda's argument:
            -- (Necessary for recursive calls to work)
            , Inst $ Mov Rbx (AddressSum Rdx $ NumOperand 8)
            , Inst $ Push Rbx

            , Inst $ Mov (AddressSum Rdx $ NumOperand 8) Rax -- Write the argument to the closure's environment
            -- Save the current environment pointer and
            -- send to the lambda its environment pointer through r9
            , Inst $ Push R9
            , Inst $ Lea R9 (AddressSum Rdx $ NumOperand 8)
            -- Save the function pointer
            , Inst $ Push Rdx
            -- Make the actual call
            , Inst $ Call (Dereference Rdx)
            -- Restore the function pointer
            , Inst $ Pop Rdx
            -- Restore the environment pointer
            , Inst $ Pop R9
            -- Restore the previous lambda argument
            , Inst $ Pop Rbx
            , Inst $ Mov (AddressSum Rdx $ NumOperand 8) Rbx
            , Comment "}"
            , EmptyLine
            ]

    go v (DBIfThenElse bool trueBranch falseBranch) = do
        compiledBool        <- go v bool
        compiledTrueBranch  <- go v trueBranch
        compiledFalseBranch <- go v falseBranch

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
    go v (DBLet _ definition body) = do
        -- Both the definition and the body have access to one more variable
        -- (namely, the let-bound one)
        compiledDefinition <- go (v + 1) definition
        compiledBody       <- go (v + 1) body
        pure $
            -- Create an environment with the let bound variable
            [ Comment "LET"
            , Inst $ Push R9 -- Save our environment pointer
            , Inst $ Mov Rbx heapRegister -- Save the address of the future environment pointer
            , Inst $ Push Rbx
            , Inst $ advanceHeapPtr 8 -- Leave room for the variable
            , Inst $ Mov R10 $ NumOperand $ fromIntegral v -- Copy the current environment
            , Inst $ Call $ Symbol "copy_env"
            , Inst $ Pop R9 -- Pass the environment pointer through R9
            , Inst $ Mov (Dereference R9) heapRegister -- Give the definition a way to refer to itself
            ]
         ++ compiledDefinition -- Evaluate the definition
         -- Write the result of evaluating the definition to the environment
         ++ [ Inst $ Mov (Dereference R9) Rax ]
         -- Evaluate the body (still in the environment)
         ++ compiledBody
         -- Restore R9
         ++ [ Inst $ Pop R9 ]

    go _ (DBVar index) = pure
        -- Read the variable from the current environment
        -- (The environment pointer is in r9)
        [ Inst $ Mov Rax $ AddressSum R9 (NumOperand $ fromIntegral $ index * 8)
        , EmptyLine
        ]

    go _ (DBInt i) = pure [ Inst $ Mov Rax (NumOperand i) ]

    go _ (DBBuiltIn builtIn) = pure [ Inst $ Mov Rax $ Symbol $ builtInName builtIn ++ "_curried_0" ]
    go _ DBTrue = pure [ Inst $ Mov Rax $ NumOperand 1 ]
    go _ DBFalse = pure [ Inst $ Mov Rax $ NumOperand 0 ]
    go v (DBAnn expr _) = go v expr

type Ctxt = [Maybe Type]

extend :: Ctxt -> Type -> Ctxt
extend = flip $ (:) . Just

extendWithUnknownType :: Ctxt -> Ctxt
extendWithUnknownType = (Nothing :)

infer :: Ctxt -> DeBruijExpr -> Either String Type
infer gamma (DBApp f x) = do
    functionTy <- infer gamma f
    (lhs, rhs) <- case functionTy of
        (ArrowType lhs rhs) -> pure (lhs, rhs)
        _ -> Left $ "Expected function type for " ++ show f
    check gamma x lhs
    pure rhs
infer gamma (DBIfThenElse condition ifTrue ifFalse) = do
    check gamma condition BoolType
    returnTy <- infer gamma ifTrue
    check gamma ifFalse returnTy
    pure returnTy
infer gamma (DBAnn expr ty) = do
    check gamma expr ty
    pure ty
infer gamma (DBVar index) = case atIndex index gamma of
    (Just (Just ty)) -> pure ty
    (Just Nothing) -> Left "Recursive code without a type annotation"
    Nothing -> Left "Type checking error: Out of context DeBruijnIndex" 
infer _ DBTrue = pure BoolType
infer _ DBFalse = pure BoolType
infer _ (DBInt _) = pure IntType
infer _ (DBBuiltIn builtIn) = pure $ builtInType builtIn
infer _ expr = Left $ "Failed to infer type for " ++ show expr

builtInType :: BuiltInFunction -> Type
builtInType BuiltInAdd = IntType `ArrowType` (IntType `ArrowType` IntType)
builtInType BuiltInEq  = IntType `ArrowType` (IntType `ArrowType` BoolType)

check :: Ctxt -> DeBruijExpr -> Type -> Either String ()
check gamma (DBLambda body) ty
    | (ArrowType lhs rhs) <- ty = check (extend gamma lhs) body rhs
    | otherwise = Left $ "Lambda can't have type " ++ prettyType ty
check gamma (DBLet Nothing def body) ty = do -- If the let doesn't have an annotation
    -- Infer a type for the definition hoping it won't make a recursive call
    -- (If it does we are screwed and typechecking fails)
    defTy <- infer (extendWithUnknownType gamma) def 
    -- Then check the result (the part after "in")
    check (extend gamma defTy) body ty
check gamma (DBLet (Just ann) def body) ty = do -- If we do have an annotation thing are easier:
    check (extend gamma ann) def ann -- Check the definition agains the annotated type
    check (extend gamma ann) body ty -- Check the body agains the type for the let

check gamma expr ty = do
    inferredTy <- infer gamma expr
    if inferredTy == ty
      then Right ()
      else Left $ "Inferred type "
            ++ prettyType inferredTy
            ++ " does not match checking type "
            ++ prettyType ty

checkMain :: DeBruijExpr -> Either String ()
checkMain = flip (check []) IntType

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

