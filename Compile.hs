module Compile (compile) where

import Control.Monad.State (State, MonadState (get, put), runState)

import Numeric.Natural (Natural)
import Data.List (genericLength)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Foldable (traverse_)
import Control.Monad (forM)

import Asm
import TypeCheck ( Type(..), DataDecl(..), DeBruijExpr(..), BuiltInFunction(..)
                 , builtInName, builtIns, builtInArity)

neSnoc :: [a] -> a -> NonEmpty a
neSnoc [] x = x :| []
neSnoc (a : as) x = a :| as ++ [x]

-- The compilation context holds the lambdas that have already been generated,
-- as well as how many of them there are
type CompCtxt = State (Asm, Natural)

createLambda :: Asm -> CompCtxt ()
createLambda newLambda = do
    (lambdas, lambdaCount) <- get
    put (newLambda ++ lambdas, lambdaCount + 1)

-- TODO: Define a function "freshLambdaId" in terms of increaseLambdaCount and getLambdaCount
-- and use that instead of always calling increaseLambdaCount after getLambdaCount
increaseLambdaCount :: CompCtxt ()
increaseLambdaCount = do
    (lambdas, lambdaCount) <- get
    put (lambdas, lambdaCount + 1)

getLambdaCount :: CompCtxt Natural
getLambdaCount = do
    (_, lambdaCount) <- get
    pure lambdaCount

getCompilationResults :: CompCtxt a -> (Asm, a)
getCompilationResults state =
    let (a, (lambdas, _)) = runState state ([], 0)
    in (lambdas, a)

-- Convenient functions for generating assembly
heapRegister :: Operand
heapRegister = Rcx

writeToPtr :: Operand -> Operand -> Instruction
writeToPtr = Mov . Dereference

writeToHeap :: Operand -> Instruction
writeToHeap = writeToPtr heapRegister

advanceHeapPtr :: Int -> Instruction
advanceHeapPtr = Add heapRegister . NumOperand

compileFinalConstructorApp :: Natural -> Natural -> Asm
compileFinalConstructorApp tag arity = map Inst
    [ Mov Rax heapRegister
    , writeToHeap $ NumOperand $ fromIntegral tag
    , advanceHeapPtr 8
    -- TODO: Create a function to reduce code duplication in every call to "copy_env"
    , Mov R10 $ NumOperand $ fromIntegral arity
    , Call $ Symbol "copy_env"
    ]

-- Use of each register:
--   rax ; Holds the return value of a compiled expression
--   rbx ; Miscelaneous use
--   rcx ; Points at the first byte of free memory in the heap
--   rdx ; Points at a closure or works as a counter in `copy_env`
--   r10 ; Holds the argument to `copy_env`
--   r9  ; Holds the current environment pointer
--   r8  ; Holds the the pointer to the next io action to execute in the io loop
compileMain :: DeBruijExpr -> CompCtxt Asm
compileMain = go 0
  where
    -- v represents the number of local variables currently in scope
    go :: Natural -> DeBruijExpr -> CompCtxt Asm
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

    go v (DBApp f x) = compileApp <$> go v x <*> go v f
      where
        compileApp :: Asm -> Asm -> Asm
        compileApp compiledArg compiledFunction = [ Comment "Compiling function for call {" ]
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
    go v (DBLet _ _ definition body) = do
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

    go vars (DBCase scrutinee cases) = do
        -- Get a fresh id for the labels for this "case"
        caseId <- getLambdaCount
        increaseLambdaCount
        compiledCases <- concat <$> traverse (compileCase caseId) cases

        let tags = map (\(tag, _, _) -> tag) cases
        compiledScrutinee <- go vars scrutinee
        pure $ compiledScrutinee
         -- Check the constructor tag the scrutinee holds and jump to the corresponding case
         ++ [ Inst $ Mov Rbx $ Dereference Rax ] -- Load the constructor tag
         ++ concatMap (checkForTag caseId) tags
         ++ compiledCases
         ++ [ Label $ "case_" ++ show caseId ++ "_done" ]
      where
        checkForTag :: Natural -> Natural -> Asm
        checkForTag caseId tag = map Inst
            [ Cmp Rbx $ NumOperand $ fromIntegral tag
            , Je $ Symbol $ "case_" ++ show caseId ++ "_branch_" ++ show tag
            ]

        compileCase :: Natural -> (Natural, [Type], DeBruijExpr) -> CompCtxt Asm
        compileCase caseId (tag, types, body) = do
            let arity = genericLength types
            compiledBody <- go (arity + vars) body
            pure $ [ Label $ "case_" ++ show caseId ++ "_branch_" ++ show tag ]
              -- Crete the environment with the variables that have been bound
              -- by pattern matching
              ++ [ Inst $ Push heapRegister -- Save what will become the env-pointer
                 , Inst $ Push R9 -- Preserve our own env-ptr
                 , Inst $ Lea R9 $ AddressSum Rax $ NumOperand 8 -- Get R9 to point to the bound variables

                 , Inst $ Mov R10 $ NumOperand $ fromIntegral arity -- Copy the bound vars to the env we are creating
                 , Inst $ Call $ Symbol "copy_env"
                 , Inst $ Pop R9 -- Restore our env-ptr
                 , Inst $ Mov R10 $ NumOperand $ fromIntegral vars -- Copy its variables to the env we are creating
                 , Inst $ Call $ Symbol "copy_env"
                 , Inst $ Pop Rbx -- Get the new env-ptr back from the stack
                 , Inst $ Push R9 -- Preserve once more our env-ptr
                 , Inst $ Mov R9 Rbx -- Set R9 to point to the created environment
                 , EmptyLine
                 ]
                 -- Then evaluate the body
              ++ compiledBody
              ++ [ Inst $ Pop R9 ] -- Restore our env-ptr
              -- Jump to the end of the case expression to ensure that only one branch executes
              ++ [ Inst $ Jmp $ Symbol $ "case_" ++ show caseId ++ "_done" ]

    go _ (DBVar index) = pure
        -- Read the variable from the current environment
        -- (The environment pointer is in r9)
        [ Inst $ Mov Rax $ AddressSum R9 (NumOperand $ fromIntegral $ index * 8)
        , EmptyLine
        ]

    -- Since types are erased, type applications are simply ignored for compilation purposes
    go v (DBTypeApp e _) = go v e

    go _ (DBInt i) = pure [ Inst $ Mov Rax (NumOperand i) ]

    go _ (DBBuiltIn builtIn)  = pure [ Inst $ Mov Rax $ Dereference $ Symbol $ builtInName builtIn ]
    go _ (DBConstructor name) = pure [ Inst $ Mov Rax $ Dereference $ Symbol name ]
    go _ DBTrue = pure [ Inst $ Mov Rax $ NumOperand 1 ]
    go _ DBFalse = pure [ Inst $ Mov Rax $ NumOperand 0 ]
    go v (DBAnn expr _) = go v expr

subroutine :: String -> Asm -> Asm
subroutine name instructions = Label name : (instructions ++ [Inst Ret])

compileFinalBuiltInApp :: BuiltInFunction -> Asm
compileFinalBuiltInApp BuiltInAdd =
    [ Inst $ Mov Rax $ Dereference R9
    , Inst $ Mov Rbx $ AddressSum R9 $ NumOperand 8
    , Inst $ Add Rax Rbx
    ]
compileFinalBuiltInApp BuiltInEq =
    [ Inst $ Mov Rax $ Dereference R9
    , Inst $ Mov Rbx $ AddressSum R9 $ NumOperand 8
    , Inst $ Cmp Rax Rbx
    -- Zero and one represent false and true, respectively (at least for now)
    , Inst $ Mov Rbx $ NumOperand 1
    , Inst $ CmoveE  Rax Rbx
    , Inst $ Mov Rbx $ NumOperand 0
    , Inst $ CmoveNE Rax Rbx
    ]

-- Create and return an IO struct with a pointer to the print_int subroutine
compileFinalBuiltInApp PrintInt = map Inst
    -- Save the pointer to the object we are creating
    [ Mov Rax heapRegister
    -- Print has no continuation, so we write a nullptr here
    , writeToHeap $ NumOperand 0
    , advanceHeapPtr 8
    -- Write the pointer to the current action
    , writeToHeap $ Symbol "print_int"
    , advanceHeapPtr 8
    -- And include the integer to be printed
    , Mov Rbx $ Dereference R9
    , writeToHeap Rbx
    , advanceHeapPtr 8
    -- (Rax already contains the pointer we are returning,
    -- so the work is over)
    ]

-- TODO: Given an IO struct pointed to by the value in Rax, we should
-- create a new one that does the original action, but has a new,
-- extended continuation
compileFinalBuiltInApp Bind = []

-- TODO: Implement pure
compileFinalBuiltInApp Pure = []

curryingStep :: String -> Natural -> Asm
curryingStep name n =
    [ Inst $ Mov Rax heapRegister -- Save the address to return
    , Inst $ writeToHeap $ Symbol $ name ++ "_curried_" ++ show (n + 1) -- Write the code pointer
    , Inst $ advanceHeapPtr 16
    , Inst $ Mov R10 $ NumOperand $ fromIntegral n -- TODO: Perhaps n-1?
    , Inst $ Call $ Symbol "copy_env" -- Make room for the arguments
    ]

asCurryingSubroutine :: String -> Natural -> Asm -> Asm
asCurryingSubroutine name n = subroutine (name ++ "_curried_" ++ show n)

computeGlobalValue :: String -> Asm -> Asm
computeGlobalValue symbol body = body ++ map Inst
    [ Mov (Dereference $ Symbol symbol) Rax ]

compile :: [DataDecl] -> DeBruijExpr -> Asm
compile dataDecls main =
    let (generatedLambdas, (asm, globalMap)) = getCompilationResults $ do
        let indexedConstructors = concatMap (zip [0 :: Natural .. ] . constructors) dataDecls
            resolvedConstructors = map (\(tag, (name, types)) -> (name, tag, genericLength types)) indexedConstructors

        -- The code for compiling constructors and built-in functions looks nearly identical.
        -- TODO: Unify the handling of constructors and built-in functions

        -- Compile constructors
        constructorMainDefs <- forM resolvedConstructors $ \(name, tag, arity) -> do
            let curryingSteps
                  | arity == 0 = []
                  | otherwise = map (curryingStep name) [0 .. arity - 1]
                (def :| subroutines) =  curryingSteps `neSnoc` compileFinalConstructorApp tag arity

            traverse_ (createLambda . uncurry (asCurryingSubroutine name)) (zip [1..] subroutines)
            pure (name, def)

        -- Compile built-in functions
        builtInMainDefs <- forM builtIns $ \builtIn -> do
            let arity = builtInArity builtIn
                name = builtInName builtIn
                curryingSteps = map (curryingStep name) [0 .. arity - 1]
                (def :| subroutines) =  curryingSteps `neSnoc` compileFinalBuiltInApp builtIn

            traverse_ (createLambda . uncurry (asCurryingSubroutine name)) (zip [1..] subroutines)
            pure (name, def)

        -- Compile main
        compiledMain <- compileMain main

        pure (compiledMain, builtInMainDefs ++ constructorMainDefs)
    in assembleAsm globalMap generatedLambdas asm

assembleAsm :: [(String, Asm)] -> Asm -> Asm -> Asm
assembleAsm globalValues lambdas start =
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
    ++ subroutine "print_int" -- Assumes R9 is pointing to the Int that is to be printed
       (map Inst
       [ Mov Rdi $ Symbol "digit_formatter"
       , Mov Rsi $ Dereference R9
       , Sub Rsp $ NumOperand 8
       , Xor Rax Rax
       , Call (Symbol "printf")
        -- We don't have to worry about returning a value, because possible continuations
        -- to IO () have to take unit as input, which, in practice, means the input value
        -- will be ignored
       , Add Rsp $ NumOperand 8
       ])
    ++ [ EmptyLine ]

    ++ [ Comment "lambdas" | not (null lambdas) ]
    ++ lambdas
    ++ [ EmptyLine ]

    ++ [ Label "main" ]
    ++ [ Comment "Initialize the heap pointer register"
       , Inst $ Mov heapRegister $ Symbol "heap_base"
       ]

    -- Write the global values (built-ins and constructors) to their respective locations,
    -- making them available for the program
    ++ [ Comment "Define global values" ]
    ++ concatMap (uncurry computeGlobalValue) globalValues
    ++ [ EmptyLine ]

    -- TODO: Think carefully about register preservation, like the one below.
    -- Preserve Rbx, which is callee-saved in the C convention
    -- (This also aligns the stack for printf calls)
    ++ [ Inst $ Push Rbx ]

    -- Runs the actual program
    ++ start
    ++ ioLoop

    -- Recover Rbx
    ++ [ Inst $ Pop Rbx ]
    ++ [ EmptyLine ]

    -- Exit the program by returning
    ++ [ Inst Ret ]

    ++ [ TopLevelComment "Put the string for printf in the data segment" ]
    ++ [ Section "data"
       , Label "digit_formatter"
       , Inst $ Db $ StringOperand "%llu" :| [NumOperand 10]

       , Section "bss"
       , TopLevelComment "Closures for built in functions"
       ]

    -- Allocate space for the closures of constructors and built-in functions
    ++ concat [ [Label name, Inst $ Resb 8] | name <- globalNames ]

       -- Allocate memory for the heap in the .bss segment
    ++ [ Label "heap_base"
       , Inst $ Resb $ 1000000 * 8 -- TODO: More memory (And garbage collection)
       ]
  where
    -- Names of the functions the compiler "magically" brings into existence:
    -- Constructors, that are defined by data declarations, and built-in functions
    globalNames = map fst globalValues

ioLoop :: Asm
ioLoop =
    -- Continually processes IO actions untill there is no continuation,
    -- and then program halts.
    -- Assumes the result of evaluating the main IO action is in Rax
    [ Label "io_loop"
    -- Save the pointer to the IO action struct
    -- (Note that R12 is caller-saved in the C convention, so the
    -- action we execute may call C functions and R12 is still
    -- preserved)
    , Inst $ Mov R12 Rax
    -- Pass the environment pointer to the action through R9
    , Inst $ Lea R9 $ AddressSum Rax $ NumOperand 16
    -- Call the impure action (which leaves its result in Rax)
    , Inst $ Call $ AddressSum Rax $ NumOperand 8
    -- Now we have to call the continuation, passing the result:
    -- First we get the thunk-pointer
    , Inst $ Mov R12 $ Dereference R12
    -- If it is zero, that means that there is no continuation and we are done
    , Inst $ Cmp R12 $ NumOperand 0
    , Inst $ Je $ Symbol "done"
    -- Otherwise, we write the argument to the thunk's environment
    -- (TODO: Maybe it's necessary to preserve whatever was already there? Idk)
    , Inst $ Mov (AddressSum R12 $ NumOperand 8) Rax
    -- And finally, we get the code-pointer and call it
    , Inst $ Call $ Dereference R12
    -- Now it's the new IO action that is stored in Rax, and we may loop
    , Inst $ Jmp $ Symbol "io_loop"
    , Label "done"
    ]
