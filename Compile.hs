module Compile (Expr(..), toDeBruijn, compile, asmToString) where

import Numeric.Natural (Natural)
import Data.Bifunctor (second)
import Data.List.NonEmpty (NonEmpty ((:|)))

import Asm

elemIndexNat :: Eq a => a -> [a] -> Maybe Natural 
elemIndexNat _ [] = Nothing
elemIndexNat a (x : xs) = if a == x then Just 0 else fmap (+1) (elemIndexNat a xs)

dropThird :: (a, b, c) -> (a, b)
dropThird (a, b, _) = (a, b)

data Expr
    = Lambda String Expr
    | App Expr Expr
    | Var String
    | Int Int
    deriving Show

data DeBruijExpr
    = DBLambda DeBruijExpr
    | DBApp DeBruijExpr DeBruijExpr
    | DBVar Natural
    | DBInt Int
    deriving Show

-- In case of Left, returns the name of the unbound variable that caused the problem
toDeBruijn :: Expr -> Either String DeBruijExpr
toDeBruijn = go []
  where
    go :: [String] -> Expr -> Either String DeBruijExpr
    go vars (Lambda varName body) = second DBLambda $ go (varName:vars) body
    go vars (App f x) = DBApp <$> go vars f <*> go vars x
    go vars (Var varName) = maybe (Left varName) (Right . DBVar) (elemIndexNat varName vars)
    go _ (Int i) = Right $ DBInt i

heapRegister :: Operand
heapRegister = Rcx

writeToPtr :: Operand -> Operand -> Instruction
writeToPtr = Mov . Dereference

writeToHeap :: Operand -> Instruction
writeToHeap = writeToPtr heapRegister

advanceHeapPtr :: Int -> Instruction
advanceHeapPtr = Add heapRegister . NumOperand

-- Use of each register:
--   rax ; Holds the return value of a compiled expression
--   rbx ; Miscelaneous use
--   rcx ; Points at the first byte of free memory in the heap
--   rdx ; Points at a closure or works as a counter in `copy_env`
--   r10 ; Holds the argument to `copy_env`
--   r9  ; Holds the current environment pointer
compile :: DeBruijExpr -> Asm
compile = uncurry assembleAsm . dropThird . go 0 0
  where
    go :: Int -> Int -> DeBruijExpr -> (Asm, Asm, Int)
    go lambdaCount localVarCount (DBLambda body) =
        (newLambda ++ lambdas, code, newLambdaCount + 1)
      where
        (lambdas, compiledBody, newLambdaCount) = go lambdaCount (localVarCount + 1) body

        lambdaName :: String
        lambdaName = "lambda_" ++ show newLambdaCount

        newLambda :: Asm
        newLambda = 
            [ Label lambdaName ]
         ++ compiledBody
         ++ [ Inst Ret ]

        -- Builds a closure on the heap and returns its address through rax
        code :: Asm
        code = map Inst
            [ Mov Rax heapRegister -- Get the address of the closure
            , writeToHeap (Symbol lambdaName) -- Write the code pointer to the closure
            , advanceHeapPtr 16 -- Leave room for the argument to the lambda (it is filled in before a call)

            -- Capture the current environment and its variables
            , Mov R10 (NumOperand localVarCount)
            , Call (Symbol "copy_env")
            ]

    go lambdaCount localVarCount (DBApp f x) =
        (lambdas ++ lambdas', code, lambdaCount'')
      where
        (lambdas , compiledArg     , lambdaCount' ) = go lambdaCount  localVarCount x
        (lambdas', compiledFunction, lambdaCount'') = go lambdaCount' localVarCount f

        code :: Asm
        code =
            compiledFunction
         ++ [ Inst $ Push Rax ] -- Save the function pointer on the stack
         ++ compiledArg -- Put the argument on rax
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
            ]

    go lambdaCount _ (DBVar index) = ([],
        -- Read the variable from the current environment
        -- (The environment pointer is in r9)
        [ Inst $ Mov Rax $ AddressSum R9 (NumOperand $ fromIntegral $ index * 8)
        ], lambdaCount)

    go lambdaCount _ (DBInt i) = ([], [ Inst $ Mov Rax (NumOperand i) ], lambdaCount)

assembleAsm :: Asm -> Asm -> Asm
assembleAsm lambdas start =
    [ Global "main"
    , Extern $ pure "printf"
    , EmptyLine
    , Section "text"
    , EmptyLine
    ]
    -- Define the `copy_env` subroutine to copy the variables currently
    -- in scope to the environment of a closure being created
    ++ [ Label "copy_env"
       , Inst $ Xor Rdx Rdx -- Zero rdx (Will be our increasing counter)
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
       , Inst Ret
       , EmptyLine
       ]
    ++ lambdas
    ++ [ EmptyLine ]
    ++ [ Label "main" ]
    -- Initialize the heap pointer register
    ++ [ Inst $ Mov heapRegister $ Symbol "heap_base" ]
    ++ start
    ++ [ EmptyLine ]
    -- Print the top of the stack
    ++ map Inst
       [ Mov Rdi $ Symbol "digit_formatter"
       , Mov Rsi Rax
       , Xor Rax Rax
       , Call (Symbol "printf")
       , Ret -- Exit by returning
       ]
    -- Put the string for printf in the data segment
    ++ [ EmptyLine
       , Section "data"
       , Label "digit_formatter"
       , Inst $ Db $ StringOperand "%llu" :| [NumOperand 10]
       -- Allocate memory for the heap in the .bss segment
       , Section "bss"
       , Label "heap_base"
       , Inst $ Resb $ 100 * 8 -- TODO: More memory (And garbage collection)
       ]

