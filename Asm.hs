module Asm (Asm, AsmLine(..), Instruction(..), Operand(..), asmToString) where

import Numeric.Natural (Natural)
import Data.List.NonEmpty (NonEmpty(..))

data AsmLine
    = Label String
    | LocalLabel String
    | Inst Instruction
    | Global String
    | Section String
    | Extern (NonEmpty String)
    | EmptyLine
    | TopLevelComment String
    | Comment String

data Instruction
    = Pop  Operand
    | Push Operand
    | Inc  Operand
    | Mov  Operand Operand
    | Add  Operand Operand
    | Sub  Operand Operand
    | Cmp  Operand Operand
    | Xor  Operand Operand
    | Lea  Operand Operand
    | Call Operand
    | Jmp  Operand
    | Je   Operand
    | Resb Natural
    | Db  (NonEmpty Operand)
    | Ret

data Operand
    = Symbol String
    | LocalSymbol String
    | Rax | Rbx | Rcx | Rdx | Rsp | Rdi | Rsi | R9 | R10
    | AddressSum Operand Operand
    | AddressSumMult Operand Operand Operand
    | Dereference Operand
    | StringOperand String
    | NumOperand Int
 
type Asm = [AsmLine]

foldlNonEmpty :: (a -> a -> a) -> NonEmpty a -> a
foldlNonEmpty f (x :| xs) = foldl f x xs

commaSeparated :: NonEmpty String -> String
commaSeparated = foldlNonEmpty (<&>)

(<+>) :: String -> String -> String
xs <+> ys = xs ++ " " ++ ys

(<&>) :: String -> String -> String
xs <&> ys = xs ++ ", " ++ ys

instructionToString :: Instruction -> String
instructionToString (Pop r) = "pop" <+> operandToString r
instructionToString (Push r) = "push" <+> operandToString r
instructionToString (Inc r) = "inc" <+> operandToString r
instructionToString (Mov a b) =
    "mov" <+> operandToString a <&> operandToString b
instructionToString (Add a b) =
    "add" <+> operandToString a <&> operandToString b
instructionToString (Sub a b) =
    "sub" <+> operandToString a <&> operandToString b
instructionToString (Lea a b) =
    "lea" <+> operandToString a <&> operandToString b
instructionToString (Cmp a b) =
    "cmp" <+> operandToString a <&> operandToString b
instructionToString Ret = "ret"
instructionToString (Call r) = "call" <+> operandToString r
instructionToString (Jmp r) = "jmp" <+> operandToString r
instructionToString (Je r) = "je" <+> operandToString r
instructionToString (Xor a b) = "xor" <+> operandToString a <&> operandToString b
instructionToString (Db operands) = "db" <+> commaSeparated (fmap operandToString operands)
instructionToString (Resb size) = "resb" <+> show size

operandToString :: Operand -> String
operandToString (Symbol s) = s
operandToString (LocalSymbol s) = "." ++ s
operandToString (NumOperand x) = show x
-- TODO: Make sure this `StringOperand` case doesn't break in case of strings with special characters
operandToString (StringOperand s) = show s
operandToString (AddressSum a b) =
    "[" ++ operandToString a <+> "+" <+> operandToString b ++ "]"
operandToString (AddressSumMult a b c) =
    "[" ++ operandToString a <+> "+" <+> operandToString b <+> "*" <+> operandToString c ++ "]"
operandToString (Dereference x) =
    "qword [" ++ operandToString x ++ "]"
operandToString Rax = "rax"
operandToString Rbx = "rbx"
operandToString Rcx = "rcx"
operandToString Rdx = "rdx"
operandToString Rsp = "rsp"
operandToString Rsi = "rsi"
operandToString Rdi = "rdi"
operandToString R9 = "r9"
operandToString R10 = "r10"

asmToString :: Asm -> String
asmToString = concatMap $ (++ "\n") . asmLineToString

asmLineToString :: AsmLine -> String
asmLineToString (Label labelName) = labelName ++ ":"
asmLineToString (LocalLabel labelName) = "." ++ labelName ++ ":"
asmLineToString (Inst instruction) = indent $ instructionToString instruction
  where indent = ("    " ++)
asmLineToString (Global s) = "global" <+> s
asmLineToString (Section s) = "section" <+> "." ++ s
asmLineToString (Extern functions) = "extern" <+> commaSeparated functions
asmLineToString EmptyLine = ""
-- Top level comments don't need indentaion, while regular comments do
asmLineToString (Comment str) = "    ;" <+> str
asmLineToString (TopLevelComment str) = ";" <+> str

