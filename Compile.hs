-- TODO: Use Haskell 2021
{-# LANGUAGE TupleSections #-}

module Compile (Expr(..), Type(..), DataDecl(..), Declaration(..), toDeBruijn,
                compile, asmToString, checkMain, generalize, declsToProgram) where

import Numeric.Natural (Natural)
import Control.Monad.State (State, MonadState (get, put), runState)
import Control.Monad (forM, forM_)
import Control.Arrow ((&&&))
import Data.Foldable (traverse_)
import Data.List (union, delete, genericLength)
import Data.Either (partitionEithers)
import Data.Bifunctor (second, Bifunctor (first))
import Data.List.NonEmpty (NonEmpty ((:|)))

import Asm
import Data.Tuple (swap)

--- Utils ---
elemIndexNat :: Eq a => a -> [a] -> Maybe Natural
elemIndexNat _ [] = Nothing
elemIndexNat a (x : xs) = if a == x
    then Just 0
    else fmap (+1) (elemIndexNat a xs)

atIndex :: Natural -> [a] -> Maybe a
atIndex _ [] = Nothing
atIndex 0 (x : _) = Just x
atIndex n (_ : xs) = atIndex (n - 1) xs

note :: a -> Maybe b -> Either a b
note a Nothing = Left a
note _ (Just b) = Right b

reassoc :: ((a, b), c) -> (a, (b, c))
reassoc ((a, b), c) = (a, (b, c))

neSnoc :: [a] -> a -> NonEmpty a
neSnoc [] x = x :| []
neSnoc (a : as) x = a :| as ++ [x]

data Kind
    = ArrowKind Kind Kind
    | Type
    deriving (Eq, Show)

data Type
    = ArrowType Type Type
    | AppType Type Type
    | BoolType
    | IntType
    | UserDefinedType String
    | TypeVar String
    | ForAll String Type
    deriving (Eq, Show)

data Declaration = DataDeclDef DataDecl | RegularDef String (Maybe Type) Expr

separateDefs :: [Declaration] -> ([DataDecl], [(String, Maybe Type, Expr)])
separateDefs = partitionEithers . map defAsEither
  where
    defAsEither :: Declaration -> Either DataDecl (String, Maybe Type, Expr)
    defAsEither (DataDeclDef decl) = Left decl
    defAsEither (RegularDef name ty expr) = Right (name, ty, expr)

declsToProgram :: [Declaration] -> Either String ([DataDecl], Expr)
declsToProgram decls = do
    let (dataDecls, exprs) = separateDefs decls
        namedMain (name, _, _) = name == "main"

    (_, mainTy, mainExpr) <- case filter namedMain exprs of
        [] -> Left "No main definition found"
        [def] -> pure def
        _ -> Left "Multiple main definitions found"

    -- Ensure the main expression has the right type
    case mainTy of
        Just ty -> if ty == IntType
            then pure ()
            else Left $ "Expected main to have type Int, but found type " ++ prettyType ty
        Nothing -> pure ()

    let otherExprs = filter (not . namedMain) exprs
        -- Note that, since we nest the let definitions here,
        -- mutual recursion is forbidden as of now.
        -- TODO: Allow definitions to refer to each other mutually recursively
        programExpr = foldr (\(name, ty, def) -> Let ty name def) mainExpr otherExprs

    pure $ (dataDecls, programExpr)

freeVars :: Type -> [String]
freeVars BoolType = []
freeVars IntType = []
freeVars (UserDefinedType _) = []
freeVars (ArrowType a b) = freeVars a `union` freeVars b
freeVars (AppType f x) = freeVars f `union` freeVars x
freeVars (TypeVar name) = [name]
freeVars (ForAll name body) = delete name $ freeVars body

-- Generalizes over unbound type variables
-- fact: freeVars (generalize ty) == []
generalize :: Type -> Type
generalize = foldr ForAll <*> freeVars

parens :: Bool -> String -> String
parens True str = "(" ++ str ++ ")"
parens False str = str

prettyType :: Type -> String
prettyType = prettyTypeP False

outermostForAlls :: Type -> ([String], Type)
outermostForAlls (ForAll name body) = first (name :) (outermostForAlls body)
outermostForAlls ty = ([], ty)

-- The argument "p" indicates whether the expression needs parenthesis or not
-- TODO: In the presence of function types and `AppType`s, this function
-- sometimes places unnecessary parenthesis.
prettyTypeP :: Bool -> Type -> String
prettyTypeP _ BoolType = "Bool"
prettyTypeP _ IntType = "Int"
prettyTypeP p (ArrowType a b) = parens p $ prettyTypeP True a ++ " -> " ++ prettyTypeP False b
prettyTypeP _ (UserDefinedType name) = name
prettyTypeP _ (TypeVar name) = name
prettyTypeP p (AppType f x) = parens p $ prettyTypeP (not $ isAppType f) f ++ " " ++ prettyTypeP True x
  where
    isAppType :: Type -> Bool
    isAppType (AppType _ _) = True
    isAppType _ = False
prettyTypeP p ty@(ForAll _ _) =
    let (vars, body) = outermostForAlls ty
    in parens p $ "forall " ++ unwords vars ++ ". " ++ prettyTypeP False body

-- Represents a data declaration, for example, "List a = Nil | Cons a (List a)"
data DataDecl = MkDataDecl
    { typeName :: String   -- "List"
    , typeVars :: [String] -- ["a"]
     -- Associates constructor names to their arguments
    , constructors :: [(String, [Type])] -- [(Nil, []), (Cons [a, List a])]
    }

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
    | Case Expr [(String, [String], Expr)] -- constructor name, constructor variables and body
    | Var String
    | Int Int
    | TypeApp Expr Type
    deriving Show

-- TODO: Fix spelling: DeBruijnExpr
data DeBruijExpr
    = DBLambda DeBruijExpr
    | DBApp DeBruijExpr DeBruijExpr

    -- DBLet holds the name of the defined variable (for error messages),
    -- an optional annotation (which is required if it is a recursive binding),
    -- the definition and the body where it's used
    | DBLet String (Maybe Type) DeBruijExpr DeBruijExpr

    | DBIfThenElse DeBruijExpr DeBruijExpr DeBruijExpr
    | DBTrue
    | DBFalse
    | DBAnn DeBruijExpr Type

    -- Holds the scrutinee and a list of cases, each holding the constructor
    -- tag and input types, as well as the case body (part after each arrow)
    | DBCase DeBruijExpr [(Natural, [Type], DeBruijExpr)]

    | DBVar Natural
    | DBInt Int
    | DBBuiltIn BuiltInFunction
    | DBConstructor String
    | DBTypeApp DeBruijExpr Type
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
toDeBruijn :: [DataDecl] -> Expr -> Either String DeBruijExpr
toDeBruijn dataDecls = go []
  where
    go :: [String] -> Expr -> Either String DeBruijExpr
    go vars (Lambda varName body) = second DBLambda $ go (varName:vars) body
    go vars (App f x) = DBApp <$> go vars f <*> go vars x
    go vars (IfThenElse bool thenBranch elseBranch) =
        DBIfThenElse <$> go vars bool <*> go vars thenBranch <*> go vars elseBranch
    go vars (Let ty varName definition body) =
        -- Since "let" can be recursive, both the definition and the body
        -- have access to variable it binds
        DBLet varName ty <$> go (varName : vars) definition <*> go (varName : vars) body
    -- The call to `elemIndexNat` comes first because the global name might be shadowed
    go vars (Var varName) = case elemIndexNat varName vars of
        Nothing -> if isConstructorDefined varName dataDecls
          then Right $ DBConstructor varName
          else case asBuiltInFunction varName of
            Just builtIn -> Right $ DBBuiltIn builtIn
            Nothing -> Left varName -- Unbound variable
        Just i -> Right $ DBVar i
    go vars (Case scrutinee cases) = do
        -- Resolve constructors here
        dbScrutinee <- go vars scrutinee

        dbCases <- forM cases $ \(conName, matchedVars, body) -> do
            dbBody <- go (reverse matchedVars ++ vars) body
            (tag, arity) <- note ("Not defined constructor " ++ conName ++ " used in pattern") $
                resolveConstructor dataDecls conName
            pure (tag, arity, dbBody)

        pure $ DBCase dbScrutinee dbCases

    go vars (TypeApp body ty) = DBTypeApp <$> go vars body  <*> pure ty

    go _ (Int i) = Right $ DBInt i
    go _ TrueExpr = Right DBTrue
    go _ FalseExpr = Right DBFalse
    go vars (Ann expr ty) = DBAnn <$> go vars expr <*> pure ty

-- Determines tag and arity of a constructor
resolveConstructor :: [DataDecl] -> String -> Maybe (Natural, [Type])
resolveConstructor decls conName = fmap swap $
    lookup conName $ concatMap (map reassoc . flip zip [0 :: Natural ..] . constructors) decls

isConstructorDefined :: String -> [DataDecl] -> Bool
isConstructorDefined = any . (\cons -> any ((== cons) . fst) . constructors)

-- Convenient functions for generating assembly
heapRegister :: Operand
heapRegister = Rcx

writeToPtr :: Operand -> Operand -> Instruction
writeToPtr = Mov . Dereference

writeToHeap :: Operand -> Instruction
writeToHeap = writeToPtr heapRegister

advanceHeapPtr :: Int -> Instruction
advanceHeapPtr = Add heapRegister . NumOperand

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

inferKind :: [(String, Kind)] -> Type -> Either String Kind
inferKind ctxt (ArrowType l r) = checkKind ctxt l Type >> checkKind ctxt r Type >> Right Type
inferKind ctxt (TypeVar a) = case lookup a ctxt of
    Just kind -> Right kind
    Nothing -> Left $ "Undefined type variable \"" ++ a ++ "\""
inferKind ctxt (AppType f x) = do
    kind <- inferKind ctxt f
    case kind of
        ArrowKind l r -> checkKind ctxt x l >> Right r
        Type -> Left $ "Expected a type constructor, but found a type, when checking " ++ prettyType f
inferKind ctxt (UserDefinedType name) = case lookup name ctxt of
    Just kind -> Right kind
    Nothing -> Left $ "Undefined name \"" ++ name ++ "\""
inferKind ctxt (ForAll name body) = do
    -- TODO: Allow for polymorphism over data constructors
    checkKind ((name, Type) : ctxt) body Type
    Right Type
inferKind _ BoolType = Right Type
inferKind _ IntType  = Right Type

checkKind :: [(String, Kind)] -> Type -> Kind -> Either String ()
checkKind ctxt ty kind = do
    kind' <- inferKind ctxt ty
    if kind == kind'
        then Right ()
        -- TODO: pretty-printing of kinds
        else Left $ "Expected kind " ++ show kind ++ " but got kind "
               ++ show kind' ++ " for " ++ show ty

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

-- Types of constructors and types of variables in scope
data Ctxt = MkCtxt
    { -- varTypes holds the types of the variables available in the current scope,
      -- which are identified by De Bruijn indices
      varTypes :: [Maybe Type]
      -- constructorMap associates constructors in scope to their types.
      -- Unlike usual variables, constructors are identified by name.
    , constructorMap :: [(String, Type)]
      -- definedTypes associates types in scope, identified by name, to their kinds
    , definedTypes :: [(String, Kind)]
      -- typeConsVars associates the names of the defined datatypes to the list of
      -- type variables they need to be applied to. Those would be 'a' and 'b' in
      -- 'Tree a b', for example.
    , typeConsVars :: [(String, [String])]
    } deriving (Show)

extend :: Ctxt -> Type -> Ctxt
extend ctxt ty = ctxt { varTypes =  Just ty : varTypes ctxt }

extendMany :: Ctxt -> [Type] -> Ctxt
extendMany ctxt types = ctxt { varTypes = map Just types ++ varTypes ctxt }

extendWithUnknownType :: Ctxt -> Ctxt
extendWithUnknownType ctxt = ctxt { varTypes =  Nothing : varTypes ctxt }

extendWithType :: String -> Ctxt -> Ctxt
extendWithType tyName ctxt = ctxt { definedTypes = (tyName, Type) : definedTypes ctxt }

infer :: Ctxt -> DeBruijExpr -> Either String Type
infer gamma (DBApp f x) = do
    functionTy <- infer gamma f
    (lhs, rhs) <- case functionTy of
        (ArrowType lhs rhs) -> pure (lhs, rhs)
        ty -> Left $ "Expected function type for " ++ show f ++ ", but got " ++ prettyType ty
    check gamma x lhs
    pure rhs
infer gamma (DBIfThenElse condition ifTrue ifFalse) = do
    check gamma condition BoolType
    returnTy <- infer gamma ifTrue
    check gamma ifFalse returnTy
    pure returnTy
infer gamma (DBAnn expr ty) = do
    checkKind (definedTypes gamma) ty Type
    check gamma expr ty
    pure ty
infer gamma (DBTypeApp e ty') = do
    -- As of now, it is assumed that 'forall' only abstracts over variables of kind Type
    checkKind (definedTypes gamma) ty' Type
    exprTy <- infer gamma e 
    (name, body) <- case exprTy of
        ForAll name body -> pure (name, body)
        _ -> Left $ "Expected polymorphic type for " ++ show e ++ ", but got " ++ prettyType exprTy
    pure $ substitute name ty' body
infer gamma (DBVar index) = case atIndex index $ varTypes gamma of
    (Just (Just ty)) -> pure ty
    (Just Nothing) -> Left "Recursive code without a type annotation"
    Nothing -> Left "Type checking error: Out of context DeBruijnIndex"
infer _ DBTrue = pure BoolType
infer _ DBFalse = pure BoolType
infer _ (DBInt _) = pure IntType
infer _ (DBBuiltIn builtIn) = pure $ builtInType builtIn
infer gamma (DBConstructor name) = case lookup name $ constructorMap gamma of
    Just ty -> Right ty
    Nothing -> Left $ "Constructor " ++ name ++ " does not have a defined type"
infer _ expr = Left $ "Failed to infer type for " ++ show expr

builtInType :: BuiltInFunction -> Type
builtInType BuiltInAdd = IntType `ArrowType` (IntType `ArrowType` IntType)
builtInType BuiltInEq  = IntType `ArrowType` (IntType `ArrowType` BoolType)

whenChecking :: String -> Either String a -> Either String a
whenChecking varName = first (("When checking " ++ varName ++ ": ") ++)

check :: Ctxt -> DeBruijExpr -> Type -> Either String ()
check gamma expr (ForAll name ty) = check (extendWithType name gamma) expr ty
check gamma (DBLambda body) ty
    | (ArrowType lhs rhs) <- ty = check (extend gamma lhs) body rhs
    | otherwise = Left $ "Lambda can't have type " ++ prettyType ty
check gamma (DBLet varName Nothing def body) ty = do -- If the let doesn't have an annotation
    -- Infer a type for the definition hoping it won't make a recursive call
    -- (If it does we are screwed and typechecking fails)
    defTy <- whenChecking varName $ infer (extendWithUnknownType gamma) def
    -- Then check the result (the part after "in")
    check (extend gamma defTy) body ty
check gamma (DBLet varName (Just ann) def body) ty = do -- If we do have an annotation things are easier:
    whenChecking ("the annotated type for " ++ varName) $
        checkKind (definedTypes gamma) ann Type -- Make sure the type annotation is reasonable
    whenChecking varName $ check (extend gamma ann) def ann -- Check the definition against the annotated type
    check (extend gamma ann) body ty -- Check the body against the type for the let
check gamma (DBCase scrutinee cases) ty = do
    -- We could be smart and infer the type of the scrutinee based on the patterns in each branch,
    -- but let's keep things simple for now and just infer it
    -- (scrTy is an abbreviation for "scrutinee type")
    scrTy <- infer gamma scrutinee

    let tyVarSubs = tyConVariables scrTy

    tyHead <- note ("Bad type for case scrutinee: " ++ prettyType scrTy) $ tyAppHead scrTy
    vars   <- note ("Undefined data constructor " ++ tyHead) $ lookup tyHead (typeConsVars gamma)

    -- It is important that all variables are substituted, otherwise there might be unbound type variables
    -- floating around in the types given to the variables created by pattern matching on a generic type
    if (length vars == length tyVarSubs)
        then pure ()
        -- Gettin in this second branch probably means there was a problem with inferring the
        -- type for the scrutinee, which might be due to a bug in "infer"
        else Left "Type checking error: type for case scrutinee is not fully applied"

    let instantionMap = zip vars tyVarSubs

        fullySubstitute :: Type -> Type
        fullySubstitute = flip (foldr (uncurry substitute)) instantionMap

    -- TODO: Check that the constructors mentioned in the patterns come from the type of the scrutinee
    forM_ cases $ \(_, types, body) ->
        -- Type check every case branch, with the new variables in scope
        check (extendMany gamma $ reverse $ map fullySubstitute types) body ty

check gamma expr ty = do
    inferredTy <- infer gamma expr
    if inferredTy == ty
      then Right ()
      else Left $ "Inferred type "
            ++ prettyType inferredTy
            ++ " does not match checking type "
            ++ prettyType ty

-- Determines what type constructor was used for a given type.
-- Informally, for example, tyAppHead (F Int Bool) = F
tyAppHead :: Type -> Maybe String
tyAppHead (AppType f _) = tyAppHead f
tyAppHead (UserDefinedType name) = Just name
tyAppHead _ = Nothing

-- Determines to which variables a type constructor is applied to.
-- Informally, for example, tyConVariables (F Int Bool) = [Int, Bool]
tyConVariables :: Type -> [Type]
tyConVariables (AppType f x) = tyConVariables f ++ [x]
tyConVariables _ = []


substitute :: String -> Type -> Type -> Type
substitute var ty (TypeVar name) = if name == var
    then ty
    else TypeVar name
substitute var ty (ArrowType a b) = ArrowType (substitute var ty a) (substitute var ty b)
substitute var ty (AppType f x) = AppType (substitute var ty f) (substitute var ty x)
-- Make sure the name bound by the forall shadows the substitution
substitute var ty (ForAll name body) = if var == name
    then ForAll name body
    else ForAll name $ substitute var ty body
substitute _ _ BoolType = BoolType
substitute _ _ IntType = IntType
substitute _ _ (UserDefinedType name) = UserDefinedType name

allDistinct :: Eq a => [a] -> Bool
allDistinct [] = True
allDistinct (x : xs) = all (/= x) xs && allDistinct xs

checkMain :: [DataDecl] -> DeBruijExpr -> Either String ()
checkMain dataDecls expr = do
    let ctx = MkCtxt
          { constructorMap = concatMap constructorTypes dataDecls
          , definedTypes = map (typeName &&& dataDeclKind) dataDecls
          , typeConsVars = map (typeName &&& typeVars) dataDecls
          , varTypes = []
          }

    -- Check that data declarations are well-formed:
    forM_ dataDecls $ \decl -> do
        -- Ensure that type variables all have distinct names
        let displayType = "data " ++ typeName decl ++ " " ++ unwords (typeVars decl)
        if not $ allDistinct $ typeVars decl
          then whenChecking displayType $ Left "not all type variables have distinct names"
          else pure ()

        -- Ensure that all types that are arguments to constructors
        -- are well-formed (that is, have kind type and don't mention undefined types)
        forM_ (constructors decl) $ \(_, argTypes) -> whenChecking displayType $
            let typesInCtxt = definedTypes ctx ++ map (, Type) (typeVars decl)
            in traverse (flip (checkKind typesInCtxt) Type) argTypes

    -- Check the main expression
    check ctx expr IntType

dataDeclKind :: DataDecl -> Kind
dataDeclKind decl = applyN (genericLength $ typeVars decl) (ArrowKind Type) Type
  where
    applyN :: Natural -> (a -> a) -> a -> a
    applyN n _ x | n <= 0 = x
    applyN n f x = f (applyN (n-1) f x)

constructorTypes :: DataDecl -> [(String, Type)]
constructorTypes = map . typeForConstructor <*> constructors

typeForConstructor :: DataDecl -> (String, [Type]) -> (String, Type)
typeForConstructor decl (conName, conArgs) = (conName, foldr ForAll typeWithArrows (typeVars decl))
  where
    typeWithArrows :: Type
    typeWithArrows = foldr ArrowType returnType conArgs

    returnType :: Type
    returnType = foldl AppType (UserDefinedType $ typeName decl) (map TypeVar $ typeVars decl)

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

arityFromType :: Type -> Natural
arityFromType (ArrowType _ b) = 1 + arityFromType b
arityFromType _ = 0

builtInArity :: BuiltInFunction -> Natural
builtInArity = arityFromType . builtInType

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

    -- Preserve Rbx, which is callee-saved in the C convention
    -- (This also aligns the stack for the printf call below)
    ++ [ Inst $ Push Rbx ]

    ++ start
    ++ [ Comment "Print the top of the stack" ]
    ++ map Inst
       [ Mov Rdi $ Symbol "digit_formatter"
       , Mov Rsi Rax
       , Xor Rax Rax
       , Call (Symbol "printf")
       , Pop Rbx -- Get Rbx back from the stack
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

