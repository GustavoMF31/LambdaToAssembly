-- TODO: Use Haskell 2021
{-# LANGUAGE TupleSections #-}

module TypeCheck (Expr(..), Type(..), DataDecl(..), Declaration(..), DeBruijExpr(..),
                  BuiltInFunction(..), toDeBruijn, checkMain, generalize, declsToProgram,
                  builtInName, builtIns, builtInArity) where

import Numeric.Natural (Natural)
import Control.Monad (forM, forM_)
import Control.Arrow ((&&&))
import Data.List (union, delete, genericLength)
import Data.Either (partitionEithers)
import Data.Bifunctor (second, Bifunctor (first))

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

data Kind
    = ArrowKind Kind Kind
    | Type
    deriving (Eq, Show)

data Type
    = ArrowType Type Type
    | AppType Type Type
    | BoolType
    | IntType
    | UnitType
    | UserDefinedType String

    -- An element of type IO a is represented at runtime as:
    -- [ continuation_ptr | current_action_ptr | current_action_args[0] | .. ]
    | IOType

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

ioUnit :: Type
ioUnit = AppType IOType UnitType

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
        Just ty -> if ty == ioUnit
            then pure ()
            else Left $ "Expected main to have type " ++ prettyType ioUnit ++ ", but found type " ++ prettyType ty
        Nothing -> pure ()

    let otherExprs = filter (not . namedMain) exprs
        -- Note that, since we nest the let definitions here,
        -- mutual recursion is forbidden as of now.
        -- TODO: Allow definitions to refer to each other mutually recursively
        programExpr = foldr (\(name, ty, def) -> Let ty name def) mainExpr otherExprs

    pure $ (dataDecls, programExpr)

freeVars :: Type -> [String]
freeVars BoolType = []
freeVars UnitType = []
freeVars IntType = []
freeVars IOType = []
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
prettyTypeP _ UnitType = "()"
prettyTypeP _ IOType = "IO"
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
    | PrintInt
    | Pure
    | Bind
    deriving (Show, Enum, Bounded)

builtInName :: BuiltInFunction -> String
builtInName BuiltInAdd = "add"
builtInName BuiltInEq  = "eq"
builtInName PrintInt  = "printInt"
builtInName Pure  = "pure"
builtInName Bind  = "bind"

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
inferKind _ IOType = Right $ ArrowKind Type Type
inferKind _ BoolType = Right Type
inferKind _ IntType  = Right Type
inferKind _ UnitType = Right Type

checkKind :: [(String, Kind)] -> Type -> Kind -> Either String ()
checkKind ctxt ty kind = do
    kind' <- inferKind ctxt ty
    if kind == kind'
        then Right ()
        -- TODO: pretty-printing of kinds
        else Left $ "Expected kind " ++ show kind ++ " but got kind "
               ++ show kind' ++ " for " ++ show ty


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
builtInType PrintInt   = IntType `ArrowType` ioUnit
builtInType Pure       = IntType `ArrowType` ioUnit
builtInType Bind       = ForAll "a" $ TypeVar "a" `ArrowType` (IOType `AppType` TypeVar "a")

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
substitute _ _ UnitType = UnitType
substitute _ _ IOType = IOType
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
    check ctx expr ioUnit

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

arityFromType :: Type -> Natural
arityFromType (ArrowType _ b) = 1 + arityFromType b
arityFromType (ForAll _ body) = arityFromType body
arityFromType _ = 0

builtInArity :: BuiltInFunction -> Natural
builtInArity = arityFromType . builtInType
