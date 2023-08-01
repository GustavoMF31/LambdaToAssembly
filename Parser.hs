{-# LANGUAGE BlockArguments #-}

module Parser where

import Text.Parsec hiding (spaces)
import Text.Parsec.String (Parser)

import Compile (Expr(..), Type(..), DataDecl(..), generalize)
import Data.Char (isDigit, isUpper, isLower)
import Data.Maybe (isJust)
import Control.Monad (guard, void)
import Data.Either (partitionEithers)

validNameChar :: Char -> Bool
validNameChar = flip elem $ ['a' .. 'z'] ++ ['A' .. 'Z']

keywords :: [String]
keywords = ["if", "then", "else", "let", "in", "data", "case", "of", "forall", "Int", "Bool", "True", "False"]

-- TODO: We might need "try" here just like in conVarName
simpleName :: Parser String
simpleName = do
    prefix <- many1 $ satisfy validNameChar
    suffix <- many $ satisfy (`elem` '\'' : ['0' .. '9'])
    let name = prefix ++ suffix
    guard $ name `notElem` keywords
    pure name

-- TODO: Same
varName :: Parser String
varName = do
    name <- simpleName
    guard $ firstLower name
    pure name

firstUpper :: String -> Bool
firstUpper [] = True
firstUpper (x : _) = isUpper x

firstLower :: String -> Bool
firstLower [] = True
firstLower (x : _) = isLower x

conVarName :: Parser String
conVarName = try $ do -- "try" here makes sure it either consumes the whole variable of none of it
    conName <- simpleName
    guard $ firstUpper conName
    pure conName

-- An empty line signals the end of a definition,
-- so "spaces" must respect it
spaces :: Parser ()
spaces = skipMany $
    void (char ' ') <|> try (char '\n' *> notFollowedBy (char '\n'))

-- TODO: Better parse error messages
-- (Seems like everything is turning into "unexpected ':'"

{- HLINT ignore "Use <$>" -}
exprPrefix :: Parser Expr
exprPrefix = do
    -- Integer literals
    isNegative <- isJust <$> optionMaybe (char '-')
    x <- many1 (satisfy isDigit)
    pure $ Int $ (if isNegative then negate else id) $ read x
 <|> TrueExpr <$ string "True"
 <|> FalseExpr <$ string "False"
 <|> do
    -- If expressions
    _ <- try $ string "if"
    spaces
    condition <- expr
    spaces
    _ <- string "then"
    spaces
    trueBranch <- expr
    spaces
    _ <- string "else"
    spaces
    falseBranch <- expr
    pure $ IfThenElse condition trueBranch falseBranch
 <|> do
    -- Lambdas
    _ <- char '\\'
    variables <- endBy1 varName (optional spaces)
    _ <- string "->"
    _ <- spaces
    body <- expr
    pure $ foldr Lambda body variables
 <|> do
    -- Parenthesized expressions
    _ <- char '('
    spaces
    exprInParens <- expr
    spaces
    -- Type annotations
    maybeAnn <- optionMaybe $ string ":" *> spaces *> parseType
    _ <- char ')'
    pure $ case maybeAnn of
        Nothing -> exprInParens
        Just ty -> Ann exprInParens ty
 <|> do
    -- Let expressions
    _ <- try $ string "let"
    spaces
    (ty, (name, def)) <- definitionWithType
    spaces
    _ <- string "in"
    spaces
    body <- expr
    pure $ Let ty name def body
 <|> do
    -- Case expression
    _ <- try $ string "case"
    spaces
    scrutinee <- expr
    spaces
    _ <- string "of"
    spaces
    branches <- caseAlternative `sepEndBy` (spaces >> char ';' >> spaces)
    pure $ Case scrutinee branches
 <|> try do -- Try is necessary to avoid consuming keywords such as `then` and `else`
    -- Variables (which might be constructors)
    name <- simpleName
    pure $ Var name
 <?> "expression"

caseAlternative :: Parser (String, [String], Expr)
caseAlternative = do
    conName <- conVarName
    spaces
    vars <- varName `sepEndBy` spaces
    spaces
    _ <- string "->"
    spaces
    body <- expr
    pure (conName, vars, body)

typeApp :: Parser Type
typeApp = char '@' >> parseTypePrefix

-- TODO: This is really just a fold, isn't it?
buildApplication :: Expr -> [Either Expr Type] -> Expr
buildApplication e [] = e
buildApplication e (Left e' : xs) = buildApplication (App e e') xs
buildApplication e (Right ty : xs) = buildApplication (TypeApp e ty) xs

expr :: Parser Expr
expr = do
    firstExpr <- exprPrefix
    optional spaces
    fragments <- sepEndBy (Left <$> exprPrefix <|> Right <$> typeApp) spaces
    pure $ buildApplication firstExpr fragments

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

exactly :: String -> Parser String
exactly s = do
    result <- string s
    notFollowedBy $ satisfy validNameChar
    pure result

parseTypePrefix :: Parser Type
parseTypePrefix = do
    parens parseType
    <|> (BoolType <$ try (exactly "Bool"))
    <|> (IntType  <$ try (exactly "Int"))
    <|> do -- ForAll
      _ <- try $ string "forall"
      spaces
      vars <- sepEndBy varName spaces
      spaces
      _ <- char '.'
      spaces
      body <- parseType
      pure $ foldr ForAll body vars
    <|> (UserDefinedType <$> conVarName)
    <|> (TypeVar <$> varName)
    <?> "type"

parseType :: Parser Type
parseType = chainr1 parseTypePrefix (ArrowType <$ try (spaces >> string "->" >> spaces))

-- TODO: Remove the code duplication between definitionWithType and definition
definitionWithType :: Parser (Maybe Type, (String, Expr))
definitionWithType = do
    name <- varName
    spaces

    ty <- optionMaybe $ do
      _ <- string ":"
      spaces
      ty <- parseType
      spaces
      _ <- string name
      spaces
      pure ty

    -- Parse variables on the LHS of the definition
    -- to support things like "f x = x" in place of "f = \x -> x"
    varNames <- varName `sepEndBy` spaces

    _ <- char '='
    spaces

    body <- expr
    pure (fmap generalize ty, (name, foldr Lambda body varNames))

definition :: Parser (String, Expr)
definition = do
    name <- varName

    varNames <- varName `sepEndBy` spaces
    spaces
    _ <- char '='
    spaces

    body <- expr

    pure (name, foldr Lambda body varNames)

dataDecl :: Parser DataDecl
dataDecl = do
    _ <- try $ string "data"
    spaces
    tyName <- conVarName
    spaces
    _ <- char '='
    spaces
    constructorsDecls <- constructor `sepBy` (char '|' >> spaces)
    pure $ MkDataDecl tyName constructorsDecls
  where
    constructor = do
        conName <- conVarName
        spaces
        inputTypes <- parseType `sepEndBy` spaces
        pure (conName, inputTypes)

file :: Parser ([DataDecl], Expr)
file = do
    decls <- (Left <$> try definitionWithType <|> Right <$> dataDecl) `sepEndBy` string "\n\n"
    let (defs, dataDecls) = partitionEithers decls
    spaces
    main <- expr
    spaces
    let programExpr = foldr (\(ty, (name, def)) ->  Let ty name def) main defs
    pure (dataDecls, programExpr)

-- Unsafe! Uses readFile.
parseFromFile :: String -> IO (Either ParseError ([DataDecl], Expr))
parseFromFile fileName = do
    fileContent <- readFile fileName
    pure $ parse (file <* eof) fileName fileContent

