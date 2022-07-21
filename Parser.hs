{-# LANGUAGE BlockArguments #-}

module Parser where

import Text.Parsec hiding (spaces)
import Text.Parsec.Char (char)
import Text.Parsec.String (Parser)

import Compile (Expr(..), Type(..), DataDecl(..))
import Data.Char (isDigit)
import Data.Maybe (isJust)
import Control.Monad (guard, void)
import Data.Either (partitionEithers)

validNameChar :: Char -> Bool
validNameChar = flip elem $ ['a' .. 'z'] ++ ['A' .. 'Z']

keywords :: [String]
keywords = ["if", "then", "else", "let", "in", "data", "Int", "Bool", "True", "False"]

varName :: Parser String
varName = do
    name <- many1 $ satisfy validNameChar
    guard $ name `notElem` keywords
    pure name

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
 <|> try do -- Try is necessary to avoid consuming keywords such as `then` and `else`
    -- Variables
    name <- varName
    pure $ Var name
 <?> "expression"

expr :: Parser Expr
expr = foldl1 App <$> endBy1 exprPrefix spaces

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

parseTypePrefix :: Parser Type
parseTypePrefix = do
    parens parseType
    <|> (BoolType <$ string "Bool")
    <|> (IntType  <$ string "Int")
    <|> (UserDefinedType <$> varName)
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
    pure (ty, (name, foldr Lambda body varNames))

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
    tyName <- varName
    spaces
    _ <- char '='
    spaces
    constructorsDecls <- constructor `sepBy` (char '|' >> spaces)
    pure $ MkDataDecl tyName constructorsDecls
  where
    constructor = do
        conName <- varName
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

