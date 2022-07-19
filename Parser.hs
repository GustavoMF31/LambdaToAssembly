{-# LANGUAGE BlockArguments #-}

module Parser where

import Text.Parsec hiding (spaces)
import Text.Parsec.Char (char)
import Text.Parsec.String (Parser)

import Compile (Expr(..), Type(..))
import Data.Char (isDigit)
import Data.Maybe (isJust)
import Control.Monad (guard, void)

validNameChar :: Char -> Bool
validNameChar = flip elem $ ['a' .. 'z'] ++ ['A' .. 'Z']

keywords :: [String]
keywords = ["if", "then", "else", "let", "in", "Int", "Bool"]

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

-- TODO: True and False
{- HLINT ignore "Use <$>" -}
exprPrefix :: Parser Expr
exprPrefix = do
    -- Integer literals
    isNegative <- isJust <$> optionMaybe (char '-')
    x <- many1 (satisfy isDigit)
    pure $ Int $ (if isNegative then negate else id) $ read x
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
    (name, def) <- definition
    spaces
    _ <- string "in"
    spaces
    body <- expr
    -- TODO: Parse type annotations
    pure $ Let Nothing name def body
 <|> try do -- Try is necessary to avoid consuming keywords such as `then` and `else`
    -- Variables
    name <- varName
    pure $ Var name

expr :: Parser Expr
expr = foldl1 App <$> endBy1 exprPrefix spaces

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

parseTypePrefix :: Parser Type
parseTypePrefix = do
    parens parseType
    <|> (BoolType <$ string "Bool")
    <|> (IntType  <$ string "Int")

parseType :: Parser Type
parseType = chainr1 parseTypePrefix (ArrowType <$ try (spaces >> string "->" >> spaces))

topLevelDefinition :: Parser (Maybe Type, (String, Expr))
topLevelDefinition = do
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

    _ <- char '='
    spaces

    body <- expr
    pure (ty, (name, body))

definition :: Parser (String, Expr)
definition = do
    name <- varName

    spaces
    _ <- char '='
    spaces

    body <- expr

    pure (name, body)

file :: Parser Expr
file = do
    definitions <- try topLevelDefinition `sepEndBy` string "\n\n"
    spaces
    main <- expr
    spaces
    pure $ foldl (\body (ann, (name, def)) -> Let ann name def body) main definitions

-- Unsafe! Uses readFile.
parseFromFile :: String -> IO (Either ParseError Expr)
parseFromFile fileName = do
    fileContent <- readFile fileName
    pure $ parse (file <* eof) fileName fileContent

