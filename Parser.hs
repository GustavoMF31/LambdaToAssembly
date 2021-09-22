module Parser where

import Text.Parsec
import Text.Parsec.Char (char)
import Text.Parsec.String (Parser)

import Compile (Expr(..))
import Data.Char (isDigit)

validNameChar :: Char -> Bool
validNameChar = flip elem $ ['a' .. 'z'] ++ ['A' .. 'Z']

varName :: Parser String
varName = many1 $ satisfy validNameChar

exprPrefix :: Parser Expr
exprPrefix = do
    -- Integer literals
    x <- many1 (satisfy isDigit)
    pure $ Int $ read x
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
    exprInParens <- expr
    _ <- char ')'
    pure exprInParens
    -- Variables
 <|> Var <$> varName

expr :: Parser Expr
expr = foldl1 App <$> endBy1 exprPrefix spaces

-- Unsafe! Uses readFile.
parseFromFile :: String -> IO (Either ParseError Expr)
parseFromFile fileName = do
    fileContent <- readFile fileName
    pure $ parse (expr <* eof) fileName fileContent

