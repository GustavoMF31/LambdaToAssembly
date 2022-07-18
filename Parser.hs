{-# LANGUAGE BlockArguments #-}

module Parser where

import Text.Parsec
import Text.Parsec.Char (char)
import Text.Parsec.String (Parser)

import Compile (Expr(..))
import Data.Char (isDigit)
import Data.Maybe (isJust)
import Control.Monad (guard)

validNameChar :: Char -> Bool
validNameChar = flip elem $ ['a' .. 'z'] ++ ['A' .. 'Z']

varName :: Parser String
varName = many1 $ satisfy validNameChar

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
    _ <- char ')'
    pure exprInParens
 <|> do
    -- Let expressions
    _ <- try $ string "let"
    spaces
    name <- varName
    spaces
    _ <- char '='
    spaces
    definition <- expr
    spaces
    _ <- string "in"
    spaces
    body <- expr
    pure $ Let name definition body
 <|> try do -- Try is necessary to avoid consuming keywords such as `then` and `else`
    -- Variables
    name <- varName
    guard $ name `notElem` ["if", "then", "else", "let", "in"]
    pure $ Var name

expr :: Parser Expr
expr = foldl1 App <$> endBy1 exprPrefix spaces

-- Unsafe! Uses readFile.
parseFromFile :: String -> IO (Either ParseError Expr)
parseFromFile fileName = do
    fileContent <- readFile fileName
    pure $ parse (expr <* eof) fileName fileContent

