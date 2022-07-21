import System.Exit (exitFailure)
import System.Environment (getArgs)

import Parser (parseFromFile)
import Compile (toDeBruijn, compile, asmToString, constructorNames, checkMain)

{-
term, idTerm, cardinal, kestrel, kite :: Expr
-- term = idTerm `App` Int 5
-- term = idTerm `App` idTerm `App` Int 5
-- term = kestrel `App` Int 5 `App` Int 4
-- term = kite
term = kite `App` Int 4 `App` Int 5
kestrel = Lambda "x" $ Lambda "y" $ Var "x"
cardinal = Lambda "f" $ Lambda "x" $ Lambda "y" $ Var "f" `App` Var "y" `App` Var "x"
kite = App cardinal kestrel
idTerm = Lambda "x" (Var "x")
-}

-- TODO: Strings
-- TODO: Printing (Or IO in general)
-- TODO: mul builtIn
-- TODO: Boolean OR
-- TODO: Infix binary operators
-- TODO: Comments
-- TODO: ADTs
-- TODO: Polymorphic Types
-- TODO: Garbage collection
main :: IO ()
main = do
    args <- getArgs
    file <- case args of
        [] -> exitWithMessage "No input file specified"
        [x] -> pure x
        _ -> exitWithMessage "Too many arguments"

    -- parseFromFile might crash due to the use of readFile
    parsed <- parseFromFile file 
    (dataDecls, expr) <- case parsed of
        Left e -> exitWithMessage $ "Parse error:\n" ++ show e
        Right x -> pure x

    dbExpr <- case toDeBruijn (constructorNames dataDecls) expr of
      Left var -> exitWithMessage $ "Out of scope variable: " ++ var
      Right dbExpr -> pure dbExpr

    case checkMain dataDecls dbExpr of
        Left err -> putStrLn $ "Type Error: " ++ err
        Right () -> pure ()

    writeFile "out.asm" $ asmToString $ compile dataDecls dbExpr

  where
    exitWithMessage msg = putStrLn msg >> exitFailure
