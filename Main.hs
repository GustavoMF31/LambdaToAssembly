import System.Exit (exitFailure)
import System.Environment (getArgs)

import Parser (parseFromFile)
import Compile (toDeBruijn, declsToProgram, compile, asmToString, checkMain)

-- TODO: Strings
-- TODO: Printing (Or IO in general)
-- TODO: mul builtIn
-- TODO: Boolean OR
-- TODO: Infix binary operators
-- TODO: Comments
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
    defs <- case parsed of
        Left e -> exitWithMessage $ "Parse error:\n" ++ show e
        Right x -> pure x

    (dataDecls, programExpr) <- case declsToProgram defs of
        Left e -> exitWithMessage e
        Right x -> pure x

    dbExpr <- case toDeBruijn dataDecls programExpr of
      Left var -> exitWithMessage $ "Out of scope variable: " ++ var
      Right dbExpr -> pure dbExpr

    case checkMain dataDecls dbExpr of
        Left err -> putStrLn $ "Type Error: " ++ err
        Right () -> pure ()

    writeFile "out.asm" $ asmToString $ compile dataDecls dbExpr

  where
    exitWithMessage msg = putStrLn msg >> exitFailure
