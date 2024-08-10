module Me.Russoul.Time.Application

import Data.String
import Data.Nat
import Data.Fin
import Data.List1
import Data.List
import Data.Either
import Data.Maybe

import Me.Russoul.Text.Parser.OverChar

import System
import System.File

import Me.Russoul.Time.Common
import Me.Russoul.Time.Definition
import Me.Russoul.Time.Display
import Me.Russoul.Time.Evaluation
import Me.Russoul.Time.Parser

doParseFile : String -> Either String (List TimeBlock)
doParseFile str =
  mapFst show (parseAllFirstError parseFile str)

main : IO ()
main = do
  [_, fileName] <- getArgs
    | _ => do
      putStrLn "Usage: time <file>"
      exitFailure
  Right str <- readFile fileName
    | Left err => putStrLn (show err)
  putStrLn "---------------------------------------------"
  putStrLn "----------------- RESULTS -------------------"
  putStrLn "---------------------------------------------"
  let Right blocks = doParseFile str
    | Left err => putStrLn ("Error: " ++ err)
  let computed = map summateBlock blocks
  putStrLn (displayCommentedTimeUnitList computed)
  putStrLn "------------------------"
  putStrLn ("Total: " ++ show (foldr sum zero (map snd computed)))
