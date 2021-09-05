module Time


import Data.String
import Data.Nat
import Data.Fin
import Data.List1
import Data.List
import Data.Either
import Data.Maybe

import Text.Parser
import Text.Parser.Util

import System.File

-- HH:MM
record TimeUnit where
  constructor MkTimeUnit
  hours : Integer
  minutes : Integer

-- HH:MM-HH:MM
record TimeInterval where
  constructor MkTimeInterval
  start : TimeUnit
  end : TimeUnit

twoDigitNat : Parser Nat
twoDigitNat = do
  d0 <- digit
  d1 <- digit
  pure (10 * finToNat d0 + finToNat d1)

||| Discards whitespace.
||| N:N
parseTimeUnit : Parser TimeUnit
parseTimeUnit = do
  a <- twoDigitNat
  ignore $ many space
  ignore $ char ':'
  ignore $ many space
  b <- twoDigitNat
  pure (MkTimeUnit (cast a) (cast b))

parseTimeInterval : Parser TimeInterval
parseTimeInterval = do
  s <- parseTimeUnit
  ignore $ many space
  ignore $ char '-'
  ignore $ many space
  e <- parseTimeUnit
  pure (MkTimeInterval s e)

asymmetricDif : Integer -> Integer -> Integer -> (Bool, Integer)
asymmetricDif x y m =
  case (x <= y) of
    True => (True, y - x)
    False => (False, m - (x - y))

intervalDif : (start : TimeInterval) -> TimeUnit
intervalDif (MkTimeInterval (MkTimeUnit sh sm) (MkTimeUnit eh em)) =
  let (v, m) = asymmetricDif sm em 60 in
  let (_, h) = asymmetricDif sh eh 24 in
  MkTimeUnit (abs (h - if v then 0 else 1)) m

sum : TimeUnit -> TimeUnit -> TimeUnit
sum (MkTimeUnit a b) (MkTimeUnit c d) =
  let m = mod (b + d) 60 in
  let d = div (b + d) 60 in
  MkTimeUnit (a + c + d) m

showPadTwo : Integer -> String
showPadTwo x = case (x < 10) of
  True => "0" ++ show x
  False => show x

public export
Show TimeUnit where
  show (MkTimeUnit a b) = showPadTwo a ++ ":" ++ showPadTwo b

public export
Show TimeInterval where
  show (MkTimeInterval a b) = show a ++ "-" ++ show b

eTimeInterval : String -> Either String TimeInterval
eTimeInterval str =
  mapFst (const "Can't parse '\{str}'") (parseFull' parseTimeInterval str)

lineFilter : String -> Bool
lineFilter x = x /= ""
            && x /= "\n"
            && x /= "\r"
            && not (isPrefixOf "//" x)
            && not (isPrefixOf "--" x)


namespace Show
  namespace Str
    public export
    [Id]
    Show String where
      show x = x

  public export
  [NLSepList]
  (inner : Show a) => Show (List a) where
    show []        = ""
    show (x :: xs) = show x ++ show' xs
     where
      show' : List a -> String
      show' []        = ""
      show' (x :: xs) = show' xs ++ "\n" ++ show x

main : IO ()
main = do
  fileName <- getLine
  Right str <- readFile fileName
    | Left err => putStrLn (show err)
  let ls = lines str
  let ls = filter lineFilter ls
  putStrLn $ "Intervals:\n" ++ show @{NLSepList @{Id}} ls
  let ds =
       do ds <- for ls $ \l => do
             i <- eTimeInterval l
             Right (intervalDif i)
          Right $ foldr sum (MkTimeUnit 0 0) ds
  case ds of
    Left x => putStrLn ("Error: " ++ x)
    Right ds => putStrLn ("Total: " ++ show ds)
