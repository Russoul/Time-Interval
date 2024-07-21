module Time.Display

import Data.String

import Time.Definition

export
showPadTwo : Integer -> String
showPadTwo x = case (x < 10) of
  True => "0" ++ show x
  False => show x

export
Show TimeUnit where
  show (MkTimeUnit a b) = showPadTwo a ++ ":" ++ showPadTwo b

export
Show TimeInterval where
  show (MkTimeInterval a b) = show a ++ "-" ++ show b

export
displayComment : String -> String
displayComment comment = "//" ++ joinBy "\n//" (lines comment)

export
displayCommentedTimeUnit : (String, TimeUnit) -> String
displayCommentedTimeUnit (comment, u) = displayComment comment ++ "\n" ++ show u

export
displayCommentedTimeUnitList : List (String, TimeUnit) -> String
displayCommentedTimeUnitList [] = ""
displayCommentedTimeUnitList [x] = displayCommentedTimeUnit x
displayCommentedTimeUnitList (x :: xs) = displayCommentedTimeUnit x ++ go xs where
  go : List (String, TimeUnit) -> String
  go [] = ""
  go (x :: xs) = "\n" ++ displayCommentedTimeUnit x ++ go xs

