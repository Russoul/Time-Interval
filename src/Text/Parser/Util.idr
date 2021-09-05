module Text.Parser.Util

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.Fin

import public Text.Parser
import Text.Lexer

public export
Digit : Type
Digit = Fin 10

public export
ignore : {c : _} -> Grammar s tok c a -> Grammar s tok c ()
ignore = map (const ())

||| Define parsers as consuming grammers over characters.
public export
Parser : (ty : Type) -> Type
Parser ty = Grammar () Char True ty

export
toString : {c : _}
        -> Foldable t
        => Grammar s tok c (t Char)
        -> Grammar s tok c String
toString p = map (foldr (\char, str => cast char ++ str) "") p

export
lower : Parser Char
lower = terminal "lower" (\x => toMaybe (isLower x) x)

export
upper : Parser Char
upper = terminal "upper" (\x => toMaybe (isUpper x) x)

export
alpha : Parser Char
alpha = terminal "alpha" (\x => toMaybe (isAlpha x) x)

public export
mbDigit : Char -> Maybe Digit
mbDigit '0' = Just 0
mbDigit '1' = Just 1
mbDigit '2' = Just 2
mbDigit '3' = Just 3
mbDigit '4' = Just 4
mbDigit '5' = Just 5
mbDigit '6' = Just 6
mbDigit '7' = Just 7
mbDigit '8' = Just 8
mbDigit '9' = Just 9
mbDigit _   = Nothing

export
digit : Parser Digit
digit = terminal "digit" mbDigit

export
digits : Parser (List1 Digit)
digits = some digit


littleEndianBase10ToNat : List Digit -> Nat
littleEndianBase10ToNat [] = 0
littleEndianBase10ToNat (x :: xs) = finToNat x + 10 * littleEndianBase10ToNat xs

||| Big-endian string of base10 digits to Nat
public export
[BigEndianBase10] Cast (List1 Digit) Nat where
  cast = littleEndianBase10ToNat . forget . reverse

public export
nat : Parser Nat
nat = map (cast @{BigEndianBase10}) digits

export
alphaNum : Grammar s Char True Char
alphaNum = terminal "alphanumeric" (\x => toMaybe (isAlphaNum x) x)

export
space : Grammar s Char True Char
space = terminal "space" (\x => toMaybe (x == ' ') x)

export
newline : Grammar s Char True Char
newline = terminal "newline" (\x => toMaybe (isNL x) x)

export
is : Eq a => String -> (a -> Bool) -> Grammar s a True a
is msg f = terminal msg (\x => toMaybe (f x) x)

||| Parse an exact char. Case-sensetive.
export
char : Char -> Parser Char
char c = terminal (cast c) (\x => toMaybe (x == c) x)

||| Parse anything but the given char.
export
notChar : Char -> Parser Char
notChar c = terminal "notChar" (\x => toMaybe (x /= c) x)

||| Parse any token.
export
any : Grammar s tok True tok
any = terminal "Any" (Just . id)

||| Parse any token, not defined by the given grammar.
export
not : Grammar s tok True tok -> Grammar s tok True tok
not g = do
  g' <- map Just g <|> pure Nothing
  case the (Maybe tok) g' of
    Nothing => any {s, tok}
    Just _ => fail "Not"

||| Parse one char from the list.
||| Prefer ones closer to the head of the list.
||| Fail if the list is empty or none of the chars matches.
export
oneOf : String -> Parser Char
oneOf str =
  case fastUnpack str of
    [] => fail "oneOf \"\""
    x :: rest => char x <|> go rest
 where
  go : List Char -> Parser Char
  go [] = fail "oneOf: no match"
  go (x :: xs) = char x <|> go xs

||| Parser an exact char. Case-insensetive.
export
charLike : Char -> Parser Char
charLike c =
  char (toLower c) <|> char (toUpper c)

export
consumesList : List (c ** Grammar s tok c a) -> Bool
consumesList [] = False
consumesList ((c ** _) :: xs) = c || consumesList xs

export
consumesList1 : List1 (c ** Grammar s tok c a) -> Bool
consumesList1 ((c ** _) ::: xs) = c || consumesList xs

export
seqList : (gs : List (c ** Grammar s tok c a))
       -> Grammar s tok (consumesList gs) (List a)
seqList [] = pure []
seqList ((_ ** x) :: xs) = map (::) x <*> seqList xs

export
seqList1 : (gs : List1 (c ** Grammar s tok c a))
        -> Grammar s tok (consumesList1 gs) (List1 a)
seqList1 ((_ ** x) ::: xs) = map (:::) x <*> seqList xs

||| Non-empty string. Case-sensitive.
export
str : String -> Parser String
str c =
  case fastUnpack c of
    [] => fail "str \"\""
    x :: xs => toString $
      seqList1 ((_ ** char x) ::: map (\x => (_ ** char x)) xs)

||| Non-empty string. Case-insensitive.
export
strLike : String -> Parser String
strLike c =
  case fastUnpack c of
    [] => fail "strLike \"\""
    x :: xs => toString $
      seqList1 ((_ ** charLike x) ::: map (\x => (_ ** charLike x)) xs)

||| Run the parser on the list of tokens,
||| expecting full consumption of the input.
export
parseFull : {c : _}
         -> (act : Grammar () tok c ty)
         -> (xs : List tok)
         -> Either (List1 (ParsingError tok)) ty
parseFull act xs = do
  (x, []) <- parse act (map irrelevantBounds xs)
    | (x, _ :: _) => Left (singleton $ Error "Some input left unconsumed" Nothing)
  Right x

export
parseFull' : {c : _}
          -> (act : Grammar () Char c ty)
          -> (xs : String)
          --        vvvvvv Error Msg
          -> Either String ty
parseFull' act xs =
  mapFst (\(Error str tok ::: _) => str) $
    parseFull act (fastUnpack xs)

