module Time.Parser

import Data.String

import Text.Parser.CharUtil

import Time.Definition

||| Discards whitespace.
||| N:N
export
parseTimeUnit : CharParser TimeUnit
parseTimeUnit = do
  a <- twoDigitNat
  ignore $ many space
  ignore $ char ':'
  ignore $ many space
  b <- twoDigitNat
  pure (MkTimeUnit (cast a) (cast b))

export
parseTimeInterval : CharParser TimeInterval
parseTimeInterval = do
  s <- parseTimeUnit
  ignore $ many space
  ignore $ char '-'
  commit
  ignore $ many space
  e <- parseTimeUnit
  pure (MkTimeInterval s e)

export
parseCommentLine : CharParser String
parseCommentLine = do
  ignore $ many space
  char_ '/'
  char_ '/'
  commit
  chars <- many $ such (\c => c /= '\n')
  newline
  pure $ pack chars

export
parseBlock : CharParser TimeBlock
parseBlock = do
  comment <- many parseCommentLine <&> joinBy "\n"
  commit
  intervals <- sepBy1 newline parseTimeInterval
  pure $ MkTimeBlock comment intervals

export
parseFile : CharParser (List TimeBlock)
parseFile = do
  ignore $ many space
  r <- sepBy (newline *> newline *> many newline) parseBlock
  ignore $ many (space <|> newline)
  pure r

