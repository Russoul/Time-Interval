module Me.Russoul.Time.Definition

import Data.List1

-- HH:MM
public export
record TimeUnit where
  constructor MkTimeUnit
  hours : Integer
  minutes : Integer

-- HH:MM-HH:MM
public export
record TimeInterval where
  constructor MkTimeInterval
  start : TimeUnit
  end : TimeUnit

-- comment?
-- HH:MM-HH:MM
-- ...
-- HH:MM-HH:MM
public export
record TimeBlock where
  constructor MkTimeBlock
  comment : String
  intervals : List1 TimeInterval

public export
zero : TimeUnit
zero = MkTimeUnit 0 0
