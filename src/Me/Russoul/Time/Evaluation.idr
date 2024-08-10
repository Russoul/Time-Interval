module Me.Russoul.Time.Evaluation

import Data.List1

import Me.Russoul.Time.Definition

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

export
sum : TimeUnit -> TimeUnit -> TimeUnit
sum (MkTimeUnit a b) (MkTimeUnit c d) =
  let m = mod (b + d) 60 in
  let d = div (b + d) 60 in
  MkTimeUnit (a + c + d) m


export
summateBlock : TimeBlock -> (String, TimeUnit)
summateBlock (MkTimeBlock comment block) = (comment, go block) where
  go : List1 TimeInterval -> TimeUnit
  go = foldr1 sum . map intervalDif
