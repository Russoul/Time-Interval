module Me.Russoul.Time.Common

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
      show' (x :: xs) = "\n" ++ show x ++ show' xs
