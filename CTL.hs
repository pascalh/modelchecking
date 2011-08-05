module CTL where

import Kripke
import Prelude hiding (pred)
import Data.List ((\\),union,intersect,nub)

data Ctl a = TT 
           | FF
           | AP a
           | Neg (Ctl a)
           | Disj (Ctl a) (Ctl a) 
           | Conj (Ctl a) (Ctl a)
           | EX (Ctl a)
           | EU (Ctl a) (Ctl a)
           | EG (Ctl a)

-- |returns whether formula holds at a specific state
holds :: (Kripke k, Eq a) => KripkeState -> k a -> Ctl a -> Bool
holds s k f= s `elem` eval k f

-- |returns all states for which given formula holds
-- (using the labeling algorithm)
eval :: (Kripke k ,Eq a) => k a -> Ctl a -> [KripkeState]
eval k TT           = states k
eval k FF           = []
eval k (AP a)       = [s| s <- states k, a `elem` labels s k]
eval k (Neg f)      = states k \\ eval k f
eval k (Conj f1 f2) = eval k f1 `intersect` eval k f2
eval k (Disj f1 f2) = nub $ eval k f1 `union` eval k f2
eval k (EX f)       = pred k f
eval k (EG f)       = nub $ eval k f `intersect` pred k (EG f)
eval k (EU f1 f2)   = nub $ 
  eval k f2 `intersect` (nub $ eval k f1 `union` pred k (EU f1 f2))

-- |returns all states whose successors satisfy given formula
pred :: (Kripke k, Eq a) => k a -> Ctl a -> [KripkeState]
pred k f = nub $ concatMap (pre k) $ eval k f

