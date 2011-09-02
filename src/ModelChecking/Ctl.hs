module ModelChecking.Ctl where

import ModelChecking.Kripke
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
           | EF (Ctl a)
           | AX (Ctl a)
           | AF (Ctl a)
           | AG (Ctl a)
           | AU (Ctl a) (Ctl a)

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
eval k (AX f)       = eval k $ Neg $ EX $ Neg f
eval k (EF f)       = eval k (EU TT f)
eval k (AF f)       = eval k $ Neg $ EF $ Neg f
eval k (EG f)       = 
  let loop = [s|s<- states k,rel s s k,holds s k f] 
      inner = pred k f \\ loop
  in loop++if null inner then [] else evalEG inner k f
eval k (AG f)       = eval k $ Neg $ EG $ Neg f
eval k (EU f1 f2)   = let t = eval k f2 in evalEU t f1 k
eval k (AU f1 f2)   = 
  eval k $ ((Neg $ Neg f2) `EU` (Neg f1) `Conj` (Neg f2)) `Conj` AG f2

evalEU :: (Eq a,Kripke k) => [KripkeState] -> Ctl a -> k a -> [KripkeState]
evalEU t_i phi k = 
  let t_ip1 = [s | s <- eval k phi , not $ null (suc k s `intersect` t_i)]
      unionNew = nub $ t_i `union` t_ip1 in 
  if length unionNew == length t_i
  then t_i
  else evalEU unionNew phi k

-- |returns all non-loop states satisfying @EG f@ using a fixpoint iteration 
evalEG :: (Kripke k, Eq a) 
  => [KripkeState] -- ^current states satisfying @EG f@ 
  -> k a -- ^ the kripke structure
  -> Ctl a -- ^formula @f@
  -> [KripkeState]
evalEG is k f = 
  let newGs      = is `intersect` (nub $ concatMap (pre k) is)
      unionIsNew = nub $ newGs `union` is in
  if length is == length unionIsNew 
  then is
  else evalEG unionIsNew k f

-- |returns all states whose successors satisfy given formula
pred :: (Kripke k, Eq a) => k a -> Ctl a -> [KripkeState]
pred k f = nub $ concatMap (pre k) $ eval k f

