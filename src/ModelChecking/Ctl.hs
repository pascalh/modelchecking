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

br s= "("++s++")"

instance Show a => Show (Ctl a) where
  show TT           = "True"
  show FF           = "False"
  show (AP a)       = show a
  show (Neg a)      = br $ "¬"++show a
  show (Disj a1 a2) = br $ show a1++" || "++show a2
  show (Conj a1 a2) = br $ show a1++" && "++show a2
  show (EX a)       = "EX "++show a
  show (AX a)       = "AX "++show a
  show (AG a)       = "AG "++show a
  show (EF a)       = "EF "++show a
  show (AF a)       = "AF "++show a
  show (EG a)       = "EG "++show a
  show (AU a1 a2)   = "A"++(br $ show a1)++" U "++ (br $ show a2)
  show (EU a1 a2)   = "E"++(br $ show a1)++" U "++ (br $ show a2)
 

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
eval k (AF f)       = eval k $ Neg $ EG $ Neg f
eval k (EG f)       = evalEG f k (eval k f) 
eval k (AG f)       = eval k $ Neg $ EF $ Neg f
eval k (EU f1 f2)   = evalEU f1 k (eval k f2)
eval k (AU f1 f2)   = 
  eval k $ 
    (Neg $ (Neg f2) `EU` (Neg f1) `Conj` (Neg f2)) 
    `Conj` 
    (Neg $ EG $ Neg f2)

evalEU :: (Eq a,Kripke k) => Ctl a -> k a -> [KripkeState] -> [KripkeState]
evalEU f1 k t = 
  let t1 = nub $ t `union` [s | s<-eval k f1 
                           , not $ null $ suc k s `intersect` t] in
  if length t1 == length t then t else evalEU f1 k t1

evalEG :: (Eq a,Kripke k) => Ctl a -> k a -> [KripkeState] -> [KripkeState]
evalEG f k t = 
  let t1 = nub $ [s | s<-eval k f , not $ null $ suc k s `intersect` t] in
  if length t1 == length t then t else evalEG f k t1
  

-- |returns all states whose successors satisfy given formula
pred :: (Kripke k, Eq a) => k a -> Ctl a -> [KripkeState]
pred k f = nub $ concatMap (pre k) $ eval k f
