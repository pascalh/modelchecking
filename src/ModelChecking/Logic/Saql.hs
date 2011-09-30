{-|
The simple ast query logic is a logic to query kripke structures
-}
module ModelChecking.Logic.Saql (Saql(..)) where
import ModelChecking.Kripke
import qualified ModelChecking.Logic as L
import Data.List ((\\),intersect,nub,union)

data Saql a 
           = TT 
           | FF
           | AP a
           | Neg (Saql a)
           | Disj (Saql a) (Saql a) 
           | Conj (Saql a) (Saql a)
           | X (Saql a) -- ^formula holds at a direct successor
           | F (Saql a) -- ^formula holds at any succeding state
           | B (Saql a) -- ^formula holds at a direct predecessor
           | P (Saql a) -- ^formula holds at any predeceding state

instance L.Logic Saql where
  eval k l = eval k l 

br s= "("++s++")"

instance Show a => Show (Saql a) where
  show TT           = "True"
  show FF           = "False"
  show (AP a)       = show a
  show (Neg a)      = "¬"++br (show a)
  show (Disj a1 a2) = (br $ show a1)++" || "++(br $ show a2)
  show (Conj a1 a2) = (br $ show a1)++" && "++(br $ show a2)
  show (X a)        = "X "++show a
  show (F a)        = "F "++show a
  show (P a)        = "P "++show a
  show (B a)        = "B "++show a

-- |returns whether formula holds at a specific state
holds :: (Kripke k, Eq a) => KripkeState -> k a -> Saql a -> Bool
holds s k f= s `elem` eval k f

-- |returns all states for which given formula holds
-- (using the labeling algorithm)
eval :: (Kripke k ,Eq a) => k a -> Saql a -> [KripkeState]
eval k TT           = states k
eval k FF           = []
eval k (AP a)       = [s| s <- states k, a `elem` labels s k]
eval k (Neg f)      = states k \\ eval k f
eval k (Conj f1 f2) = eval k f1 `intersect` eval k f2
eval k (Disj f1 f2) = nub $ eval k f1 `union` eval k f2
eval k (X f)        = nub $ concatMap (pre k)  $ eval k f
eval k (P f)        = nub $ concatMap (sucT k) $ eval k f 
eval k (B f)        = nub $ concatMap (suc k)  $ eval k f
eval k (F f)        = nub $ concatMap (preT k) $ eval k f 

