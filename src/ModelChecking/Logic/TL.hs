{-|
data types for basic temporal logic
-}
module ModelChecking.Logic.TL (TL(..)) where
import ModelChecking.Kripke
import qualified ModelChecking.Logic as L
import Data.List ((\\),intersect,nub,union)

data TL a 
           = TT 
           | FF
           | AP a
           | Neg (TL a)
           | Disj (TL a) (TL a) 
           | Conj (TL a) (TL a)
           | EX (TL a) -- ^formula holds at a direct successor
           | EF (TL a) -- ^formula holds at any succeding state
           | EY (TL a) -- ^formula holds at a direct predecessor
           | EP (TL a) -- ^formula holds at any predeceding state

instance L.Logic TL where
  eval k l = eval k l 

br :: String -> String
br s= "("++s++")"

instance Show a => Show (TL a) where
  show TT           = "True"
  show FF           = "False"
  show (AP a)       = show a
  show (Neg a)      = "¬"++br (show a)
  show (Disj a1 a2) = (br $ show a1)++" || "++(br $ show a2)
  show (Conj a1 a2) = (br $ show a1)++" && "++(br $ show a2)
  show (EX a)        = "EX "++show a
  show (EF a)        = "EF "++show a
  show (EP a)        = "EP "++show a
  show (EY a)        = "EY "++show a

-- |returns all states satisfying a given formula 
eval :: (Kripke k ,Eq a) => k a -> TL a -> [KripkeState]
eval k TT           = states k
eval _ FF           = []
eval k (AP a)       = [s| s <- states k, a `elem` labels s k]
eval k (Neg f)      = states k \\ eval k f
eval k (Conj f1 f2) = eval k f1 `intersect` eval k f2
eval k (Disj f1 f2) = nub $ eval k f1 `union` eval k f2
eval k (EX f)        = nub $ concatMap (pre k)  $ eval k f
eval k (EP f)        = nub $ concatMap (sucT k) $ eval k f 
eval k (EY f)        = nub $ concatMap (suc k)  $ eval k f
eval k (EF f)        = nub $ concatMap (preT k) $ eval k f 

