{-# LANGUAGE TypeFamilies , MultiParamTypeClasses , TypeSynonymInstances #-}
module Kripke where
import Data.Graph.Inductive hiding (suc,pre)
import Data.Maybe (mapMaybe)

-- |we distingiush between four kinds of nodes in a kripke structure
data KripkeNode a
  = Initial -- ^ see definition of kripke structures
  | Terminal -- ^ optional but useful for control flow graphs
  | Value {value :: a } -- ^ values are processed by our algorithms
  | Tag {tag :: String } -- ^ tags are only used for output
  deriving (Eq,Ord)

instance Show a => Show (KripkeNode a) where
  show Initial = "Initial"
  show Terminal= "Terminal"
  show (Value v) = show v
  show (Tag t)   = "Tag "++show t

-- |an interface for kripke structures
class Kripke k s where
  states :: k l -> [s] -- ^ all states
  initStates :: k l -> [s] -- ^ initial states 
  rel :: s -> s -> k l -> Bool -- ^ transition relation
  labels :: s -> k l -> [l] -- ^ state labeling function

  pre :: k l -> s -> [s] -- ^finds predecessor nodes
  pre k s = [s'|s'<-states k, rel s' s k]

  suc :: k l -> s -> [s] -- ^ finds successor nodes
  suc k s = [s'|s' <- states k,rel s s' k]

-- |a wrapper for graphs containing cfgnodes
newtype KripkeGr a = KripkeGr {graph :: Gr (KripkeNode a) ()} deriving Show

instance Kripke KripkeGr Node where
  states (KripkeGr g) = Data.Graph.Inductive.nodes g

  initStates (KripkeGr g) = mapMaybe (f . flip match g) (nodes g) where
    f (Just (_,n,Initial,_),_) = Just n
    f _                      = Nothing

  rel u v (KripkeGr g) = elem (u,v) $ edges g

  labels s (KripkeGr g) = case match s g of
    (Just (_,_,Value l,_),_) -> return l
    _                        -> []


