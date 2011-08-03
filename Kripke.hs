{-# LANGUAGE TypeFamilies #-}
module Kripke where
import Data.Graph.Inductive
import Data.Maybe (mapMaybe)

-- |we distingiush between four kinds of nodes in a kripke structure
data KripkeNode a
  = Initial -- ^ see definition of kripke structures
  | Terminal -- ^ optional but useful for control flow graphs
  | Value {value :: a } -- ^ values are processed by our algorithms
  | Tag {tag :: String } -- ^ tags are only used for output
  deriving Show 

-- |an interface for kripke structures
class Kripke k where
  type State
  states :: k l -> [State] -- ^ all states
  initStates :: k l -> [State] -- ^ initial states 
  rel :: State -> State -> k l -> Bool -- ^ transition relation
  labels :: State -> k l -> [l] -- ^ state labeling function

-- |a wrapper for graphs containing cfgnodes
newtype KripkeGr a = KripkeGr {graph :: Gr (KripkeNode a) ()} deriving Show

instance Kripke KripkeGr where
  type State = Node

  states (KripkeGr g) = Data.Graph.Inductive.nodes g

  initStates (KripkeGr g) = mapMaybe (f . flip match g) (nodes g) where
    f (Just (_,n,Initial,_),_) = Just n
    f _                      = Nothing

  rel u v (KripkeGr g) = elem (u,v) $ edges g

  labels s (KripkeGr g) = case match s g of
    (Just (_,_,Value l,_),_) -> return l
    _                        -> []


