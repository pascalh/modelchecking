{-# LANGUAGE TypeFamilies , MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances #-}
module Kripke where
import qualified Data.Graph.Inductive as G 
import Data.Maybe (mapMaybe)
import Control.Applicative
import Data.List ((\\))

type KripkeState = Int

-- |an interface for kripke structures. We use @Int@s to uniquely identify
-- a state in a kripke structure
class Kripke k where
  states :: k l -> [KripkeState] -- ^ all states
  initStates :: k l -> [Int] -- ^ initial states 
  rel :: KripkeState -> KripkeState -> k l -> Bool -- ^ transition relation
  labels :: KripkeState -> k l -> [l] -- ^ state labeling function

  -- building a kripke structure
  empty :: k l
  addState :: KripkeState -> k l -> k l
  addInitState :: KripkeState -> k l -> k l
  addRel :: KripkeState -> KripkeState -> k l -> k l
  addLabel :: KripkeState -> l -> k l -> k l

  addStateWithLabel :: KripkeState -> l -> k l -> k l
  addStateWithLabel s l = addLabel s l . addState s 

  -- helper functions
  nelem :: KripkeState -> k l -> Bool
  nelem s = elem s . states

  newNodes :: Int -> k l -> [Int]
  newNodes n k = let m = maximum $ states k in take n [m+1,m+2..]


  pre :: k l -> KripkeState -> [KripkeState] -- ^finds predecessor nodes
  pre k s = [s'|s'<-states k, rel s' s k]

  suc :: k l -> KripkeState -> [KripkeState] -- ^ finds successor nodes
  suc k s = [s'|s' <- states k,rel s s' k]

  -- |returns all nodes without a successor
  leafs :: k l -> [KripkeState]
  leafs k = concatMap (\n -> if null $ suc k n then return n else []) $ states k 



-- * inductive graphs as kripke structures

-- |a state in a kripke structure has a type and a set of labels
type KripkeLabel a = (NodeType,[a])

instance (Kripke k) => Show (k String)  where
  show k = 
    concatMap 
      (\s->show s++":"++(concatMap show $ labels s k)++ "  -> "++concatMap (\c->show c++" ") (suc k s) ++"\n") $ 
      states k

-- |we distinguish three kinds of states
data NodeType 
  = Initial -- ^ see definition of kripke structures
  | Terminal -- ^ optional but useful for control flow graphs
  | Normal   -- ^ a normal node in kripke structure
  | Label    -- ^ a node which will only be processed by printer
  deriving (Show,Eq,Ord)


-- |a wrapper for graphs containing cfgnodes
newtype KripkeGr a = KripkeGr {graph :: G.Gr (KripkeLabel a) ()}

err f s = error $ f++ "|State "++show s++" is already in kripke structure" 
errN s = error $ "State "++show s++" is not in kripke structure" 

instance Kripke KripkeGr where
  states (KripkeGr g) = G.nodes g

  initStates (KripkeGr g) = mapMaybe (f . flip G.match g) (G.nodes g) where
    f (Just (_,n,(Initial,_),_),_) = Just n
    f _                            = Nothing

  rel u v = elem (u,v) . G.edges . graph

  labels s (KripkeGr g) = case G.match s g of
    (Just (_,_,(_,ls),_),_) -> ls
    _                       -> []

  empty = KripkeGr G.empty

  addState s g
    | nelem s g = err "addState" s
    | otherwise = KripkeGr $ G.insNode (s,(Normal,[])) $ graph g

  addInitState s g 
    | nelem s g = err "addInitState" s
    | otherwise = KripkeGr $ G.insNode (s,(Initial,[])) $ graph g

  addRel u v g
    | nelem u g && nelem v g = KripkeGr $ G.insEdge (u,v,()) $ graph g
    | otherwise              = if nelem u g then err "addRel" u else err "addRel" v

  addLabel s l g = case G.match s $ graph g of
    (Just (pp,n,(t,ls),ss),g') -> KripkeGr $ (pp,n,(t,l:ls),ss) G.& g'
    _                          -> errN s

  addStateWithLabel s l g 
    | nelem s g = err "addStateWithLabel" s
    | otherwise = KripkeGr $ G.insNode (s,(Normal,[l])) $ graph g


