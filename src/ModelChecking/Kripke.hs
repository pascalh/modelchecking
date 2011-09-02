{-# LANGUAGE TypeSynonymInstances ,FlexibleInstances #-}
module ModelChecking.Kripke where
import qualified Data.Graph.Inductive as G 
import Data.Maybe (mapMaybe)
import Data.List ((\\))

-- | We use @Int@s to uniquely identify a state in a kripke structure.
type KripkeState = Int

-- |A interface for kripke structures. Errors are thrown if already existing
-- nodes are inserted.
-- Minimal definition: 'states','initStates','rel','labels','empty',
-- 'addState', 'addInitState', 'addRel' and 'addLabel'.
class Kripke k where
  -- |all states
  states :: k l -> [KripkeState] 
  -- |initial states
  initStates :: k l -> [Int] 
  -- |transition relation
  rel :: KripkeState -> KripkeState -> k l -> Bool 
  -- |state labeling function
  labels :: KripkeState -> k l -> [l] 

  -- building a kripke structure
  -- |a empty kripke structure
  empty :: k l 
  -- |add a new state
  addState :: KripkeState -> k l -> k l 
  -- |add a new state and mark is a initial
  addInitState :: KripkeState -> k l -> k l 
  -- | adds a relation between two already existing states
  addRel :: KripkeState -> KripkeState -> k l -> k l 
  -- | adds a label to a already existing state
  addLabel :: KripkeState -> l -> k l -> k l 

  -- |adds a new node with a given label
  addStateWithLabel :: KripkeState -> l -> k l -> k l
  addStateWithLabel s l = addLabel s l . addState s 
  
  -- |return all transitions
  rels :: k l -> [(KripkeState,KripkeState)]
  rels k = [(i,j)|i<-states k,j<-states k,rel i j k] 

  -- helper functions
  -- |returns whether given state is already in kripke structure
  nelem :: KripkeState -> k l -> Bool
  nelem s = elem s . states

  -- |returns a specified number of state which are not in kripke structure
  newNodes :: Int -> k l -> [Int]
  newNodes n k = 
    let m = if null $ states k then 0  else maximum $ states k 
    in take n [m+1,m+2..]

  -- |returns all predecessors of a given state
  pre :: k l -> KripkeState -> [KripkeState] 
  pre k s = [s'|s'<-states k, rel s' s k]

  -- |returns all successors of a given state
  suc :: k l -> KripkeState -> [KripkeState] 
  suc k s = [s'|s' <- states k,rel s s' k]

-- |a state in a kripke structure has a type and a set of labels
type KripkeLabel a = (NodeType,[a])

instance (Kripke k) => Show (k String)  where
  show k = 
    let lbls s= concatMap show $ labels s k
        sucs s= concatMap (\c->show c++" ") (suc k s)
    in concatMap (\s->show s++":"++lbls s++ "  -> "++sucs s++"\n")  $ states k

-- |we distinguish the following kinds of states
data NodeType 
  = Initial -- ^ see definition of kripke structures
  | Terminal -- ^ optional but useful for control flow graphs
  | Normal   -- ^ a normal node in kripke structure
  | Label    -- ^ a node which will only be processed by printer
  deriving (Show,Eq,Ord)


-- |a wrapper for graphs containing 'NodeType's
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
    | otherwise              = 
        if nelem u g then err "addRel" u else err "addRel" v

  addLabel s l g = case G.match s $ graph g of
    (Just (pp,n,(t,ls),ss),g') -> KripkeGr $ (pp,n,(t,l:ls),ss) G.& g'
    _                          -> errN s

  addStateWithLabel s l g 
    | nelem s g = err "addStateWithLabel" s
    | otherwise = KripkeGr $ G.insNode (s,(Normal,[l])) $ graph g
 
  pre (KripkeGr g) s = G.pre g s
  suc (KripkeGr g) s = G.suc g s
  rels (KripkeGr k) = G.edges k



