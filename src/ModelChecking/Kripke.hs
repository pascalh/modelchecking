module ModelChecking.Kripke where
import qualified Data.Graph.Inductive as G 
import Data.Maybe (mapMaybe)
import Data.List (nub,union)
import Data.Array (Array,indices,(!))

-- | We use @Int@s to uniquely identify a state in a kripke structure.
type KripkeState = Int

-- |A interface for kripke structures. Errors are thrown if already existing
-- nodes are inserted.
-- Minimal definition: 'states','initStates','rel','labels'
class Kripke k where
  -- |all states
  states :: k l -> [KripkeState] 
  -- |initial states
  initStates :: k l -> [Int] 
  -- |transition relation
  rel :: KripkeState -> KripkeState -> k l -> Bool 
  -- |state labeling function
  labels :: KripkeState -> k l -> [l] 

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

  -- |transitive closure of predecessor relation for a given state
  preT :: k l -> KripkeState -> [KripkeState]
  preT k s = nub $ pre k s `union` concatMap (preT k) (pre k s)

  -- |transitive closure of successor relation for a given state
  sucT :: k l -> KripkeState -> [KripkeState]
  sucT k s | suc k s == [s] = [s] 
           | otherwise      = 
      nub $ suc k s `union` (nub $ concatMap (nub . sucT k) (suc k s))

-- |This class offers an interface to mutable kripke structure, i.e.
-- their content after initial creation. Minimal definition:
-- 'empty', 'addState', 'addInitState', 'addRel', 'addLabel'
class Kripke k => KripkeDyn k where
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

instance KripkeDyn KripkeGr where
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
 
-- maybe statt error 
errN :: Show a => a -> b
errN s = error $ "State "++show s++" is not in kripke structure" 

err :: Show a => String -> a -> b
err f s = error $ f++ "|State "++show s++" is already in kripke structure" 


-- |a state in a kripke structure has a type and a set of labels
type KripkeLabel a = (NodeType,[a])

-- |we distinguish the following kinds of states
data NodeType 
  = Initial -- ^ see definition of kripke structures
  | Terminal -- ^ optional but useful for control flow graphs
  | Normal   -- ^ a normal node in kripke structure
  | Label    -- ^ a node which will only be processed by printer
  deriving (Show,Eq,Ord)

-- |a adjacency list to represent static kripke structures
data AdjList a = AdjList 
  { ps :: Array KripkeState [KripkeState] -- ^ predecessor relation
  , ss :: Array KripkeState [KripkeState] -- ^ succesor relation
  , lbls :: Array KripkeState a -- ^ labeling function
  , initialStates :: [KripkeState] -- ^ initial states
  } deriving Show

instance Kripke AdjList where
  states (AdjList adj _ _ _) = indices adj
  initStates = initialStates
  rel i j (AdjList _ ss _ _) = j `elem` (ss ! i)
  labels i (AdjList _ _ l _) = return $ l ! i
  suc (AdjList _ ss _ _) s = ss ! s
  pre (AdjList ps _ _ _) s = ps ! s

-- |a wrapper for graphs containing 'NodeType's
newtype KripkeGr a = KripkeGr {graph :: G.Gr (KripkeLabel a) ()}



instance Kripke KripkeGr where
  states (KripkeGr g) = G.nodes g

  initStates (KripkeGr g) = mapMaybe (f . flip G.match g) (G.nodes g) where
    f (Just (_,n,(Initial,_),_),_) = Just n
    f _                            = Nothing

  rel u v = elem (u,v) . G.edges . graph

  labels s (KripkeGr g) = case G.match s g of
    (Just (_,_,(_,ls),_),_) -> ls
    _                       -> []
  pre (KripkeGr g) s = G.pre g s
  suc (KripkeGr g) s = G.suc g s
  rels (KripkeGr k) = G.edges k

  newNodes n (KripkeGr k) = G.newNodes n k


