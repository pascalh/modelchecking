{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleContexts #-}
module Depricated where
import Cfg
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile
import Data.Graph.Inductive
import Data.Tree
import Data.Data
import Data.Generics.Aliases
import Control.Monad.State

-- a control flow graph for abstract syntax tree ast containing
-- node labels of type nodelabel
class ControlFlow ast nodelabel where
  toControlFlowGraph :: ast -> Gr (CfgNode nodelabel) ()

instance ControlFlow Program String where
  toControlFlowGraph (Program ss) = 
    let g     = empty 
        [i,t] = newNodes 2 g
        (p1,h,p2) = stmtsToCfg ss $ insNode (t,Terminal) $ insNode (i,Initial) g
    in insEdge (i,p1,()) $ insEdge (p2,t,()) h


-- |creates usual cfg-structre for a conditional language element.
-- if given conditional is a loop, a backwards edge has to be inserted
-- within guarded stmt
conditionalToCfg 
  :: Stmt -- ^ stmt before conditional
  -> Stmts -- ^ stmts which are guarded
  -> Stmts -- ^ stmts after conditional
  -> Bool -- ^ is the guarded expr a loop?
  -> Gr (CfgNode String) ()
  -> (Node,Gr (CfgNode String) (),Node)
conditionalToCfg pre ss post isLoop gr = let 
      (npre ,gr1,_)      = stmtToCfgOut pre gr -- s1 is a single stmt -> (n1pre ==n1post)
      (nss  ,gr2,nss')   = stmtsToCfg ss gr1 
      (npost,gr3,npost') = stmtsToCfg post gr2 
      f = if isLoop then insEdge (nss',nss,()) else id
      gr4 = insEdge (npre ,nss  ,()) 
          $ insEdge (nss' ,npost,())
          $ insEdge (npre ,npost,()) gr3 in (npre,f gr4,npost')
            

stmtsToCfg :: Stmts -> Gr (CfgNode String) () -> (Node,Gr (CfgNode String) (),Node)
stmtsToCfg (StmtsE s) gr = stmtToCfgOut s gr 
stmtsToCfg (Stmts s1 (Stmts (SIf _ s2) ss)) gr = 
  conditionalToCfg s1 s2 ss False gr

stmtsToCfg (Stmts s1 (Stmts (SWhile _ s2) ss)) gr = 
  conditionalToCfg s1 s2 ss True gr

stmtsToCfg (Stmts s ss) gr = 
  let (n1,gr1,n1') = stmtToCfgOut s gr
      (n2,gr2,n2') = stmtsToCfg ss gr1 in
  (n1,insEdge (n1',n2,()) gr2,n2')
{-
stmtToCfg :: Stmt -> Gr Varops () -> (Node,Gr Varops (),Node)
stmtToCfg s gr = let n = head $ newNodes 1 gr in case s of
  (SDecl (Ident v))     -> (n,insNode (n,Decl v ) gr,n)
  (SAssign (Ident v) _) -> (n,insNode (n,Write v) gr,n)
  (SIf _ ss)            -> stmtsToCfg ss gr
  (SWhile _ ss)         -> 
    let (a,gr1,b) = stmtsToCfg ss gr in (a,insEdge (b,a,()) gr1,b)
-}
stmtToCfgOut :: Stmt -> Gr (CfgNode String) () -> (Node,Gr (CfgNode String) (),Node)
stmtToCfgOut s gr = let n = head $ newNodes 1 gr in case s of
  (SDecl (Ident v))     -> (n,insNode (n,Value $ pretty s) gr,n)
  (SAssign (Ident v) _) -> (n,insNode (n,Value $ pretty s) gr,n)
  (SIf _ ss)            -> stmtsToCfg ss gr
  (SWhile _ ss)         -> 
    let (a,gr1,b) = stmtsToCfg ss gr in (a,insEdge (b,a,()) gr1,b)

-- * gehackt und so -> klappt nicht

data CfgState a = 
  CfgState { graph :: Gr (CfgNode a) () 
           , pre1 :: Int 
           , post :: Int } 
  deriving Show 
-- |klappt nicht!!! -> zipper?
constructorGraph :: Data a => a -> Gr (CfgNode String) ()
constructorGraph = graph . snd . flip runState emptyState . asttree

-- |
asttree :: Data a => a -> State (CfgState String) a 
asttree t = do 
  (CfgState g p1 p2) <- get
  let n = head $ newNodes 1 g
     -- cs = zip (tail ns) $ gmapQ (\c-> Value $ showConstr $ toConstr c) t  
  graphMap $ \h -> insEdge (p1,n,()) $ insNode (n,Value $ showConstr $ toConstr t) h   
  modify (\(CfgState g _ succ) -> CfgState g n succ) 
  gmapM asttree t 

-- crazy helper
graphMap
  :: MonadState (CfgState a) m 
  => (Gr (CfgNode a) () -> Gr (CfgNode a) ()) -> m ()
graphMap f = do
  (CfgState g pr po) <- get
  put $ CfgState (f g) pr po

emptyState :: CfgState a
emptyState = CfgState g i t where
   g = insNode (i,Initial) $ insNode (t,Terminal) empty
   [i,t] = newNodes 2 (empty::Gr (CfgNode a) ())

-- * tryyy

{-
data family NN a c 
data instance NN Program cfgnode = WhileCfgNode1
  { program122 :: Program -> (CfgNode cfgnode)
  , stmts1   :: Stmts   -> (CfgNode cfgnode)
  , stmt1    :: Stmt    -> (CfgNode cfgnode)
  , bexp1    :: BExp    -> (CfgNode cfgnode)
  }
-}
