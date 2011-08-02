{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies#-}

module Cfg where
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile
import Data.Graph.Inductive
import Data.Graph.Inductive.Graphviz

import Control.Monad.State

import Data.Tree
import Data.Data
import Data.Generics.Aliases

-- a control flow graph for abstract syntax tree ast containing
-- node labels of type nodelabel
class ControlFlow ast nodelabel where
  toControlFlowGraph :: ast -> Gr (CfgNode nodelabel) ()

data Varops = Decl String | Read String | Write String deriving (Show)

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

-- * define a datatype which contains the transformation functions 

data CfgNode a = Initial
             | Terminal 
             | Value a -- ^ a node for values which matter
             | Tag String -- ^ just a description of a node (won't be processed later on)
             deriving Show 

{-
data family NN a c 
data instance NN Program cfgnode = WhileCfgNode1
  { program122 :: Program -> (CfgNode cfgnode)
  , stmts1   :: Stmts   -> (CfgNode cfgnode)
  , stmt1    :: Stmt    -> (CfgNode cfgnode)
  , bexp1    :: BExp    -> (CfgNode cfgnode)
  }
-}

-- |data type for defining cfg-node-label-creations
data WhileCfgNode cfgnode 
  = WhileCfgNode 
  { program :: Program -> CfgNode cfgnode
  , stmts   :: Stmts   -> CfgNode cfgnode
  , stmt    :: Stmt    -> CfgNode cfgnode
  , bexp    :: BExp    -> CfgNode cfgnode
  }

vars :: WhileCfgNode Varops
vars = WhileCfgNode toCfgNode toCfgNode toCfgNode toCfgNode 

class TonNode a b where
  toCfgNode :: a -> CfgNode b

class Foo a b where
  getCfg :: WhileCfgNode b -> a -> Gr (CfgNode b) ()
  getCfg v p = toCfg v undefined p undefined undefined

  toCfg :: WhileCfgNode b -> Int -> a -> Int -> Gr (CfgNode b) () -> Gr (CfgNode b) ()

instance Foo Program b where
  toCfg v _ (Program ss) _ _ =   
    let g     = empty 
        [i,t] = newNodes 2 g
        h     = insNode (t,Terminal) $ insNode (i,Initial) g
    in toCfg v i ss t h


instance Foo Stmts b where
  toCfg v i (StmtsE s  ) t g = toCfg v i s t g
  toCfg v i (Stmts s ss) t g = 
    let b = head $ newNodes 1 g in 
      toCfg v b ss t $ toCfg v i s b $ insNode (b,Tag []) g

instance Foo Stmt b where
  toCfg v i s t g = 
    case s of
      (SIf _ _)    -> insCond v i t s g
      (SWhile _ _) -> insCond v i t s g
      _            -> insBetween i t (stmt v $ s) g


-- cfgnodes: a -> Varops
instance TonNode Program Varops where
  toCfgNode _ = Tag []

instance TonNode Stmt Varops where
  toCfgNode (SDecl (Ident i))     = Value $ Decl i
  toCfgNode (SAssign (Ident i) _) = Value $ Write i
  toCfgNode (SWhile _ _)          = Tag "While"
  toCfgNode (SIf _ _)             = Tag "If"

instance TonNode Stmts Varops where
  toCfgNode _ = Tag []

instance TonNode BExp Varops where
  toCfgNode _ = Tag []
  


insCond :: WhileCfgNode b -> Node -> Node -> Stmt 
        -> Gr (CfgNode b) () -> Gr (CfgNode b) ()
insCond v i t s@(SWhile _ ss) g =     
  let [x,y] = newNodes 2 g
      h = insEdge (y,x,()) 
        $ insEdge (x,y,()) 
        $ insEdge (i,x,()) 
        $ insEdge (y,t,()) 
        $ insNode (x,stmt v $ s) 
        $ insNode (y,stmt v $ s) g
  in toCfg v x ss y h

insCond v i t s@(SIf _ ss) g =     
  let [x,y] = newNodes 2 g
      h = insEdge (x,y,()) 
        $ insEdge (i,x,()) 
        $ insEdge (y,t,()) 
        $ insNode (x,stmt v $ s) 
        $ insNode (y,stmt v $ s) g
  in toCfg v x ss y h


-- simple inserting nodes
insBetween :: Node -> Node -> CfgNode a 
           -> Gr (CfgNode a) () -> Gr (CfgNode a) ()
insBetween i t v g = 
  let n = head $ newNodes 1 g in
  insEdge (i,n,()) $ insEdge (n,t,()) $ insNode (n,v) g

-- * pruning the cfg: doesnt work properly 
prune :: Gr (CfgNode a) () -> Gr (CfgNode a) () 
prune g 
  | isEmpty g = g
  | otherwise = let (c@(preds,_,_,succs),g') = matchAny g in
      case (preds,succs) of
        ([(_,p)],[(_,s)]) -> prune $ insEdge (p,s,()) g'
        _                 -> c & prune g'

-- * gehackt und so -> klappt nicht

data CfgState a = 
  CfgState { graph :: Gr (CfgNode a) () 
           , pre :: Int 
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

-- * testing values

test :: IO ()
test = mapM_ 
  (\x -> let cfg = (getCfg::WhileCfgNode Varops -> Program -> Gr (CfgNode Varops) ())vars x in 
    putStrLn "----" >> print ( pretty x) >> print cfg) 
  [program6,program1,program2,program3,program4,program5]

program6 :: Program
program6 = read "prog var i ; i ::= true ; var h ; i::= false ;  end" 

program1 :: Program
program1 = read $ 
  "prog var g ; var i ; "++
   "if true then  var h ; if false then h ::= true ; fi var j; fi "++
   "i::= false ; h ::= true  ; g ::= true ;  end" 

program2 :: Program
program2 = read $ 
  "prog var g ; while true do var y ; var z; y ::= false ; end var f; end"


program3 :: Program
program3 = read $ 
  "prog var g ; while true do var y ; y ::= false ;  var u; end end"

program4 :: Program
program4 = read "prog var i ; i ::= true ; var h ; if false then i::= false ; var g ; fi  end"  

program5 :: Program
program5 = read 
  "prog var i ; i ::= true ; var h ; if false then i::= false ; var g ; fi var f; end"  


-- * should be "global"

instance Read Program where
  readsPrec _ s = 
    case pProgram $ myLexer s of
      Ok ast -> [(ast,[])]
      Bad _  -> []

class Pretty a where
  pretty :: a -> String

instance Pretty Program where
  pretty (Program ss) = "prog "++pretty ss++" end"

instance Pretty Stmts where
  pretty (Stmts s ss) = pretty s ++ " "++ pretty ss
  pretty (StmtsE s)   = pretty s

instance Pretty Stmt where
  pretty (SWhile b s) = "while "++pretty b++" do "++pretty s++" end "
  pretty (SIf b s) = "if "++pretty b++" then "++pretty s++" fi "
  pretty (SDecl (Ident s)) = "var "++s++" ; "
  pretty (SAssign (Ident s) b) = s++" ::= " ++pretty b++" ; "

instance Pretty BExp where
  pretty BTrue = "true"
  pretty BFalse = "false"
  pretty (BConj b1 b2) = "("++pretty b1++" && "++pretty b2++")"
  pretty (BDisj b1 b2) = "("++pretty b1++" || "++pretty b2++")"
  pretty (BNeg b) = "not("++pretty b++")"

