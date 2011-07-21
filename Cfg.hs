{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts #-}

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

-- * using state monad and adding explicit starting and ending states

data CfgNode a = Initial
             | Terminal 
             | Value a -- ^ a node for values which matter
             | Tag String -- ^ just a description of a node (won't be processed later on)
             deriving Show 


class TonNode a b where
  toCfgNode :: a -> CfgNode b

class Foo a b where
  getCfg :: (TonNode Stmt b, TonNode Stmts b) => a -> Gr (CfgNode b) ()
  getCfg p = toCfg undefined p undefined undefined

  toCfg :: (TonNode Stmts b,TonNode Stmt b) => Int -> a -> Int -> Gr (CfgNode b) () -> Gr (CfgNode b) ()

instance Foo Program b where
  toCfg _ (Program ss) _ _ =   
    let g     = empty 
        [i,t] = newNodes 2 g
        h     = insNode (t,Terminal) $ insNode (i,Initial) g
    in toCfg i ss t h

instance TonNode Program Varops where
  toCfgNode _ = Tag []

instance Foo Stmts b where
  toCfg i (StmtsE s  ) t g = toCfg i s t g
  toCfg i (Stmts s ss) t g = 
    let b = head $ newNodes 1 g in 
      toCfg b ss t $ toCfg i s b $ insNode (b,Tag []) g

instance Foo Stmt b where
  toCfg i s t g = 
    case s of
      (SIf _ _)    -> insCond i t s g
      (SWhile _ _) -> insCond i t s g
      _            -> insBetween i t (toCfgNode s) g

instance TonNode Stmt Varops where
  toCfgNode (SDecl (Ident i))     = Value $ Decl i
  toCfgNode (SAssign (Ident i) _) = Value $ Write i
  toCfgNode (SWhile _ _)          = Tag "While"
  toCfgNode (SIf _ _)             = Tag "If"

instance TonNode Stmts Varops where
  toCfgNode _ = Tag []
  

insCond :: (TonNode Stmt b,TonNode Stmts b) 
        => Node -> Node -> Stmt -> Gr (CfgNode b) () -> Gr (CfgNode b) ()
insCond i t s@(SWhile _ ss) g =     
  let [x,y] = newNodes 2 g
      h = insEdge (y,x,()) 
        $ insEdge (x,y,()) 
        $ insEdge (i,x,()) 
        $ insEdge (y,t,()) 
        $ insNode (x,toCfgNode s) 
        $ insNode (y,toCfgNode s) g
  in toCfg x ss y h

insCond i t s@(SIf _ ss) g =     
  let [x,y] = newNodes 2 g
      h = insEdge (x,y,()) 
        $ insEdge (i,x,()) 
        $ insEdge (y,t,()) 
        $ insNode (x,toCfgNode s) 
        $ insNode (y,toCfgNode s) g
  in toCfg x ss y h


-- simple inserting nodes
insBetween :: Node -> Node -> CfgNode a -> Gr (CfgNode a) () -> Gr (CfgNode a) ()
insBetween i t v g = 
  let n = head $ newNodes 1 g in
  insEdge (i,n,()) $ insEdge (n,t,()) $ insNode (n,v) g




-- * creating simple graphs

-- |erzeugt graphen aus baum
treeToGraph :: Tree a -> Gr a () 
treeToGraph t = let n = head $ newNodes 1 (empty::Gr a ()) in
  toCG n t $ insNode (n,rootLabel t) empty 

toCG :: Int -> Tree a -> Gr a () -> Gr a ()
toCG j (Node _ cs) g = 
  foldr (\(c,i) -> toCG i c . insEdge (j,i,()) . insNode (i,rootLabel c)) g $
    zip cs $ newNodes (length cs) g 

blah = treeToGraph $ 
  Node "root" [Node "inner1" [Node "leaf1" []]
              ,Node "inner2" [Node "leaf2" []]]

dataToTree :: Data a => a -> Tree String 
dataToTree t = Node (showConstr (toConstr t)) (gmapQ dataToTree t) 

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
  (\x -> let cfg = (toControlFlowGraph::Program -> Gr (CfgNode String) ())x in 
    putStrLn "----" >> print ( pretty x) >> print cfg) 
  [program,program1,program2,program3,program4,program5]

program :: Program
program = read "prog var i ; i ::= true ; var h ; i::= false ;  end" 

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

