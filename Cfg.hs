{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies #-}

module Cfg where
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile
import Data.Graph.Inductive

import WhileMisc
import Kripke
import GraphUtil
import DataToGraph
import Control.Arrow (first)
import Data.Maybe (fromJust)

data Varops = Decl String | Read String | Write String deriving (Show)

-- * define a datatype which contains the transformation functions 

-- |data type for defining cfg-node-label-creations
data WhileKripkeNode k 
  = WhileKripkeNode 
  { program :: Program -> KripkeNode k
  , stmts   :: Stmts   -> KripkeNode k
  , stmt    :: Stmt    -> KripkeNode k
  , bexp    :: BExp    -> KripkeNode k
  }

vars :: WhileKripkeNode Varops
vars = WhileKripkeNode toKripkeNode toKripkeNode toKripkeNode toKripkeNode 

class TonNode a b where
  toKripkeNode :: a -> KripkeNode b

class Foo a b where
  getCfg :: WhileKripkeNode b -> a -> Gr (KripkeNode b) ()
  getCfg v p = toCfg v undefined p undefined undefined

  toCfg :: WhileKripkeNode b -> Int -> a -> Int -> Gr (KripkeNode b) () -> Gr (KripkeNode b) ()

instance Foo Program b where
  toCfg v _ (Program ss) _ _ =   
    let g     = empty 
        [i,t] = newNodes 2 g
        h     = insNodes [(t,Terminal),(i,Initial)] g
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


-- ks: a -> Varops
instance TonNode Program Varops where
  toKripkeNode _ = Tag []

instance TonNode Stmt Varops where
  toKripkeNode (SDecl (Ident i))     = Value $ Decl i
  toKripkeNode (SAssign (Ident i) _) = Value $ Write i
  toKripkeNode (SWhile _ _)          = Tag "While"
  toKripkeNode (SIf _ _)             = Tag "If"

instance TonNode Stmts Varops where
  toKripkeNode _ = Tag []

instance TonNode BExp Varops where
  toKripkeNode _ = Tag []
  


insCond :: WhileKripkeNode b -> Node -> Node -> Stmt 
        -> Gr (KripkeNode b) () -> Gr (KripkeNode b) ()
insCond v i t s@(SWhile _ ss) g =     
  let [x,y] = newNodes 2 g
      h = insEdges [(y,x,()),(x,y,()),(i,x,()),(y,t,())]  
        $ insNodes [(x,stmt v s),(y,stmt v s)] g 
  in toCfg v x ss y h

insCond v i t s@(SIf _ ss) g =     
  let [x,y] = newNodes 2 g
      h = insEdges [(x,y,()),(i,x,()),(y,t,())]  
        $ insNodes [(x,stmt v s),(y,stmt v s)] g 
  in toCfg v x ss y h


-- simple inserting nodes
insBetween :: Node -> Node -> KripkeNode a 
           -> Gr (KripkeNode a) () -> Gr (KripkeNode a) ()
insBetween i t v g = 
  let n = head $ newNodes 1 g in
  insEdge (i,n,()) $ insEdge (n,t,()) $ insNode (n,v) g

-- * pruning the cfg: doesnt work properly 

-- |removes all empty tags from given graph
prune :: DynGraph g => g (KripkeNode a) () -> g (KripkeNode a) ()
prune g = prune' (nodes g) g where
  prune' []     g = g
  prune' (n:ns) g = let ((_,_,l,_),_) = first fromJust $ match n g in 
    case l of
      Tag "" ->  prune' ns (removeNode n g)
      _     ->  prune' ns g
  
-- * testing values

test :: IO ()
test = mapM_ 
  (\x -> let cfg = prune $ (getCfg::WhileKripkeNode Varops -> Program -> Gr (KripkeNode Varops) ())vars x in 
    putStrLn "----" >> print ( pretty x) >> print cfg) 
    programs 

test2 :: IO ()
test2 = mapM_ (\p -> putStrLn "----" >> print (pretty p) >> print (dataToKripkeGraph p)) programs

programs =[program6,program1,program2,program3,program4,program5] 

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

