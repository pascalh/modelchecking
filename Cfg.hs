{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies , ScopedTypeVariables #-}

module Cfg where
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile
import qualified Data.Graph.Inductive as G

import Test.QuickCheck
import WhileMisc
import Kripke
import CTL
import GraphUtil
import DataToGraph
import Control.Arrow (first)
import Control.Monad (forM_)
import Data.Maybe (fromJust)

data Varops = Decl String | Read String | Write String | VLabel String 

instance Show Varops where
  show (Decl s) = s
  show (Read s) = s
  show (Write s) = s
  show (VLabel s) = s

-- * define a datatype which contains the transformation functions 

-- |data type for defining cfg-node-label-creations
data WhileKripkeLabel k 
  = WhileKripkeLabel 
  { program :: Program -> KripkeLabel k
  , stmts   :: Stmts   -> KripkeLabel k
  , stmt    :: Stmt    -> KripkeLabel k
  , bexp    :: BExp    -> KripkeLabel k
  }
{-
vars :: WhileKripkeLabel Varops
vars = WhileKripkeLabel toKripkeLabel toKripkeLabel toKripkeLabel toKripkeLabel 

class TonNode a b where
  toKripkeLabel :: a -> KripkeLabel b

class Foo a b where
  getCfg :: WhileKripkeLabel b -> a -> G.Gr (KripkeLabel b) ()
  getCfg v p = toCfg v undefined p undefined undefined

  toCfg :: WhileKripkeLabel b -> Int -> a -> Int -> G.Gr (KripkeLabel b) () -> G.Gr (KripkeLabel b) ()

instance Foo Program b where
  toCfg v _ (Program ss) _ _ =   
    let g     = G.empty 
        [i,t] = G.newNodes 2 g
        h     = G.insNodes [(t,Terminal),(i,Initial)] g
    in toCfg v i ss t h


instance Foo Stmts b where
  toCfg v i (StmtsE s  ) t g = toCfg v i s t g
  toCfg v i (Stmts s ss) t g = 
    let b = head $ G.newNodes 1 g in 
      toCfg v b ss t $ toCfg v i s b $ G.insNode (b,toKripkeLabel $ Stmts s ss ) g

instance Foo Stmt b where
  toCfg v i s t g = 
    case s of
      (SIf _ _)    -> insCond v i t s g
      (SWhile _ _) -> insCond v i t s g
      _            -> insBetween i t (stmt v $ s) g


-- ks: a -> Varops
instance TonNode Program Varops where
  toKripkeLabel _ = (Label,[VLabel []])

instance TonNode Stmt Varops where
  toKripkeLabel (SDecl (Ident i))     = (Normal,[Decl i])
  toKripkeLabel (SAssign (Ident i) _) = (Normal,[Write i])
  toKripkeLabel (SWhile _ _)          = (Label, [VLabel "While"])
  toKripkeLabel (SIf _ _)             = (Label, [VLabel "If"])

instance TonNode Stmts Varops where
  toKripkeLabel _ = (Label,[VLabel []])

instance TonNode BExp Varops where
  toKripkeLabel _ = (Label,[VLabel []])
  


insCond :: WhileKripkeLabel b -> G.Node -> G.Node -> Stmt 
        -> G.Gr (KripkeLabel b) () -> G.Gr (KripkeLabel b) ()
insCond v i t s@(SWhile _ ss) g =     
  let [x,y] = G.newNodes 2 g
      h = G.insEdges [(y,x,()),(x,y,()),(i,x,()),(y,t,())]  
        $ G.insNodes [(x,stmt v s),(y,stmt v s)] g 
  in toCfg v x ss y h

insCond v i t s@(SIf _ ss) g =     
  let [x,y] = G.newNodes 2 g
      h = G.insEdges [(x,y,()),(i,x,()),(y,t,())]  
        $ G.insNodes [(x,stmt v s),(y,stmt v s)] g 
  in toCfg v x ss y h


-- simple inserting nodes
insBetween :: G.Node -> G.Node -> KripkeLabel a 
           -> G.Gr (KripkeLabel a) () -> G.Gr (KripkeLabel a) ()
insBetween i t v g = 
  let n = head $ G.newNodes 1 g in
  G.insEdge (i,n,()) $ G.insEdge (n,t,()) $ G.insNode (n,v) g
-}

-- |removes all empty tags from given graph
-- TODO remove all states marked with Label
prune :: G.DynGraph g => g (KripkeLabel a) () -> g (KripkeLabel a) ()
prune g = prune' (G.nodes g) g where
  prune' []     g = g
  prune' (n:ns) g = let ((_,_,l,_),_) = first fromJust $ G.match n g in 
    case l of
      (Label,_) ->  prune' ns (removeNode n g)
      _     ->  prune' ns g
  
-- * testing values

{-
test :: IO ()
test = mapM_ 
  (\x -> let cfg = prune $ (getCfg::WhileKripkeLabel Varops -> Program -> G.Gr (KripkeLabel Varops) ())vars x in 
    putStrLn "----" >> print ( pretty x) >> print cfg) 
    programs 
-}
test2 :: IO ()
test2 = forM_ programs $ \p -> do
  let (k::KripkeGr String) = dataToKripke p 
  print (pretty p) 
  putStrLn "----" 
  print k

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


test3 :: IO ()
test3 = do
  p <- sample' (arbitrary::Gen Program)
  let (k::KripkeGr String) = dataToKripke $ head p 
  print $ pretty $ head p
  putStrLn "----" 
  --print $ "initstates:"++(show $ initStates k)
  print k
  print "################################"
  print $ eval k (EG $ AP "f")

-- * CTL tests

test2_CTL :: IO ()
test2_CTL = forM_ programs $ \p -> do
  let (k::KripkeGr String) = dataToKripke p 
  print (pretty p) 
  print "------"
  print k 
  print "################################"
  print $ eval k (Conj (AP "(:)") (EX $ AP "'f'"))

