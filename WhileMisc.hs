{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies, TemplateHaskell #-}
module WhileMisc where
import Control.Monad

import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile

import Data.DeriveTH
import Data.Generics hiding (empty) 

import Test.QuickCheck

import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile
import Kripke

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

$( derive makeData ''Program )
$( derive makeTypeable ''Program )

$( derive makeData ''Stmts )
$( derive makeTypeable ''Stmts )
$( derive makeData ''Stmt )
$( derive makeTypeable ''Stmt )
$( derive makeData ''BExp )
$( derive makeTypeable ''BExp )
$( derive makeData ''Ident )
$( derive makeTypeable ''Ident )


instance Arbitrary Program where
  arbitrary = sized $ \n -> liftM Program $ arStmts n

instance Arbitrary Ident where
  arbitrary = liftM Ident (elements $ map return ['a'..'z'])

instance Arbitrary BExp where
  arbitrary = sized arBEXP

arBEXP :: Int -> Gen BExp
arBEXP n
  |n<=0 = elements [BTrue,BFalse]
  |n>0  = oneof [liftM BNeg st1
                ,liftM2 BConj st2 st2
                ,liftM2 BDisj st2 st2
                ] where
    st1 = arBEXP (n-1)
    st2 = arBEXP (n `div` 2)


instance Arbitrary Stmt where
  arbitrary = sized arStmt

arStmt :: Int -> Gen Stmt
arStmt n
  |n<=0 = oneof [liftM SDecl arbitrary
                ,liftM2 SAssign arbitrary (arBEXP (n-1))
                ]
  |n>0 = oneof [liftM2 SIf (arBEXP (n-1)) (arStmts (n-1)) 
               ,liftM2 SWhile (arBEXP (n-1)) (arStmts (n-1)) 
               ] 

instance Arbitrary Stmts where
  arbitrary = sized arStmts

arStmts :: Int -> Gen Stmts
arStmts n 
  |n<=0 = liftM StmtsE (arStmt (n-1))
  |n>0  = liftM2 Stmts (arStmt (n-1)) (arStmts (n-1))
 
-- * creating control-flow graphs for WHILE

varCFG :: Program -> KripkeGr Varops
varCFG = getCfg vars 

data Varops = Decl String | Read String | Write String | VLabel String 

instance Show Varops where
  show (Decl s) = "Decl "++s
  show (Read s) = "Read "++s
  show (Write s) = "Write "++s
  show (VLabel s) = s

-- * define a datatype which contains the transformation functions 

-- |data type for defining cfg-node-label-creations
data WhileKripkeLabel 
  = WhileKripkeLabel 
  { program :: Program -> Varops 
  , stmts   :: Stmts   -> Varops
  , stmt    :: Stmt    -> Varops
  , bexp    :: BExp    -> Varops
  }

vars :: WhileKripkeLabel 
vars = WhileKripkeLabel toKripkeLabel toKripkeLabel toKripkeLabel toKripkeLabel 

class TonNode a where
  toKripkeLabel :: a -> Varops 

class Foo a where
  getCfg :: WhileKripkeLabel -> a -> KripkeGr Varops 
  getCfg v p = toCfg v undefined p undefined undefined

  toCfg :: WhileKripkeLabel -> Int -> a -> Int -> KripkeGr Varops ->KripkeGr Varops 

instance Foo Program where
  toCfg v _ (Program ss) _ _ =   
    let g     = empty 
        [i,t] = newNodes 2 g
        h     = addStateWithLabel t (VLabel []) $
                addInitState i g
    in toCfg v i ss t h


instance Foo Stmts where
  toCfg v i (StmtsE s  ) t g = toCfg v i s t g
  toCfg v i (Stmts s ss) t g = 
    let b = head $ newNodes 1 g in 
      toCfg v b ss t $ toCfg v i s b $ 
        addStateWithLabel b (VLabel []) g -- (toKripkeLabel $ Stmts s ss ) g

instance Foo Stmt where
  toCfg v i s t g = 
    case s of
      (SIf _ _)    -> insCond v i t s g
      (SWhile _ _) -> insCond v i t s g
      _            -> insBetween i t (stmt v $ s) g


-- ks: a -> Varops
instance TonNode Program where
  toKripkeLabel _ = VLabel []

instance TonNode Stmt where
  toKripkeLabel (SDecl (Ident i))     = Decl i
  toKripkeLabel (SAssign (Ident i) _) = Write i
  toKripkeLabel (SWhile _ _)          = VLabel "While"
  toKripkeLabel (SIf _ _)             = VLabel "If"

instance TonNode Stmts where
  toKripkeLabel _ = VLabel []

instance TonNode BExp where
  toKripkeLabel _ = VLabel [] 


insCond :: WhileKripkeLabel -> KripkeState -> KripkeState  -> Stmt 
        -> KripkeGr Varops -> KripkeGr Varops
insCond v i t s@(SWhile _ ss) g = 
  let [x,y] = newNodes 2 g
      h = addRel y x $ addRel x y $ addRel i x $ addRel y t   
        $ addStateWithLabel x (stmt v s)
        $ addStateWithLabel y (stmt v s) g 
  in toCfg v x ss y h 

insCond v i t s@(SIf _ ss) g = 
  let [x,y] = newNodes 2 g
      h = addRel x y $ addRel i x $ addRel y t  
        $ addStateWithLabel x (stmt v s) 
        $ addStateWithLabel y (stmt v s) g 
  in toCfg v x ss y h


-- simple inserting nodes
insBetween :: KripkeState -> KripkeState -> Varops 
           -> KripkeGr Varops -> KripkeGr Varops
insBetween i t v  g =  
  let n = head $ newNodes 1 g in 
  addRel i n $ addRel n t $ addStateWithLabel n v g
