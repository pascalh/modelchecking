{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies, TemplateHaskell #-}
module WhileMisc where
import Control.Monad

import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile

import Data.DeriveTH
import Data.Generics 

import Test.QuickCheck


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
 

