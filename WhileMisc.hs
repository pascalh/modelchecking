{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies, TemplateHaskell #-}
module WhileMisc where
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile

import Data.DeriveTH
import Data.Generics hiding (empty)

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
