{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies , ScopedTypeVariables #-}

module Cfg where
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile

import Test.QuickCheck
import WhileMisc
import Kripke
import CTL
import DataToGraph
import PrintKripke (showKripke)
import Control.Monad (forM_)



test :: IO ()
test = forM_ programs $ \p ->  
  let cfg = varCFG p in 
  putStrLn "----" >> print (pretty p) >> showKripke cfg 

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
  ps <- sample' (arbitrary::Gen Program)
  let (ks::[KripkeGr String]) = map dataToKripke $ take 5 ps
  -- print $ pretty $ head p
  --putStrLn "----" 
  --print $ "initstates:"++(show $ initStates k)
  --print k
  --print "################################"
  mapM_ (print . flip eval (EG $ AP "[]")) ks

-- * CTL tests

test2_CTL :: IO ()
test2_CTL = forM_ programs $ \p -> do
  let (k::KripkeGr String) = dataToKripke p 
  print (pretty p) 
  print "------"
  let f = EG $ Disj (AP "[]") (AP "(:)")
  print $ eval k f
  print "################################"
  showKripke k
  --print $ eval k (Conj (AP "(:)") (EX $ AP "'f'"))

