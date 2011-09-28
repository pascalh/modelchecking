{- |this module offers an interface to define logics for kripke 
-- structures. -}
module ModelChecking.Logic where
import ModelChecking.Kripke

-- |interface for logics
class Logic l where
  -- |returns all states which satisfy given formula in kripke structure
  eval :: (Eq a,Kripke k) => k a -> l a -> [KripkeState]

  -- |does formula hold at given state?
  holds :: (Kripke k, Eq a) => KripkeState -> k a -> l a -> Bool
  holds s k phi = s `elem` eval k phi
