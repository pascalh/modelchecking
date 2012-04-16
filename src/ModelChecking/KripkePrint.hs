module ModelChecking.KripkePrint
  (outputKripke,showKripkeInDialog,saveKripke) 
  where

import qualified ModelChecking.Kripke as K

import Data.GraphViz hiding (toNode)
import Data.Graph.Inductive
import Data.GraphViz.Attributes.Complete

-- * main functions and offered interface

-- |a kripke structure to dotgraph representation
outputKripke :: (K.Kripke k,Show l) => Settings -> k l -> IO ()
outputKripke s g = do
    let g_dot = DotGraph True True Nothing dstmts 
    case outputMode s of
      File file -> runGraphviz g_dot Png file >> return () 
      XLib      -> runGraphvizCanvas' g_dot Xlib     
  where
  dstmts = DotStmts [nodeAttrs s,edgeAttrs s] [] dnodes dedges 
  dnodes = map (toNode g) $ K.states g 
  dedges =  map toEdge  $ K.rels g

-- |shows a kripke structure using 'show' to create state labels.
-- The result will be presented in a new dialog window.
showKripkeInDialog :: (K.Kripke k,Show l) => k l -> IO () 
showKripkeInDialog k = outputKripke defaultSettings k >> return ()

-- |shows a kripke structure using 'show' to create state labels.
-- The result will be presented in a new dialog window.
saveKripke :: (K.Kripke k,Show l) => FilePath -> k l -> IO () 
saveKripke file k = do
  outputKripke (defaultSettings {outputMode = File file }) k
  return ()

-- * Settings

-- |print settings for a kripke structure
data Settings = Settings 
              { fontSize :: Double -- ^font size of kripke labels
              , outputMode :: Mode
              } 

-- |data type for output modes
data Mode = XLib -- ^ show kripke structure in a dialog 
          | File FilePath -- ^ save kripke structure to a file

-- |default settings
defaultSettings :: Settings
defaultSettings = Settings 9 XLib

-- * transforming a kripke structure to a dot graph

-- |transforms a state to dotnode
toNode :: (K.Kripke k, Show l) 
       => k l -> K.KripkeState -> DotNode K.KripkeState
toNode g n = DotNode n [Center True, Label $ toLabelValue m ] where
  m :: String
  m = case K.labels n g of
    (l:_) -> show n ++ "|"++show l
    _     -> []

-- |creates a directed edge
toEdge :: (K.KripkeState,K.KripkeState) -> DotEdge Node
toEdge (u,v) = DotEdge  u v edgeAtt

-- |global node attribute
nodeAttrs :: Settings -> GlobalAttributes
nodeAttrs s = NodeAttrs [ Shape Ellipse 
                        , FontSize $ fontSize s
                        , FontColor $ X11Color RoyalBlue4
                        ]

-- |global edge attribute
edgeAttrs :: Settings -> GlobalAttributes
edgeAttrs s = EdgeAttrs 
  [ FontSize $ fontSize s
  , Style $ return $ SItem Dotted []
  , ArrowHead $ AType [(ArrMod OpenArrow BothSides,Vee)]
  ]

edgeAtt ::[Attribute]
edgeAtt = [Dir Forward]


