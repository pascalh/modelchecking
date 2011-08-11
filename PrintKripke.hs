module PrintKripke where

import qualified Kripke as K

import Data.GraphViz
import Data.Graph.Inductive

-- |transforms a kripke structure to dotgraph representation
toDotgraph :: (K.Kripke k,Show l) => Settings -> k l -> IO (DotGraph Node)
toDotgraph s g = do
    let g_dot = DotGraph True True Nothing dstmts 
    runGraphvizCanvas' g_dot Xlib
    return g_dot
  where
  dstmts = DotStmts [nodeAttrs s,edgeAttrs s] [] dnodes dedges 
  dnodes = map (toNode g) $ K.states g 
  dedges =  map toEdge  $ K.rels g

-- |transforms a component to dotnode
toNode :: (K.Kripke k, Show l) 
       => k l -> K.KripkeState -> DotNode K.KripkeState
toNode g n = DotNode n [Center True, Label $ StrLabel $ f n ] where
  f n = case K.labels n g of
    (l:_) -> show n ++ "|"++show l
    _     -> []

-- |creates a directed edge
toEdge :: (K.KripkeState,K.KripkeState) -> DotEdge Node
toEdge (u,v) = DotEdge  u v True edgeAtt

-- |global node attribute
nodeAttrs :: Settings -> GlobalAttributes
nodeAttrs s = NodeAttrs [ Shape BoxShape
                        , FontSize $ fontSize s
                        , FontName $ font s 
                        ]

-- |global edge attribute
edgeAttrs :: Settings -> GlobalAttributes
edgeAttrs s = EdgeAttrs 
  [ FontSize $ fontSize s
  , FontName $ font s
  ]

edgeAtt ::[Attribute]
edgeAtt = []

-- |shows a kripke structure using 'show' to create state labels
showKripke :: (K.Kripke k,Show l) => k l -> IO String 
showKripke k = prettyPrint =<< toDotgraph defaultSettings k

-- |default settings
defaultSettings :: Settings
defaultSettings = Settings 9 "Arial"

-- |print settings for a kripke structure
data Settings = Settings 
              { fontSize :: Double -- ^font size of kripke labels
              , font :: String -- ^font family of kripke labels 
              } 

