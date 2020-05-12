module Main where


import           Criterion
import           Criterion.Main (defaultMain)

import           ParComp.Examples.CFG (runCFG)
import           ParComp.Examples.TSG (runTSG)


main :: IO ()
main = do
  defaultMain
    [ bgroup "examples" 
      [ bench "CFG (simple parser)"   $ whnfIO (runCFG True)
      , bench "CFG (regular parser)"  $ whnfIO (runCFG False)
      , bench "TSG (simple parser)"   $ whnfIO (runTSG True)
      , bench "TSG (regular parser)"  $ whnfIO (runTSG False)
      ]
    ]
