#!/usr/bin/runhaskell

{-# LANGUAGE RecordWildCards #-}
import Text.Pandoc.JSON
import Text.Pandoc
import Tip
import Tip.Parser
import Tip.Parser.Convert
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3
import Tip.Lint
import Tip.Fresh
import Tip.Simplify
import Tip.Decase
import Tip.Lift
import Tip.EqualFunctions
import Tip.Deprove
import Tip
import Control.Monad

transform :: Block -> IO Block
transform (CodeBlock (name, ("tip":classes), attrs) expr) =
  return (tipBlock name classes attrs expr)
transform (CodeBlock (name, ("tip-include":classes), attrs) file) = do
  contents <- readFile file
  return (tipBlock name classes attrs contents)
transform (CodeBlock (name, ["include"], attrs) file) = do
  contents <- readFile file
  return (CodeBlock (name, [], attrs) contents)
transform block = return block

tipBlock name classes attrs expr =
  CodeBlock (name, [], attrs) (mode modes (foldr (.) id (map pass passes) thy))
  where
    Right thy = parse expr
    (modes, passes) = go classes [] []
    go [] modes passes = (reverse modes, reverse passes)
    go ("match-to-if":xs) modes passes = go xs modes (Decase:passes)
    go ("negate-conjecture":xs) modes passes = go xs modes (Deprove:passes)
    go ("lambda-lift":xs) modes passes = go xs modes (LambdaLift:passes)
    go ("no-datatypes":xs) modes passes = go xs (NoData:modes) passes
    go ("no-check-sat":xs) modes passes = go xs (NoCheckSat:modes) passes
    go ("no-functions":xs) modes passes = go xs (NoFuns:modes) passes
    go ("no-properties":xs) modes passes = go xs (NoProp:modes) passes
    go ("why3":xs) modes passes = go xs (Why3:modes) passes

data Pass = Decase | Deprove | LambdaLift deriving Show
data Mode = NoData | NoProp | NoFuns | NoCheckSat | Why3 deriving (Show, Eq)

pass :: Pass -> Theory Id -> Theory Id
pass Decase     = freshPass decase
pass Deprove    = freshPass deprove
pass LambdaLift = freshPass (axiomatizeLambdas <=< lambdaLift)

mode :: [Mode] -> Theory Id -> String
mode ms thy@Theory{..}
  | Why3 `elem` ms       = show . Why3.ppTheory $ thy'
  | NoCheckSat `elem` ms = out' thy'
  | otherwise = out thy'
  where
    out  = show . SMT.ppTheory
    out' = dropRev (length "(check-sat)") . show . SMT.ppTheory
    dropRev n = reverse . drop n . reverse
    thy' =
      thy {
        thy_data_decls = checking NoData thy_data_decls,
        thy_func_decls = checking NoFuns thy_func_decls,
        thy_form_decls = checking NoFuns thy_form_decls }
    checking x xs
      | x `elem` ms = []
      | otherwise = xs

main = toJSONFilter (bottomUpM transform :: Pandoc -> IO Pandoc)
