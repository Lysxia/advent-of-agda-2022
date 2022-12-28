module Main where

open import Function
open import Data.Unit.Polymorphic.Base
open import Data.List as List using ([]; _∷_)
open import Data.String as String
open import IO.Base as IO using (IO; Main; _>>=_; _>>_)
open import IO.Finite

import Day01
import Day02
import Day03
import Day04
import Day05
import Day06
import Day09
import Day10
import Day11
import Day12
import Day13
import Day15
import Day20
import Day21
import Day23
import Day24
import Day25

run : String → (String → String) → IO ⊤
run name f = do
  input ← readFile ("input/" ++ name)
  putStrLn (name ++ ": " ++ f input)

main : Main
main = IO.run do
  run "Day01" Day01.sol
  run "Day02" Day02.sol
  run "Day03" Day03.sol
  run "Day04" Day04.sol
  run "Day05" Day05.sol
  run "Day06" Day06.sol
  run "Day09" Day09.sol
  run "Day10" Day10.sol
  -- run "Day11" Day11.sol
  run "Day12" Day12.sol
  run "Day13" Day13.sol
  run "Day15" Day15.sol
  run "Day20" Day20.sol
  run "Day21" Day21.sol
  run "Day23" Day23.sol
  run "Day24" Day24.sol
  run "Day25" Day25.sol
