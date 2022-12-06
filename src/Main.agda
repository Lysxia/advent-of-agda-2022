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
