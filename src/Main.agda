module Main where

open import Function
open import Data.Unit.Polymorphic.Base
open import Data.List as List using ([]; _∷_)
open import Data.String as String
open import IO.Base as IO using (IO; Main; _>>=_)
open import IO.Finite

import Day01

run : String → (String → String) → IO ⊤
run name f = do
  input ← readFile ("input/" ++ name)
  putStrLn (name ++ ": " ++ f input)

main : Main
main = IO.run do
  run "Day01" Day01.sol
