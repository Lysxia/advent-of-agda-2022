{-# OPTIONS -v print:1 #-}
module Day01 where

open import Function.Base using (_∘_; _$_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ using (readMaybe)
open import Data.List.Base using (List; []; _∷_; map; sum; mapMaybe; take)
open import Data.List.NonEmpty as List⁺ using (wordsBy; toList) renaming (map to map⁺)
open import Data.Unit using (⊤)
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; lines; _≈?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

-- _≤_: increasing order of ℕ
open import Data.Nat.Properties using (≤-decTotalOrder)

-- _≥_: decreasing order of ℕ
open import Relation.Binary.Properties.DecTotalOrder ≤-decTotalOrder using (≥-decTotalOrder)

-- Maximum of a list
open import Data.List.Extrema.Nat using (max)

-- Sorting lists, in decreasing order
open import Data.List.Sort.MergeSort ≥-decTotalOrder using (sort)

-- Type of inputs
Input : Set
Input = List (List ℕ)

-- Parsing
readInput : List String → Maybe Input
readInput = traverse (traverse (ℕ.readMaybe 10) ∘ toList) ∘ wordsBy ("" ≈?_)

example : Input
example = from-just $ readInput $
  "1000" ∷
  "2000" ∷
  "3000" ∷
  "" ∷
  "4000" ∷
  "" ∷
  "5000" ∷
  "6000" ∷
  "" ∷
  "7000" ∷
  "8000" ∷
  "9000" ∷
  "" ∷
  "10000" ∷
  []


-- Solutions

solve-1 : Input → ℕ
solve-1 = max 0 ∘ map sum

solve-2 : Input → ℕ
solve-2 = sum ∘ take 3 ∘ sort ∘ map sum


-- Examples

_ : solve-1 example ≡ 24000
_ = refl

_ : solve-2 example ≡ 45000
_ = refl

-- Fun with macros
_ : ⊤
_ = print (solve-1 example)

-- Wrapped solution
sol : String → String
sol str with readInput (lines str)
... | just input = show (solve-1 input , solve-2 input)
... | nothing = ""
