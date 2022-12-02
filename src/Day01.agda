{-# OPTIONS -v print:1 #-}
module Day01 where

open import Level using (zero)
open import Function.Base using (_∘_; _$_)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-totalOrder; ≤-decTotalOrder)
import Data.Nat.Show as ℕ using (readMaybe)
open import Data.List.Base using (List; []; _∷_; map; sum; mapMaybe; take)
open import Data.List.Effectful as List
open import Data.List.Extrema.Nat using (max)
open import Data.List.NonEmpty as List⁺ using (wordsBy; toList) renaming (map to map⁺)
open import Data.Unit using (⊤)
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Maybe.Effectful as Maybe using (applicative)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; lines; _≈?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Properties.DecTotalOrder ≤-decTotalOrder using (≥-decTotalOrder)

open import Data.List.Sort.MergeSort ≥-decTotalOrder using (sort)

open import Night

Input : Set
Input = List (List ℕ)

readInput : List String → Maybe Input
readInput = mapA (mapA (ℕ.readMaybe 10) ∘ toList) ∘ wordsBy ("" ≈?_)
  where
    open List.TraversableA (Maybe.applicative {zero}) using (mapA)

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

solve-1 : Input → ℕ
solve-1 = max 0 ∘ map sum

solve-2 : Input → ℕ
solve-2 = sum ∘ take 3 ∘ sort ∘ map sum

_ : solve-1 example ≡ 24000
_ = refl

_ : solve-2 example ≡ 45000
_ = refl

_ : ⊤
_ = print (solve-1 example)

sol : String → String
sol str with readInput (lines str)
... | just input = show (solve-1 input , solve-2 input)
... | nothing = ""
