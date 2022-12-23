{-# OPTIONS --allow-exec #-}
module Day15 where

import Algebra.Definitions
open import Level using () renaming (zero to 0ℓ)
open import Effect.Monad
open import Function.Base using (_∘_; _∘′_; _$_; flip; case_of_; id)
open import Agda.Builtin.FromNat using (Number; fromNat)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Literals renaming (number to number-ℕ)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer as Int hiding (show)
import Data.Integer.Properties as Intₚ
open import Data.Integer.Literals renaming (number to number-ℤ)
open import Data.Maybe.Base using (Maybe; nothing; just; from-just; maybe)
open import Data.Maybe.Effectful as Maybe using (monad)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
open import Data.Product as Prod using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String.Base as String using (String)
open import Relation.Nullary using (¬_; Reflects; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (∅; _∪_; _∩_; _≐_; _⊆_; ∁)
open import Relation.Unary.Properties
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Relation.Binary.Reasoning.Base.Single as Reasoning

open import Night
open import Day15Core

private variable
  A : Set

instance
  _ : ⊤
  _ = tt
  _ : Number ℕ
  _ = number-ℕ
  _ : Number ℤ
  _ = number-ℤ

solve-0 : Input → ℕ
solve-0 = disjointSize ∘ disjoint-union 10

{-
example : Input
example = from-just $ readInput $
  "Sensor at x=2, y=18: closest beacon is at x=-2, y=15" ∷
  "Sensor at x=9, y=16: closest beacon is at x=10, y=16" ∷
  "Sensor at x=13, y=2: closest beacon is at x=15, y=3" ∷
  "Sensor at x=12, y=14: closest beacon is at x=10, y=16" ∷
  "Sensor at x=10, y=20: closest beacon is at x=10, y=16" ∷
  "Sensor at x=14, y=17: closest beacon is at x=10, y=16" ∷
  "Sensor at x=8, y=7: closest beacon is at x=2, y=10" ∷
  "Sensor at x=2, y=0: closest beacon is at x=2, y=10" ∷
  "Sensor at x=0, y=11: closest beacon is at x=2, y=10" ∷
  "Sensor at x=20, y=14: closest beacon is at x=25, y=17" ∷
  "Sensor at x=17, y=20: closest beacon is at x=21, y=22" ∷
  "Sensor at x=16, y=7: closest beacon is at x=15, y=3" ∷
  "Sensor at x=14, y=3: closest beacon is at x=15, y=3" ∷
  "Sensor at x=20, y=1: closest beacon is at x=15, y=3" ∷
  []

_ : solve-0 example ≡ 26
_ = refl
-}

solve-1 : Input → ℕ
solve-1 = disjointSize ∘ disjoint-union 2000000

searchFrom : ℕ → (ℕ → Maybe A) → Maybe A
searchFrom 0 _ = nothing
searchFrom (ℕ.suc i) f with f i
... | nothing = searchFrom i f
... | just x = just x

search′ : Input → ℤ → Maybe Point
search′ pts y = case sets (disjoint-union y pts) of λ where
    ((i , j) ∷ (k , l) ∷ []) → case ((i ≟ l + 1) , (k ≟ j + 1)) of λ where
      (yes _ , _) → just (l , y)
      (_ , yes _) → just (j , y)
      _ → nothing
    _ → nothing
  where
    open DisjointUnion using (sets)

search : (ymax : ℤ) → Input → Maybe Point
search ymax pts = searchFrom (ℕ.suc ∣ ymax ∣) (search′ pts ∘ +_)

abstract
  n-4M : ℤ
  n-4M = 4000000

solve-2 : Input → ℕ
solve-2 = maybe f 0 ∘ search n-4M
  where
    f = λ{ (x , y) → ∣ x * n-4M + y ∣ }

sol : String → String
sol = maybe (show ∘ solve-1) "" ∘ readInput ∘ String.lines
