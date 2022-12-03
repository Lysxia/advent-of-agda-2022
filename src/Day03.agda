module Day03 where

open import Function using (_∘_; _$_)
open import Function.Inverse using (Inverse)
open import Function.Bijection using (Bijection)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; _+_; _∸_; _/_)
import Data.Nat.Properties as ℕ
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Properties
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties using (∃∈-Any)
open import Data.List.Relation.Binary.Permutation.Propositional as Perm using (_↭_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe)
open import Data.Product as Prod using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Char as Char using (Char)
open import Data.String as String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable as Dec using (from-yes)
open import Relation.Unary using (Pred; _⊆_; _≐_; _∩_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night using (show)

Bag : Set
Bag = List ℕ

Input : Set
Input = List Bag

readInput : List String → Input
readInput = List.map (List.map readChar ∘ String.toList)
  where
    readChar : Char → ℕ
    readChar c with Char.isLower c
    ... | true  = 1 + (Char.toℕ c ∸ Char.toℕ 'a')
    ... | false = 27 + (Char.toℕ c ∸ Char.toℕ 'A')

example : Input
example = readInput $
  "vJrwpWtwJgWrhcsFMMfFFhFp" ∷
  "jqHRNqRjqzjGDLGLrsFMfFZSrLrFZsSL" ∷
  "PmmdzqPrVvPwwTWBwg" ∷
  "wMqvLMZHhHMvwLHjbvcjnnSBnvTQFn" ∷
  "ttgJtRGJQctTZtZT" ∷
  "CrZsJsPPZsGzwwsLwLmpwMDw" ∷
  []

module Part1 where
  Input₁ : Set
  Input₁ = List (List ℕ × List ℕ)

  splitHalf : {A : Set} → List A → List A × List A
  splitHalf xs = List.splitAt (List.length xs / 2) xs

  toInput₁ : Input → Input₁
  toInput₁ = List.map splitHalf

  example₁ : Input₁
  example₁ = toInput₁ example

  module Find {A : Set} (_≟_ : DecidableEquality A) where

    open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

    open Perm.PermutationReasoning

    find-intersect : ∀ (xs ys : List A) → Dec (∃[ x ] x ∈ xs × x ∈ ys)
    find-intersect xs ys = Dec.map′ find ∃∈-Any (Any.any? (λ x → x ∈? ys) xs)

  open Find ℕ._≟_

  Valid : Input₁ → Set
  Valid = All (λ{ (xs , ys) → ∃[ x ] x ∈ xs × x ∈ ys })

  validate : (input : Input₁) → Dec (Valid input)
  validate = All.all? (uncurry find-intersect)

  valid-example : Valid example₁
  valid-example = from-yes (validate example₁)

  solve : {input : Input₁} → Valid input → ℕ
  solve = List.sum ∘ All.reduce proj₁

  _ : solve valid-example ≡ 157
  _ = refl

solve-1 : Input → Maybe ℕ
solve-1 input with Part1.validate (Part1.toInput₁ input)
... | yes valid = just (Part1.solve valid)
... | no _ = nothing

module Part2 where
  Input₂ : Set
  Input₂ = List (List⁺ Bag)

  toInput₂ : Input → Input₂
  toInput₂ (x ∷ y ∷ z ∷ xs) = (x ∷ y ∷ z ∷ []) ∷ toInput₂ xs
  toInput₂ _ = []

  example₂ : Input₂
  example₂ = toInput₂ example

  module Find {A : Set} (_≟_ : DecidableEquality A) where

    open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

    open Perm.PermutationReasoning

    find-intersects : (xs : List A) → (xss : List (List A)) → Dec (∃[ x ] All (x ∈_) (xs ∷ xss))
    find-intersects xs xss = Dec.map′ to from (Any.any? (λ x → All.all? (x ∈?_) xss) xs)
      where
        to = λ any-xs → let x , x∈xs , x∈xss = find any-xs in x , x∈xs ∷ x∈xss
        from = λ{ (x , x∈xs ∷ x∈xss) → ∃∈-Any (x , x∈xs , x∈xss) }

  open Find ℕ._≟_

  Valid : Input₂ → Set
  Valid = All (λ{ (xs ∷ xss) → ∃[ x ] All (x ∈_) (xs ∷ xss) })

  validate : (input : Input₂) → Dec (Valid input)
  validate = All.all? λ{ (xs ∷ xss) → find-intersects xs xss }

  valid-example : Valid example₂
  valid-example = from-yes (validate example₂)

  solve : {input : Input₂} → Valid input → ℕ
  solve = List.sum ∘ All.reduce proj₁

  _ : solve valid-example ≡ 70
  _ = refl

solve-2 : Input → Maybe ℕ
solve-2 input with Part2.validate (Part2.toInput₂ input)
... | yes valid = just (Part2.solve valid)
... | no _ = nothing

sol : String → String
sol str = show (solve-1 input , solve-2 input)
  where
    input = readInput (String.lines str)
