module Day06 where

open import Data.Bool
open import Function.Base using (_∘_; _$_)
open import Data.Nat.Base as ℕ using (ℕ; _+_)
open import Data.String as String using (String)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (allPairs?)
open import Data.Product using (_,′_; <_,_>)
open import Data.Char as Char using (Char; _≟_)
open import Relation.Nullary.Decidable using (isYes; ¬?)
open import Relation.Binary.Definitions using (Decidable; DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Night

Input : Set
Input = List Char

private variable
  A : Set

dec≢ : DecidableEquality A → Decidable {A = A} _≢_
dec≢ decEq x y = ¬? (decEq x y)

nDistinct : ℕ → DecidableEquality A → List A → Bool
nDistinct n decEq = isYes ∘ allPairs? (dec≢ decEq) ∘ List.take n

solve : ℕ → Input → ℕ
solve n = (n +_) ∘ List.length ∘ List.takeWhileᵇ (not ∘ nDistinct n Char._≟_) ∘ List.tails

examples : List Input
examples = List.map String.toList $
  "mjqjpqmgbljsphdztnvjfqwrcgsmlb" ∷
  "bvwbjplbgvbhsrlpgdmjqwftvncz" ∷
  "nppdvjthqldpwncqszvftbrmjlhg" ∷
  "nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg" ∷
  "zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw" ∷
  []

_ : List.map (solve 4) examples ≡ 7 ∷ 5 ∷ 6 ∷ 10 ∷ 11 ∷ []
_ = refl

_ : List.map (solve 14) examples ≡ 19 ∷ 23 ∷ 23 ∷ 29 ∷ 26 ∷ []
_ = refl

sol : String → String
sol = show ∘ (λ x → solve 4 x ,′ solve 14 x) ∘ String.toList
