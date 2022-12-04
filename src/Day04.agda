module Day04 where

open import Effect.Applicative
open import Function.Base using (_$_; _∘_)
open import Data.Bool
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.Effectful as List
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; from-just; maybe)
import Data.Maybe.Effectful as Maybe
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Show as ℕ
open import Data.Product as Prod using (_×_; _,_; <_,_>; uncurry)
open import Data.String as String using (String; lines; wordsByᵇ)
open import Data.Char as Char using (_≈ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

data Section : Set where
  [_-_] : ℕ → ℕ → Section

Input : Set
Input = List (Section × Section)

readInput : List String → Maybe Input
readInput = traverse ((Maybe._>>= toPair) ∘ traverse (ℕ.readMaybe 10) ∘ words')
  where
    open List.TraversableA Maybe.applicative renaming (mapA to traverse)
    words' = wordsByᵇ (λ c → (c ≈ᵇ '-') ∨ (c ≈ᵇ ','))
    toPair = λ where
      (l1 ∷ r1 ∷ l2 ∷ r2 ∷ []) → just ([ l1 - r1 ] , [ l2 - r2 ])
      _ → nothing

example : Input
example = from-just $ readInput $
  "2-4,6-8" ∷
  "2-3,4-5" ∷
  "5-7,7-9" ∷
  "2-8,3-7" ∷
  "6-6,4-6" ∷
  "2-6,4-8" ∷
  []

_⊑_ : Section → Section → Bool
[ l1 - r1 ] ⊑ [ l2 - r2 ] = (l2 ℕ.≤ᵇ l1) ∧ (r1 ℕ.≤ᵇ r2)

_⊑∨⊒_ : Section → Section → Bool
s1 ⊑∨⊒ s2 = (s1 ⊑ s2) ∨ (s2 ⊑ s1)

overlaps : Section → Section → Bool
overlaps [ l1 - r1 ] [ l2 - r2 ] = (l2 ℕ.≤ᵇ r1) ∧ (l1 ℕ.≤ᵇ r2)

solve-1 : Input → ℕ
solve-1 = List.length ∘ List.filterᵇ (uncurry _⊑∨⊒_)

solve-2 : Input → ℕ
solve-2 = List.length ∘ List.filterᵇ (uncurry overlaps)

_ : solve-1 example ≡ 2
_ = refl

_ : solve-2 example ≡ 4
_ = refl

sol : String → String
sol = maybe (show ∘ < solve-1 , solve-2 >) "" ∘ readInput ∘ lines
