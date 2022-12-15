module Day13 where

open import Function.Base using (_∘_; _$_)
open import Data.Bool.Base using (true; false)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
open import Data.Sum.Base using (fromInj₂)
open import Data.DifferenceList as DList using (DiffList; [_]; _++_)
open import Data.String.Base as String using (String)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Induction.Nat.Strong using (fix)
open import Text.Parser

open import Night

private variable
  A : Set

data Tree : Set where
  list : List Tree → Tree
  atom : ℕ → Tree

Input : Set
Input = List (Tree × Tree)

module Parse where

  tree : ∀[ Parser Tree ]
  tree = fix (Parser Tree) λ □tree →
    let □comma = box (_++_ <$ exact ',')
        □chainr1 = lift2 (λ tree comma →
          (list ∘ DList.toList) <$> chainr1 ([_] <$> tree) (box comma))
        list⁺ = between (exact '[') (box (exact ']')) (□chainr1 □tree □comma)
    in (list [] <$ text "[]")
    <|> list⁺
    <|> atom <$> decimalℕ

  _ : "[]" ∈ tree
  _ = list [] !

  _ : "[3]" ∈ tree
  _ = list (atom 3 ∷ []) !

  _ : "[3,[4,[5],6]]" ∈ tree
  _ = list (atom 3 ∷
            list (atom 4 ∷
                  list (atom 5 ∷ []) ∷
                  atom 6 ∷ []) ∷ []) !

  input : ∀[ Parser Input ]
  input = List⁺.toList <$> list⁺ (withSpaces (tree <& box spaces <&> box tree))

  _ : "[]\n[]\n" ∈ input
  _ = ((list [] , list []) ∷ []) !

data Cmp : Set where
  LT EQ GT : Cmp

_<>_ : Cmp → Cmp → Cmp
EQ <> c = c
LT <> c = LT
GT <> c = GT

run-out : List A → Cmp → Cmp
run-out [] _ = EQ
run-out (_ ∷ _) c = c

compare : Tree → Tree → Cmp
compare (atom n) (atom m) with Nat.<-cmp n m
... | tri< _ _ _ = LT
... | tri≈ _ _ _ = EQ
... | tri> _ _ _ = GT
compare (atom n) (list []) = GT
compare (atom n) (list (x ∷ xs)) = compare (atom n) x <> run-out xs LT
compare (list []) (list []) = EQ
compare (list []) (list (_ ∷ _)) = LT
compare (list []) (atom y) = LT
compare (list (x ∷ xs)) (list []) = GT
compare (list (x ∷ xs)) (list (y ∷ ys)) = compare x y <> compare (list xs) (list ys)
compare (list (x ∷ xs)) (atom y) = compare x (atom y) <> run-out xs GT

readInput : String → Input
readInput = fromInj₂ (λ _ → []) ∘ runParser Parse.input

example : Input
example = readInput $ String.unlines $
  "[1,1,3,1,1]" ∷
  "[1,1,5,1,1]" ∷
  "" ∷
  "[[1],[2,3,4]]" ∷
  "[[1],4]" ∷
  "" ∷
  "[9]" ∷
  "[[8,7,6]]" ∷
  "" ∷
  "[[4,4],4,4]" ∷
  "[[4,4],4,4,4]" ∷
  "" ∷
  "[7,7,7,7]" ∷
  "[7,7,7]" ∷
  "" ∷
  "[]" ∷
  "[3]" ∷
  "" ∷
  "[[[]]]" ∷
  "[[]]" ∷
  "" ∷
  "[1,[2,[3,[4,[5,6,7]]]],8,9]" ∷
  "[1,[2,[3,[4,[5,6,0]]]],8,9]" ∷
  []

number-from : ℕ → List A → List (ℕ × A)
number-from i [] = []
number-from i (x ∷ xs) = (i , x) ∷ number-from (Nat.suc i) xs

solve-1 : Input → ℕ
solve-1 = List.sum ∘ List.map proj₁ ∘ List.filterᵇ f ∘ number-from 1
  where
    isn'tGT = λ{ GT → false ; _ → true }
    f = isn'tGT ∘ uncurry compare ∘ proj₂

_ : solve-1 example ≡ 13
_ = refl

sol : String → String
sol = show ∘ solve-1 ∘ readInput
