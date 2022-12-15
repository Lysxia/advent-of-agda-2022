module Day13 where

open import Function.Base using (_∘_; _$_; case_of_)
open import Data.Bool.Base using (true; false)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂; uncurry)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
open import Data.Sum.Base using (fromInj₂; inj₁; inj₂)
open import Data.DifferenceList as DList using (DiffList; [_]; _++_)
open import Data.String.Base as String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Definitions
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

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

_≈_ : Tree → Tree → Set
t ≈ u = Erased (compare t u ≡ EQ)

compare-refl : (t : Tree) → compare t t ≡ EQ
compare-refl (list []) = refl
compare-refl (list (x ∷ xs)) with compare-refl x | compare-refl (list xs)
... | eq | eq′ rewrite eq = eq′
compare-refl (atom x) with Nat.<-cmp x x
... | tri≈ _ _ _ = refl
... | tri< _ x≉x _ = contradiction refl x≉x
... | tri> _ x≉x _ = contradiction refl x≉x

_≈?_ : Decidable _≈_
t ≈? u with compare t u
... | EQ = yes (erased refl)
... | GT = no λ()
... | LT = no λ()

_≤_ : Tree → Tree → Set
t ≤ u = Erased (compare t u ≢ GT)

_≤?_ : Decidable _≤_
t ≤? u with compare t u
... | EQ = yes (erased λ())
... | LT = yes (erased λ())
... | GT = no λ{ (erased ¬) → erased-⊥ (¬ refl) }

postulate @0 compare-sym : {t u : Tree} → compare t u ≡ EQ → compare u t ≡ EQ
postulate @0 compare-trans : {t u v : Tree} → compare t u ≡ EQ → compare u v ≡ EQ → compare t v ≡ EQ
postulate @0 trans-< : {t u v : Tree} → compare t u ≢ GT → compare u v ≢ GT → compare t v ≢ GT
postulate @0 asym-< : {t u : Tree} → compare t u ≡ GT → compare u t ≢ GT
postulate @0 antisym-< : {t u : Tree} → compare t u ≢ GT → compare u t ≢ GT → compare u t ≡ EQ

≤-refl : {t u : Tree} → t ≈ u → t ≤ u
≤-refl (erased eq) = erased (λ eq′ → case erased (trans (sym eq) eq′) of λ ())

≤-trans : Transitive _≤_
≤-trans {t} {u} {v} (erased p) (erased q) = erased (trans-< {t} {u} {v} p q)

total-≤ : Total _≤_
total-≤ t u with compare t u in eq
... | EQ = inj₁ (erased λ())
... | LT = inj₁ (erased λ())
... | GT = inj₂ (erased (asym-< {t} {u} eq))

≈-refl : Reflexive _≈_
≈-refl {t} rewrite compare-refl t = erased refl

≈-sym : Symmetric _≈_
≈-sym {t} {u} (erased q) = (erased (compare-sym {t} {u} q))

≈-trans : Transitive _≈_
≈-trans {t} {u} {v} (erased q) (erased p) = erased (compare-trans {t} {u} {v} q p)

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl = λ {t} → ≈-refl {t}
  ; sym = λ {t} {u} → ≈-sym {t} {u}
  ; trans = λ {t u v} → ≈-trans {t} {u} {v}
  }

isPartialOrder : IsPartialOrder _≈_ _≤_
isPartialOrder = record
  { isPreorder = record
      { isEquivalence = ≈-isEquivalence
      ; reflexive = λ {t} {u} → ≤-refl {t} {u}
      ; trans = λ {t} {u} → ≤-trans {t} {u}
      }
  ; antisym = λ{ {t} {u} (erased a) (erased b) → erased (antisym-< {u} {t} b a) } }

isTotalOrder : IsTotalOrder _≈_ _≤_
isTotalOrder = record
  { isPartialOrder = isPartialOrder
  ; total = total-≤
  }

isDecTotalOrder : IsDecTotalOrder _≈_ _≤_
isDecTotalOrder = record
  { isTotalOrder = isTotalOrder
  ; _≟_ = _≈?_
  ; _≤?_ = _≤?_
  }

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record { isDecTotalOrder = isDecTotalOrder }

open import Data.List.Sort.MergeSort decTotalOrder using (sort)

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

pattern [[_]] n = list (list (atom n ∷ []) ∷ [])


solve-2 : Input → ℕ
solve-2 = p ∘ List.filterᵇ f ∘ number-from 1 ∘ sort ∘ List.concatMap (λ{ (x , y) → x ∷ y ∷ [] }) ∘ (([[ 2 ]] , [[ 6 ]]) ∷_)
  where
    f = λ{ (_ , [[ 2 ]]) → true ; (_ , [[ 6 ]]) → true ; _ → false }
    p = λ{ ((i , _) ∷ (j , _) ∷ []) → i Nat.* j ; _ → 0 }

_ : solve-1 example ≡ 13
_ = refl

_ : solve-2 example ≡ 140
_ = refl

sol : String → String
sol = show ∘ < solve-1 , solve-2 > ∘ readInput
