module Day24 where

open import Function.Base using (_∘_; _$_)
open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Char.Base using (Char)
open import Data.Maybe.Base using (Maybe; just; nothing; from-just; maybe; fromMaybe; when)
open import Data.Nat.Base as Nat using (ℕ; suc; zero; pred; _≡ᵇ_; _%_; _+_)
import Data.Nat.Properties as Natₚ
open import Data.String.Base as String using (String)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Data.Unit.Base using (⊤; tt)
import Data.Tree.AVL.Map as MkMap
import Data.Tree.AVL.Sets as MkSets
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

private variable
  A : Set

Point : Set
Point = ℕ × ℕ

-- Point-indexed maps
module _ where
  STO2 : StrictTotalOrder _ _ _
  STO2 = ×-strictTotalOrder Natₚ.<-strictTotalOrder Natₚ.<-strictTotalOrder

  open module Map = MkMap STO2 public
    using (Map)

module _ where
  open module Sets = MkSets Natₚ.<-strictTotalOrder public
    using (⟨Set⟩)

record Input : Set where
  field
    width height : ℕ  -- height and width of the core area (starting point (1,0), end point (width,height+1), and other non-boundary points range in [1,width]×[1,height]
    carte : Map (⟨Set⟩ × ⟨Set⟩)
    -- horizontal and vertical moduli when the cell is occupied

TimePoint : Set
TimePoint = ℕ × ℕ × ℕ

STO3 : StrictTotalOrder _ _ _
STO3 = ×-strictTotalOrder Natₚ.<-strictTotalOrder (×-strictTotalOrder Natₚ.<-strictTotalOrder Natₚ.<-strictTotalOrder)

_%%_ : ℕ → ℕ → ℕ
n %% zero = zero
n %% m@(suc _) = n % m

is-final : Input → Point → Bool
is-final input (x , y)
  = (x ≡ᵇ Input.width input)
  ∧ (y ≡ᵇ suc (Input.height input))

free : Input → TimePoint → Bool
free input (t , p@(x , y)) with Map.lookup (Input.carte input) p
... | just (hor , ver)
    = not (Sets.member (t %% Input.width input) hor)
    ∧ not (Sets.member (t %% Input.height input) ver)
... | nothing = false

neighbors : Input → TimePoint → List TimePoint
neighbors input (t , (x , y)) = List.filterᵇ (free input) $
  (suc t , (x , y)) ∷
  (suc t , (pred x , y)) ∷
  (suc t , (x , pred y)) ∷
  (suc t , (suc x , y)) ∷
  (suc t , (x , suc y)) ∷
  []

record Stream {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A

module _ where
  open module S = MkSets STO2
    renaming (⟨Set⟩ to Visited)

  private
    V = TimePoint

    uniq : Visited → List V → List V
    uniq visited [] = []
    uniq visited (x@(t , p) ∷ xs) with S.member p visited
    ... | true = uniq visited xs
    ... | false = x ∷ uniq (S.insert p visited) xs

    bfs : Input → List V → Stream (List V)
    bfs input to-visit = λ where
      .Stream.head → to-visit
      .Stream.tail → bfs input (uniq S.empty (List.concatMap (neighbors input) to-visit))

  reach : Input → TimePoint → Stream (List TimePoint)
  reach input start = bfs input (start ∷ [])

find-Stream : ℕ → (A → Bool) → Stream A → Maybe ℕ
find-Stream {A} fuel f = go fuel 0
  where
    go : ℕ → ℕ → Stream A → Maybe ℕ
    go 0 i s = nothing
    go (suc n) i s with f (Stream.head s)
    ... | true = just i
    ... | false = go n (suc i) (Stream.tail s)

point-eq : Point → Point → Bool
point-eq (x , y) (x′ , y′) = (x ≡ᵇ x′) ∧ (y ≡ᵇ y′)

reach-from-to : Input → TimePoint → Point → Maybe ℕ
reach-from-to input start end =
  find-Stream 1000 (List.any (point-eq end ∘ proj₂)) (reach input start)

solve-1 : Input → Maybe ℕ
solve-1 input = reach-from-to input start end
  where
    open Input input
    start = (0 , 1 , 0) 
    end = (width , suc height)

solve-2 : Input → Maybe ℕ
solve-2 input = do
    t₁ ← reach-from-to input (0 , start) end
    t₂ ← reach-from-to input (t₁ , end) start
    t₃ ← reach-from-to input (t₁ + t₂ , start) end
    just (t₁ + t₂ + t₃)
  where
    open Data.Maybe.Base
    open Input input
    start = (1 , 0) 
    end = (width , suc height)

take-S : ℕ → Stream A → List A
take-S 0 s = []
take-S (suc n) s = Stream.head s ∷ take-S n (Stream.tail s)

forℕ : ℕ → A → (ℕ → A → A) → A
forℕ zero i _ = i
forℕ (suc n) i f = f n (forℕ n i f)

add> : ℕ → ℕ → Input → Input
add> x y m = record m { carte = forℕ width carte λ i →
   Map.insertWith (1 + ((x + i ∸ 1) %% width) , y)
    (λ where (just (hor , ver)) → (Sets.insert i hor , ver)
             nothing → (Sets.singleton i , Sets.empty) ) }
  where
    open Input m
    open Nat using (_+_; _∸_)

add< : ℕ → ℕ → Input → Input
add< x y m = record m { carte = forℕ width carte λ i →
   Map.insertWith (1 + ((x + width ∸ i ∸ 1) %% width) , y)
    (λ where (just (hor , ver)) → (Sets.insert i hor , ver)
             nothing → (Sets.singleton i , Sets.empty) ) }
  where
    open Input m
    open Nat using (_+_; _∸_)

addv : ℕ → ℕ → Input → Input
addv x y m = record m { carte = forℕ width carte λ i →
   Map.insertWith (x , 1 + ((y + i ∸ 1) %% height))
    (λ where (just (hor , ver)) → (hor , Sets.insert i ver)
             nothing → (Sets.empty , Sets.singleton i) ) }
  where
    open Input m
    open Nat using (_+_; _∸_)

add^ : ℕ → ℕ → Input → Input
add^ x y m = record m { carte = forℕ width carte λ i →
   Map.insertWith (x , 1 + ((y + height ∸ i ∸ 1) %% height))
    (λ where (just (hor , ver)) → (hor , Sets.insert i ver)
             nothing → (Sets.empty , Sets.singleton i) ) }
  where
    open Input m
    open Nat using (_+_; _∸_)

readMatrix : Point → List Char → Input → Input
readMatrix (x , y) [] m = m
readMatrix (x , y) ('#' ∷ s) m = readMatrix (suc x , y) s m
readMatrix (x , y) ('.' ∷ s) m = readMatrix (suc x , y) s m
readMatrix (x , y) ('>' ∷ s) m = readMatrix (suc x , y) s (add> x y m)
readMatrix (x , y) ('<' ∷ s) m = readMatrix (suc x , y) s (add< x y m)
readMatrix (x , y) ('^' ∷ s) m = readMatrix (suc x , y) s (add^ x y m)
readMatrix (x , y) ('v' ∷ s) m = readMatrix (suc x , y) s (addv x y m)
readMatrix (x , y) ('\n' ∷ s) m = readMatrix (0 , suc y) s m
readMatrix (x , y) (_ ∷ s) m = m

emptyInput : String → Input
emptyInput s with String.lines s
... | [] = record { width = 0 ; height = 0 ; carte = Map.empty }
... | ls@(l ∷ _) = record { width = w ; height = h
                          ; carte = Map.fromList (((1 , 0) , e2) ∷ ((w , suc h) , e2) ∷ []) }
  where
    open Nat using (_∸_)
    e2 = Sets.empty , Sets.empty
    w = String.length l ∸ 2
    h = List.length ls ∸ 2

readInput : String → Input
readInput s = readMatrix (0 , 0) (String.toList s) (emptyInput s)

example : Input
example = readInput $ String.unlines $
  "#.######" ∷
  "#>>.<^<#" ∷
  "#.<..<<#" ∷
  "#>v.><>#" ∷
  "#<^v^^>#" ∷
  "######.#" ∷
  []

example2 : Input
example2 = readInput $ String.unlines $
  "#.################" ∷
  "#.<<...<<<....<..#" ∷
  "#.<...<<...<<<.<.#" ∷
  "################.#" ∷
  []

{-
_ : take-S 10 (reach example2) ≡ ?
_ = ?
-}

{-
_ : solve-1 example ≡ just 18
_ = refl

_ : solve-2 example ≡ just 54
_ = refl
-}

sol : String → String
sol = show ∘ < solve-1 , solve-2 > ∘ readInput
