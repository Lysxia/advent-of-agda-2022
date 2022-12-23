{-# OPTIONS --allow-exec #-}
module Day15Core where

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

module ⊆-Reasoning {A : Set} = Reasoning {A = A → Set} (_⊆_ {A = A}) (λ {x} → ⊆-refl {x = x}) (λ {i} → ⊆-trans {i = i})
module ≐-Reasoning {A : Set} = Reasoning {A = A → Set} (_≐_ {A = A}) (λ {x} → ≐-refl {x = x}) (λ {i} → ≐-trans {i = i})

open import SMT.Theories.Ints as Ints using (theory)
open import SMT.Theories.Ints.Extra using (+∣_∣)
open import SMT.Backend.Z3 Ints.theory
  using (solveZ3)

open import Text.Parser

open import Night

private variable
  A B : Set
  i j k l r : ℤ
  P Q : A → Set

instance
  _ : ⊤
  _ = tt
  _ : Number ℕ
  _ = number-ℕ
  _ : Number ℤ
  _ = number-ℤ

Point : Set
Point = ℤ × ℤ

Input : Set
Input = List (Point × Point)

abstract

  parseLine : ∀[ Parser (Point × Point) ]
  parseLine =
    (λ{ (((sx , sy) , bx ) , by) → ((sx , sy) , (bx , by)) }) <$>
    (text "Sensor at x=" &> box decimalℤ
    <& box (text ", y=") <&> box decimalℤ
    <& box (text ": closest beacon is at x=") <&> box decimalℤ
    <& box (text ", y=") <&> box decimalℤ)

  readLine : String → Maybe (Point × Point)
  readLine = Sum.[ (λ _ → nothing) , just ] ∘ runParser parseLine

  readInput : List String → Maybe Input
  readInput = traverse readLine

[_⨟_[ : ℤ → ℤ → ℤ → Set
[ i ⨟ j [ k = i ≤ k × k < j

]-∞⨟_[ : ℤ → ℤ → Set
]-∞⨟ j [ k = k < j

[_⨟+∞[ : ℤ → ℤ → Set
[ i ⨟+∞[ k = i ≤ k


mapUnion : (A → B → Set) → List A → B → Set
mapUnion f = List.foldr (_∪_ ∘ f) ∅

data Merge {A S : Set} (⟦_⟧ : S → A → Set) (s t : S) : Set where
  AreDisjoint : @0 ⟦ t ⟧ ∩ ⟦ s ⟧ ⊆ ∅ → Merge ⟦_⟧ s t
  Merged : (z : S) → @0 ⟦ z ⟧ ≐ ⟦ s ⟧ ∪ ⟦ t ⟧ → Merge ⟦_⟧ s t

record SetLike (A S : Set) : Set₁ where
  field
    ⟦_⟧ : S → A → Set
    merge : (s t : S) → Merge ⟦_⟧ s t

module Interval where
  Interval : Set
  Interval = ℤ × ℤ

  ⟦_⟧ : Interval → ℤ → Set
  ⟦ i , j ⟧ k = i ≤ k × k < j

  private
    variable
      x : ℤ

    lem1 : l < i → x < l → i ≤ x → ⊥
    lem1 = solveZ3

    lem2 : j < k → x < j → k ≤ x → ⊥
    lem2 = solveZ3

    postulate
      @0 lem3 : ⟦ i ⊓ k , j ⊔ l ⟧ ⊆ ⟦ i , j ⟧ ∪ ⟦ k , l ⟧
      @0 lem4 : ⟦ i , j ⟧ ∪ ⟦ k , l ⟧ ⊆ ⟦ i ⊓ k , j ⊔ l ⟧

  merge : (s t : Interval) → Merge ⟦_⟧ s t
  merge (i , j) (k , l) with i ≤? l | k ≤? j
  ... | no i≰l | _ = AreDisjoint (λ{ ((k≤x , x<l) , (i≤x , x<j)) → lem1 (Intₚ.≰⇒> i≰l) x<l i≤x })
  ... | _ | no k≰j = AreDisjoint (λ{ ((k≤x , x<l) , (i≤x , x<j)) → lem2 (Intₚ.≰⇒> k≰j) x<j k≤x })
  ... | yes i≤l | yes k≤j = Merged (i ⊓ k , j ⊔ l) (lem3 , lem4)


  setLike : SetLike ℤ Interval
  setLike = record
    { ⟦_⟧ = ⟦_⟧
    ; merge = merge }

module DU {A S : Set} (SL : SetLike A S) where
  open SetLike SL

  private variable
    s : S
    ss : List S

  Union : List S → A → Set
  Union = List.foldr (_∪_ ∘ ⟦_⟧) ∅

  data Disjoint : List S → Set where
    [] : Disjoint []
    _∷_ : ⟦ s ⟧ ∩ Union ss ⊆ ∅ → Disjoint ss → Disjoint (s ∷ ss)

  record DisjointUnion (P : A → Set) : Set where
    field
      sets : List S
      @0 disjoint : Disjoint sets
      @0 union : Union sets ≐ P

  open DisjointUnion

  insert′ : (s : S) (xs : List S) → @0 Disjoint xs → ∃[ ss ] Erased (Disjoint ss × Union ss ≐ ⟦ s ⟧ ∪ Union xs)
  insert′ s [] _ = s ∷ [] , erased ((λ{ (_ , ()) }) ∷ [] , ≐-refl)
  insert′ s (x ∷ xs) (xd ∷ disjoint) with merge s x
  insert′ s (x ∷ xs) (xd ∷ disjoint) | Merged z z≐ with insert′ z xs disjoint
  ... | ss , erased (disjoint′ , union′) = ss , erased (disjoint′ , f)
    where
      open ≐-Reasoning
      @0 f : Union ss ≐ ⟦ s ⟧ ∪ (⟦ x ⟧ ∪ Union xs)
      f = begin
        Union ss ∼⟨ union′ ⟩
        ⟦ z ⟧ ∪ Union xs ∼⟨ ∪-mono-≐ z≐ ≐-refl ⟩
        (⟦ s ⟧ ∪ ⟦ x ⟧) ∪ Union xs ∼⟨ ∪-assoc ⟦ s ⟧ ⟦ x ⟧ _ ⟩
        ⟦ s ⟧ ∪ (⟦ x ⟧ ∪ Union xs) ∎
  insert′ s (x ∷ xs) (xd ∷ disjoint) | AreDisjoint x∩s⊆∅ with insert′ s xs disjoint
  ... | ss , erased (disjoint′ , union′) = x ∷ ss , erased (e ∷ disjoint′ , g)
    where
      @0 e : ⟦ x ⟧ ∩ Union ss ⊆ ∅
      e = begin
        ⟦ x ⟧ ∩ Union ss ∼⟨ ∩-mono-⊆ {x = ⟦ x ⟧} {u = Union ss} {v = ⟦ s ⟧ ∪ Union xs} (⊆-refl {x = ⟦ x ⟧}) (proj₁ union′) ⟩
        ⟦ x ⟧ ∩ (⟦ s ⟧ ∪ Union xs) ∼⟨ proj₁ (∩-distribˡ-∪ ⟦ x ⟧ ⟦ s ⟧ (Union xs)) ⟩
        ⟦ x ⟧ ∩ ⟦ s ⟧ ∪ ⟦ x ⟧ ∩ Union xs ∼⟨ ∪-mono-⊆ {x = ⟦ x ⟧ ∩ ⟦ s ⟧} {u = ⟦ x ⟧ ∩ Union xs} x∩s⊆∅ xd ⟩
        ∅ ∪ ∅ ∼⟨ Sum.reduce ⟩
        ∅ ∎
        where open ⊆-Reasoning
      @0 g : ⟦ x ⟧ ∪ Union ss ≐ ⟦ s ⟧ ∪ (⟦ x ⟧ ∪ Union xs)
      g = begin
        ⟦ x ⟧ ∪ Union ss ∼⟨ ∪-mono-≐ ≐-refl union′ ⟩
        ⟦ x ⟧ ∪ (⟦ s ⟧ ∪ Union xs) ∼⟨ ≐-sym (∪-assoc _ _ _) ⟩
        (⟦ x ⟧ ∪ ⟦ s ⟧) ∪ Union xs ∼⟨ ∪-mono-≐ (∪-comm _ _) ≐-refl ⟩
        (⟦ s ⟧ ∪ ⟦ x ⟧) ∪ Union xs ∼⟨ ∪-assoc ⟦ s ⟧ ⟦ x ⟧ (Union xs) ⟩
        ⟦ s ⟧ ∪ (⟦ x ⟧ ∪ Union xs) ∎
        where open ≐-Reasoning


  insert : (s : S) → DisjointUnion P → DisjointUnion (⟦ s ⟧ ∪ P)
  insert s du with insert′ s (sets du) (disjoint du)
  ... | sets , erased (disjoint , union′) = record { sets = sets ; disjoint = disjoint ; union = ≐-trans union′ (∪-mono-≐ ≐-refl (union du)) }

  empty : DisjointUnion ∅
  empty = record { sets = [] ; disjoint = [] ; union = ≐-refl }

  map : @0 P ≐ Q → DisjointUnion P → DisjointUnion Q
  map P≐Q du = record { sets = sets du ; disjoint = disjoint du ; union = ≐-trans (union du) P≐Q }

open Interval using (Interval; ⟦_⟧)
open DU Interval.setLike public

L₁² : Point → Point → ℤ
L₁² (x , y) (x′ , y′) = +∣ x - x′ ∣ + +∣ y - y′ ∣

nearby : ℤ → Point × Point → ℤ → Set
nearby y (sensor , beacon) x = L₁² sensor (x , y) ≤ L₁² sensor beacon × (x , y) ≢ beacon

module _ where
  private
    @0 lem1 : ∀ {sx sy bx by x y} →
      +∣ sx - bx ∣ + +∣ sy - by ∣ < +∣ y - sy ∣ →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣ →
      ⊥
    lem1 = solveZ3

    @0 lem2 : ∀ {sx sy bx by x y} →
      let db = +∣ sx - bx ∣ + +∣ sy - by ∣
          dy = +∣ y - sy ∣ in
      (sx - db + dy ≤ x) × (x < sx + db - dy + 1) →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ db
    lem2 w = solveZ3

    @0 lem3 : ∀ {sx sy bx by x y} →
      let db = +∣ sx - bx ∣ + +∣ sy - by ∣
          dy = +∣ y - sy ∣ in
      dy ≤ db →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ db →
      (sx - db + dy ≤ x) × (x < sx + db - dy + 1)
    lem3 h w = solveZ3

    @0 lem4′ : ∀ {sx bx by x y : ℤ} →
      y ≡ by →
      sx ≤ bx →
      sx - (bx - sx) ≤ x × x < bx →
      (x , y) ≡ (bx , by) → ⊥
    lem4′ a b c refl = solveZ3

    @0 lem4 : ∀ {sx sy bx by x y} →
      y ≡ by →
      sx ≤ bx →
      sx - (bx - sx) ≤ x × x < bx →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣
        × ((x , y) ≡ (bx , by) → ⊥)
    lem4 a b c = solveZ3 , lem4′ a b c

    @0 lem5′ : ∀ {sx sy bx by x} →
      sx ≤ bx →
      +∣ sx - x ∣ + +∣ sy - by ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣ →
      x ≢ bx →
      sx - (bx - sx) ≤ x × x < bx
    lem5′ = solveZ3

    @0 lem5 : ∀ {sx sy bx by y x} →
      y ≡ by →
      sx ≤ bx →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣
        × ((x , y) ≡ (bx , by) → ⊥) →
      sx - (bx - sx) ≤ x × x < bx
    lem5 {sx} {sy} refl b (c , d) = lem5′ {sx} {sy} b c (≢-proj₁′ d)

    @0 lem6 : ∀ {sx sy bx by x y} →
      y ≡ by →
      bx < sx →
      bx + 1 ≤ x × x < sx + (sx - bx) + 1 →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣
        × ((x , y) ≡ (bx , by) → ⊥)
    lem6 {sx} a b c = solveZ3 , λ{ refl → solveZ3 }

    @0 lem7′ : ∀ {sx sy bx by x} →
      bx < sx →
      +∣ sx - x ∣ + +∣ sy - by ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣ →
      x ≢ bx →
      bx + 1 ≤ x × x < sx + (sx - bx) + 1
    lem7′ = solveZ3

    @0 lem7 : ∀ {sx sy bx by x y} →
      y ≡ by →
      bx < sx →
      +∣ sx - x ∣ + +∣ sy - y ∣ ≤ +∣ sx - bx ∣ + +∣ sy - by ∣
        × ((x , y) ≡ (bx , by) → ⊥) →
      bx + 1 ≤ x × x < sx + (sx - bx) + 1
    lem7 {sx} {sy} refl b (c , d) = lem7′ {sx} {sy} b c (≢-proj₁′ d)

  nearby-interval : (y : ℤ) → (sb : Point × Point) → nearby y sb ⊆ ∅ ⊎ Σ[ (xmin , xmax) ∈ Interval ] Erased (⟦ xmin , xmax ⟧ ≐ nearby y sb)
  nearby-interval y (sensor@(sx , sy) , beacon@(bx , by)) with y ≟ by
  ... | no y≢by =
    let db = L₁² sensor beacon
        dy = +∣ y - sy ∣ in
    case dy ≤? db of λ where
      (yes dy≤db) → inj₂ ((sx - db + dy , sx + db - dy + 1) , erased ((λ {x : ℤ} w → lem2 {sx} {sy} w , ≢-proj₂ y≢by) , (λ {x : ℤ} → lem3 {sx} {sy} dy≤db ∘ proj₁)))
      (no  dy≰db) → inj₁ λ {x : ℤ} (w , _) → erased-⊥ (lem1 {sx} {sy} (Intₚ.≰⇒> dy≰db) w)
  ... | yes y≡by with sx ≤? bx
  ...            | yes sx≤bx = inj₂ ((sx - (bx - sx) , bx) , erased (lem4 {sx} {sy} y≡by sx≤bx , lem5 {sx} {sy} y≡by sx≤bx))
  ...            | no  sx≰bx = inj₂ ((bx + 1 , sx + (sx - bx) + 1) , erased (lem6 {sx} {sy} y≡by bx<sx , lem7 {sx} {sy} y≡by bx<sx))
    where bx<sx = Intₚ.≰⇒> sx≰bx

disjoint-union : (y : ℤ) → (pts : Input) → DisjointUnion (mapUnion (nearby y) pts)
disjoint-union y [] = empty
disjoint-union y (sb ∷ pts) with nearby-interval y sb
... | inj₁ nby⊆∅ = map (lemma nby⊆∅) (disjoint-union y pts)
  where
    @0 lemma : (P ⊆ ∅) → Q ≐ P ∪ Q
    lemma ⊆∅ = inj₂ , Sum.[ ⊥-elim ∘ ⊆∅ , id ]
... | inj₂ (s , erased s≐nby) = map (lemma s≐nby) (insert s (disjoint-union y pts))
  where
    @0 lemma : ∀ {P′ : A → Set} → P ≐ P′ → P ∪ Q ≐ P′ ∪ Q
    lemma P≐ = ∪-mono-≐ P≐ ≐-refl

disjointSize : DisjointUnion P → ℕ
disjointSize = List.sum ∘ List.map intervalLength ∘ sets
  where
    open DisjointUnion using (sets)
    intervalLength = λ{ (i , j) → ∣ i - j ∣ }
