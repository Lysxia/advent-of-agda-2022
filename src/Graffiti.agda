-- Graph algorithms
module Graffiti where

open import Function.Base using (_∘_; id; case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _<_)
open import Data.Irrelevant
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Binary.Subset.Propositional.Properties as List
open import Data.Product as Prod using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred; _∪_; _⊆_; _≐_)
open import Relation.Unary.Algebra
open import Relation.Unary.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Night using (Erased; erased; unerase; Erased-map)

private variable
  A B : Set
  P Q : A → Set

Injective : {A B : Set} → (f : A → B) → Set
Injective {A} f = (x y : A) → f x ≡ f y → x ≡ y

record Finite (A : Set) : Set where
  field
    card⁺ : ℕ  -- this is an overapproximation of the actual cardinality
    coenum : A → Fin card⁺
    injective-coenum : Injective coenum

open Finite

Subset : (A → Set) → Set
Subset P = ∃[ x ] Irrelevant (¬ P x)

IsCofiniteSubset : {A : Set} → (A → Set) → Set
IsCofiniteSubset P = Finite (Subset (¬_ ∘ P))

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to∘from : ∀ x → (to ∘ from) x ≡ x
    from∘to : ∀ x → (from ∘ to) x ≡ x

infix 3 _⟷_

_⟷_ : (_ _ : A → Set) → Set
P ⟷ Q = Subset P ↔ Subset Q

⟷-≐ : P ⟷ Q → P ≐ Q
⟷-≐ f = ? , ?

Cof-ext : P ⟷ Q → IsCofiniteSubset P → IsCofiniteSubset Q
Cof-ext f Cof-P = λ where
  .card⁺ → Cof-P .card⁺
  .coenum → ?
  .injective-coenum → ?

record Ensembles (A : Set) : Set₁ where
  field
    Ensemble : @0 (A → Set) → Set
    ∅ : Ensemble (λ _ → ⊥)
    _∈?_ : ∀ {@0 P} → (x : A) → Ensemble P → Dec (Erased (P x))
    insert : ∀ {@0 P} → (x : A) → Ensemble P → Ensemble ((x ≡_) ∪ P)
    ext : ∀ {@0 P Q} → @0 P ≐ Q → Ensemble P → Ensemble Q

record SimpleGraph : Set₁ where
  field
    Vertex : Set
    @0 Finite-Vertex : Finite Vertex

    neighbors : Vertex → List Vertex

module SimleGraphTheory (G : SimpleGraph) (E : Ensembles (SimpleGraph.Vertex G)) where
  open SimpleGraph G
  open Ensembles E

  Edge : Vertex → Vertex → Set
  Edge v w = w ∈ neighbors v

  private
    Cof = IsCofiniteSubset

  data Uniq (V0 : Vertex → Set) (pending : List Vertex) : Set where
    mk-uniq :
      (list : List Vertex) →
      (ens : Ensemble (V0 ∪ (_∈ list))) →
      @0 ¬ Any V0 list →
      @0 (_∈ list) ⊆ (_∈ pending) →
      Uniq V0 pending

  @0 with-erased : {@0 A : Set} → {@0 P : A → Set} → (x : Erased A) → (@0 _ : (x : A) → P x) → P (unerase x)
  with-erased x f = f (unerase x)

  @0 erased-fun : {@0 A : Set} → {@0 P : A → Set} → (@0 _ : (x : A) → Erased (P x)) → (x : A) → P x
  erased-fun f x = unerase (f x)

  uniq : {@0 Visited : Vertex → Set} →
    Ensemble Visited → (pending : List Vertex) → Uniq Visited pending
  uniq visited [] = mk-uniq [] (ext assoc visited) (λ()) id
    where
      @0 assoc : ∀ {A} → A ≐ A ∪ (_∈ [])
      assoc = ?
  uniq {Visited} visited (x ∷ xs) with x ∈? visited | uniq  (insert x visited) xs
  ... | yes x∈Visited | mk-uniq list ens fresh old =
        mk-uniq list (ext (∪-cong redundant ≐-refl) ens)
          (fresh ∘ Any.map inj₂)
          (there ∘ old)
    where
      @0 redundant : (x ≡_) ∪ Visited ≐ Visited
      redundant = ?
  ... | no ¬x∈Visited | mk-uniq list ens fresh old =
        mk-uniq (x ∷ list) (ext assoc ens)
          (Sum.[ (λ x → ¬x∈Visited (erased x)) , fresh ∘ Any.map inj₂ ] ∘ Any.toSum)
          (List.∷⁺ʳ _ old)
    where
      @0 assoc : ((x ≡_) ∪ Visited) ∪ (_∈ list) ≐ Visited ∪ (_∈ x ∷ list)
      assoc = ?

  infix 3 _⊃_
  _⊃_ : (_ _ : A → Set) → Set
  P ⊃ Q = Q ⊆ P × ∃[ x ] P x × ¬ Q x

  bfs-from : ∀ {@0 Visited} → Ensemble Visited → List Vertex → @0 Acc _⊃_ Visited → List (List Vertex)
  bfs-from {Visited} visited roots (acc rec) with uniq visited (List.concatMap neighbors roots)
  ... | mk-uniq [] visited' fresh old = []
  ... | mk-uniq unvisited@(_ ∷ _) visited′ fresh old =
        unvisited ∷ bfs-from visited′ unvisited (rec (Visited ∪ (_∈ unvisited)) (oblig (fresh ∘ here)))
    where
      oblig : ∀ {P x xs} → ¬ P x → P ∪ (_∈ x ∷ xs) ⊃ P
      oblig ¬Px = inj₁ , _ , inj₂ (here refl) , ¬Px

  WellFounded-⊃ : WellFounded {A = A → Set} _⊃_
  WellFounded-⊃ = ?

  bfs : Vertex → List (List Vertex)
  bfs x = (x ∷ []) ∷ bfs-from ∅ (x ∷ []) (WellFounded-⊃ (λ _ → ⊥))
