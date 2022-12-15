-- Graph algorithms
module Graffiti where

open import Level using () renaming (zero to 0ℓ)
open import Function.Base using (_∘_; id; flip; case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _<_)
open import Data.Irrelevant
open import Data.Fin.Base as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Binary.Subset.Propositional.Properties as List
open import Data.Product as Prod using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)
import Data.Tree.AVL.Sets as Sets
import Data.Tree.AVL.Sets.Membership as SetsMembership
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded
open import Relation.Nullary using (¬_; Dec; yes; no; _because_)
open import Relation.Unary as R1 using (Pred; _∪_; _⊆_; _≐_)
open import Relation.Unary.Algebra
open import Relation.Unary.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.Bundles
open import Relation.Binary.Structures

open import Night using (Erased; erased; unerase; Erased-map)

private variable
  A B : Set
  P Q : A → Set
  n : ℕ

Injective : {A B : Set} → (f : A → B) → Set
Injective {A} f = (x y : A) → f x ≡ f y → x ≡ y

_↪_ : Set → Set → Set
A ↪ B = Σ[ f ∈ (A → B) ] Injective f

Enum : ℕ → Set → Set
Enum n A = A ↪ Fin n

record Finite (A : Set) : Set where
  constructor _,_
  field
    card⁺ : ℕ  -- this is an overapproximation of the actual cardinality
    enum : Enum card⁺ A

open Finite

Subset : (A → Set) → Set
Subset P = ∃[ x ] Irrelevant (P x)

IsCofiniteSubset : (A → Set) → Set
IsCofiniteSubset P = Finite (Subset (¬_ ∘ P))

Coenum : ℕ → (A → Set) → Set
Coenum n P = Enum n (Subset (¬_ ∘ P))

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to∘from : ∀ x → (to ∘ from) x ≡ x
    from∘to : ∀ x → (from ∘ to) x ≡ x

infix 3 _⊂_ _⊃_

_⊂_ : (_ _ : A → Set) → Set
P ⊂ Q = P ⊆ Q × ∃[ x ] Q x × ¬ P x

_⊃_ : (_ _ : A → Set) → Set
_⊃_ = flip _⊂_

cong-irr-proj₂ : {x y : ∃[ x ] Irrelevant (P x)} → proj₁ x ≡ proj₁ y → x ≡ y
cong-irr-proj₂ refl = refl

irr-⊥ : .⊥ → ⊥
irr-⊥ ()

erased-⊥ : @0 ⊥ → ⊥
erased-⊥ ()

@0 with-erased : {@0 A : Set} → {@0 P : A → Set} → (x : Erased A) → (@0 _ : (x : A) → P x) → P (unerase x)
with-erased x f = f (unerase x)

@0 erased-fun : {@0 A : Set} → {@0 P : A → Set} → (@0 _ : (x : A) → Erased (P x)) → (x : A) → P x
erased-fun f x = unerase (f x)

_Erased->>=_ : {@0 A B : Set} → (x : Erased A) → (@0 f : A → Erased B) → Erased B
x Erased->>= f = erased (unerase (f (unerase x)))

Erased-<&> : {@0 A B : Set} → (x : Erased A) → (@0 f : A → B) → Erased B
Erased-<&> (erased x) f = erased (f x)

module _ (Cof-P : IsCofiniteSubset P) (P⊂Q@(P⊆Q , x0 , Qx0 , ¬Px0) : P ⊂ Q) where

  i0 : Fin (card⁺ Cof-P)
  i0 = proj₁ (enum Cof-P) (x0 , [ ¬Px0 ])

  private

    fin-NonZero : Fin n → Nat.NonZero n
    fin-NonZero zero = Nat.nonZero
    fin-NonZero (suc i) = Nat.nonZero

    fin-delete : (i j : Fin n) → i ≢ j → Fin (Nat.pred n)
    fin-delete i j with Nat.NonZero.nonZero (fin-NonZero i)
    fin-delete {suc _} i j | _ = Fin.punchOut

    module _ ((f , injective-f) : Subset (¬_ ∘ P) ↪ Fin (suc n)) where

      private
        toP : Subset (¬_ ∘ Q) → Subset (¬_ ∘ P)
        toP (x , [ ¬Qx ]) = (x , [ ¬Qx ∘ P⊆Q ])

        x0≢toP : ∀ x → x0 ≢ proj₁ (toP x)
        x0≢toP (x , [ ¬Qx ]) refl = irr-⊥ (¬Qx Qx0)

        fx0≢ftoP : ∀ x → f (x0 , [ ¬Px0 ]) ≢ f (toP x)
        fx0≢ftoP x = x0≢toP x ∘ cong proj₁ ∘ injective-f _ _

      fin-remove : Subset (¬_ ∘ Q) ↪ Fin n
      fin-remove
        = Fin.punchOut ∘ fx0≢ftoP
        , λ x y fx≡fy → cong-irr-proj₂ (cong proj₁
            (injective-f _ _ (Fin.punchOut-injective (fx0≢ftoP x) (fx0≢ftoP y) fx≡fy)))

  enum-Cof-⊂ : Subset (¬_ ∘ Q) ↪ Fin (Nat.pred (Cof-P .card⁺))
  enum-Cof-⊂ with Cof-P .card⁺ | fin-NonZero i0 | enum Cof-P
  ... | suc _ | _ | f = fin-remove f

  Cof-⊂ : IsCofiniteSubset Q
  Cof-⊂ = λ where
    .card⁺ → Nat.pred (Cof-P .card⁺)
    .enum → enum-Cof-⊂


Acc-⊃-Cof : {n : ℕ} → Coenum n P → WfRec {A = A → Set} _⊃_ (Acc _⊃_) P
Acc-⊃-Cof {n = n} coenum Q P⊂Q with i0 (n , coenum) P⊂Q
Acc-⊃-Cof {n = suc n} coenum Q P⊂Q | _ = acc (Acc-⊃-Cof {n = n} (enum-Cof-⊂ (suc n , coenum) P⊂Q))

coenum-∅ : (FA : Finite A) → Coenum {A = A} (card⁺ FA) R1.∅
coenum-∅ (_ , f , injective-f) = (f ∘ proj₁) , λ _ _ → cong-irr-proj₂ ∘ injective-f _ _

Acc-⊃-∅ : Finite A → Acc {A = A → Set} _⊃_ R1.∅
Acc-⊃-∅ finite = acc (Acc-⊃-Cof (coenum-∅ finite))

-- * Finite sets

record Ensembles (A : Set) : Set₁ where
  field
    Ensemble : @0 (A → Set) → Set
    ∅ : Ensemble R1.∅
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

  uniq : {@0 Visited : Vertex → Set} →
    Ensemble Visited → (pending : List Vertex) → Uniq Visited pending
  uniq visited [] = mk-uniq [] (ext assoc visited) (λ()) id
    where
      @0 assoc : ∀ {A} → A ≐ A ∪ (_∈ [])
      assoc = inj₁ , Sum.[ id , (λ()) ]
  uniq {Visited} visited (x ∷ xs) with x ∈? visited | uniq  (insert x visited) xs
  ... | yes x∈Visited | mk-uniq list ens fresh old =
        mk-uniq list (ext (∪-cong redundant ≐-refl) ens)
          (fresh ∘ Any.map inj₂)
          (there ∘ old)
    where
      @0 redundant : (x ≡_) ∪ Visited ≐ Visited
      redundant = unerase (Erased-<&> x∈Visited λ x∈Visited → Sum.[ (λ{ refl → x∈Visited }) , id ] , inj₂)
  ... | no ¬x∈Visited | mk-uniq list ens fresh old =
        mk-uniq (x ∷ list) (ext assoc ens)
          (Sum.[ (λ x → ¬x∈Visited (erased x)) , fresh ∘ Any.map inj₂ ] ∘ Any.toSum)
          (List.∷⁺ʳ _ old)
    where
      @0 assoc : ((x ≡_) ∪ Visited) ∪ (_∈ list) ≐ Visited ∪ (_∈ x ∷ list)
      assoc .proj₁ = Sum.[ Sum.[ (λ{ refl → inj₂ (here refl) }) , inj₁ ] , inj₂ ∘ there ]
      assoc .proj₂ = Sum.[ inj₁ ∘ inj₂ , Sum.[ (λ{ refl → inj₁ (inj₁ refl) })  , inj₂ ] ∘ Any.toSum ]

  bfs-from : ∀ {@0 Visited} → Ensemble Visited → List Vertex → @0 Acc _⊃_ Visited → List (List Vertex)
  bfs-from {Visited} visited roots (acc rec) with uniq visited (List.concatMap neighbors roots)
  ... | mk-uniq [] visited' fresh old = []
  ... | mk-uniq unvisited@(_ ∷ _) visited′ fresh old =
        unvisited ∷ bfs-from visited′ unvisited (rec (Visited ∪ (_∈ unvisited)) (oblig (fresh ∘ here)))
    where
      oblig : ∀ {P x xs} → ¬ P x → P ∪ (_∈ x ∷ xs) ⊃ P
      oblig ¬Px = inj₁ , _ , inj₂ (here refl) , ¬Px

  bfs : Vertex → List (List Vertex)
  bfs x = (x ∷ []) ∷ bfs-from ∅ (x ∷ []) (Acc-⊃-∅ Finite-Vertex)

module AVL {A : Set} {_<_ : A → A → Set} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where
  STO : StrictTotalOrder _ _ _
  STO = record { isStrictTotalOrder = isStrictTotalOrder }

  open StrictTotalOrder STO
  module S where
    open Sets STO public
    open SetsMembership STO public

  private module Ensembles-AVL-impl where

    record Ensemble (@0 P : A → Set) : Set where
      constructor _,_
      field
        set : S.⟨Set⟩
        @0 set≐P : (S._∈ set) ≐ P

    ∅ : Ensemble R1.∅
    ∅ = S.empty , ⊥-elim ∘ S.∈-empty , λ()

    Dec-∈ : ∀ x s → Dec (x S.∈ s)
    Dec-∈ x s = _ because S.∈?-Reflects-∈

    _∈?_ : ∀ {@0 P} → (x : A) → Ensemble P → Dec (Erased (P x))
    x ∈? (s , toP , fromP) with Dec-∈ x s
    ... | yes sx = yes (erased (toP sx))
    ... | no ¬sx = no (λ{ (erased Px) → erased-⊥ (¬sx (fromP Px)) })

    insert : ∀ {@0 P} → (x : A) → Ensemble P → Ensemble ((x ≡_) ∪ P)
    insert x (s , s≐P)
      = S.insert x s , Sum.map sym (proj₁ s≐P) ∘ S.∈-insert⁻
      , unerase (Erased-<&> (erased s≐P) λ s≐P → λ where
          (inj₁ refl) → S.∈-insert⁺⁺
          (inj₂ Px) → S.∈-insert⁺ (proj₂ s≐P Px))

    ext : ∀ {@0 P Q} → @0 P ≐ Q → Ensemble P → Ensemble Q
    ext P≐Q (s , s≐P) = s , ≐-trans s≐P P≐Q

  Ensembles-AVL : Ensembles A
  Ensembles-AVL = record { Ensembles-AVL-impl }
