-- Graph algorithms
module Graffiti where

open import Level using () renaming (zero to 0ℓ)
open import Function.Base using (_∘_; id; flip; case_of_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat as Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties as Nat
open import Data.Irrelevant
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Binary.Subset.Propositional.Properties as List
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product as Prod using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
import Data.Tree.AVL.Sets as Sets
import Data.Tree.AVL.Sets.Membership as SetsMembership
import Data.Tree.AVL.Sets.Membership.Properties as Sets∈ₚ
import Data.Tree.AVL.Map as Map
import Data.Tree.AVL.Map.Membership.Propositional as MapsMembership
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded
open import Relation.Nullary using (¬_; Dec; yes; no; _because_)
open import Relation.Unary as R1 using (Pred; _∪_; _⊆_; _≐_)
open import Relation.Unary.Algebra
open import Relation.Unary.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.Bundles
open import Relation.Binary.Structures

open import Night using (Erased; erased; unerase; Erased-map; erased-⊥)

private variable
  A B : Set
  P Q : A → Set
  n m : ℕ

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

module SimpleGraphTheory (G : SimpleGraph) (E : Ensembles (SimpleGraph.Vertex G)) where
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
    open Sets∈ₚ STO public

  private module Ensembles-AVL-impl where

    record Ensemble (@0 P : A → Set) : Set where
      constructor _,_
      field
        set : S.⟨Set⟩
        @0 set≐P : (S._∈ set) ≐ P

    ∅ : Ensemble R1.∅
    ∅ = S.empty , ⊥-elim ∘ S.∈-empty , λ()

    Dec-∈ : ∀ x s → Dec (x S.∈ s)
    Dec-∈ x s = _ because S.member-Reflects-∈

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

module Grid where

  module _ (n m : ℕ) where

    Point : Set
    Point = ℕ × ℕ

    Grid : Set → Set
    Grid A = Vec (Vec A m) n

  toRow : List A → Maybe (Vec A n)
  toRow {n = zero} [] = just []
  toRow {n = suc n} (x ∷ xs) = Maybe.map (x ∷_) (toRow xs)
  toRow _ = nothing

  toGrid′ : List (List A) → Maybe (∃[ n ] Grid n m A)
  toGrid′ [] = just (0 , [])
  toGrid′ (row ∷ rows) = Maybe.zipWith (λ{ row′ (n , rows′) → suc n , row′ ∷ rows′ }) (toRow row) (toGrid′ rows)

  toGrid : List (List A) → Maybe (∃[ n ] ∃[ m ] Grid n m A)
  toGrid [] = just (0 , 0 , [])
  toGrid (row ∷ rows) = Maybe.map (λ{ (n , rows′) → suc n , _ , row′ ∷ rows′ }) (toGrid′ rows)
    where row′ = Vec.fromList row

module NatMap where
  
  open Map Nat.<-strictTotalOrder public

module Nat2Map where

  STO : StrictTotalOrder _ _ _
  STO = ×-strictTotalOrder Nat.<-strictTotalOrder Nat.<-strictTotalOrder

  open StrictTotalOrder STO public renaming (_<_ to _<²_)

  open Map STO public

module Griddy where
  open Nat2Map public

  foldli : (ℕ → A → B → A) → A → List B → A
  foldli {A = A} {B = B} f = go 0
    where
      go : ℕ → A → List B → A
      go i x [] = x
      go i x (y ∷ ys) = go (suc i) (f i x y) ys

  to2D : List (List A) → Map A
  to2D =
    flip foldli empty λ i m →
    flip foldli m λ j m cell →
    insert (i , j) cell m

  Point : ℕ → ℕ → Set
  Point n m = Σ[ (i , j) ∈ ℕ × ℕ ] i Nat.<″ n × j Nat.<″ m

  toPoint : ℕ × ℕ → Maybe (Point n m)
  toPoint {n} {m} (i , j) with i Nat.<″? n | j Nat.<″? m
  ... | yes i<n | yes j<m = just ((i , j) , i<n , j<m)
  ... | _ | _ = nothing

  four-neighbors-Point : Point n m → List (Point n m)
  four-neighbors-Point ((i , j) , _) =
    let z2 = (suc i , j) ∷ (i , suc j) ∷ []
        z3 = case i of λ where
          (suc i′) → (i′ , j) ∷ z2
          zero → z2
        z4 = case j of λ where
          (suc j′) → (i , j′) ∷ z3
          zero → z3
    in List.mapMaybe toPoint z4

  four-neighbors : (A → A → Bool) → Map A → Point n m → List (Point n m)
  four-neighbors {n = n} {m = m} edge g p with lookup g (proj₁ p)
  ... | nothing = []
  ... | just x = let f = λ (q : Point n m) → case lookup g (proj₁ q) of λ where
                       nothing → false
                       (just y) → edge x y
                 in List.filterᵇ f (four-neighbors-Point p)

  fromℕ-injective : ∀ {i j} {i<n : i Nat.<″ n} {j<n : j Nat.<″ n} → Fin.fromℕ<″ i i<n ≡ Fin.fromℕ<″ j j<n → i ≡ j
  fromℕ-injective {i = i} {j = j} {i<n} {j<n} ff = begin
    i ≡⟨ sym (Fin.toℕ-fromℕ<″ i<n) ⟩
    Fin.toℕ (Fin.fromℕ<″ i i<n) ≡⟨ cong Fin.toℕ ff ⟩
    Fin.toℕ (Fin.fromℕ<″ j j<n) ≡⟨ Fin.toℕ-fromℕ<″ j<n ⟩
    j ∎
    where open ≡-Reasoning

  Point-point : ∀ {p@(q , _) p′@(q′ , _) : Point n m} → q ≡ q′ → p ≡ p′
  Point-point {_} {_} {(q , _)} {(.q , _)} refl = cong (q ,_) (cong₂ _,_ (Nat.<″-irrelevant _ _) (Nat.<″-irrelevant _ _))

  Finite-Point : Finite (Point n m)
  Finite-Point {n} {m} = (n Nat.* m) , (f , inject)
    where
      f : Point n m → Fin (n Nat.* m)
      f ((i , j) , i<n , j<m) = Fin.combine (Fin.fromℕ<″ i i<n) (Fin.fromℕ<″ j j<m)

      inject : Injective f
      inject ((i , j) , i<n , j<m) ((i′ , j′) , i′<n , j′<m) fx≡fy =
        let ff , gg = Fin.combine-injective (Fin.fromℕ<″ i i<n) _ _ _ fx≡fy
        in Point-point (cong₂ _,_ (fromℕ-injective ff) (fromℕ-injective gg))

  lengthHead : List (List A) → ℕ
  lengthHead = λ{ [] → 0 ; (x ∷ _) → List.length x }

  module Graph {A : Set} (matrix : List (List A)) (edge : A → A → Bool) where
    nRows : ℕ
    nRows = List.length matrix

    nCols : ℕ
    nCols = lengthHead matrix

    vertexMap : Map A
    vertexMap = to2D matrix

    graph : SimpleGraph
    graph = record
      { Vertex = Point nRows nCols
      ; Finite-Vertex = Finite-Point
      ; neighbors = four-neighbors edge vertexMap
      }
