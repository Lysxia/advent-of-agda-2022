-- | Utils module
module Night where

open import Level using () renaming (zero to 0ℓ)
import Algebra.Definitions
open import Function.Base using (id; _∘_)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ
open import Data.Integer.Base as ℤ using (ℤ)
import Data.Integer.Show as ℤ
open import Data.Sign.Base as Sign using (Sign)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Effectful as List
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Effectful as Maybe using (applicative)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _≈?_; unlines)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Relation.Nullary using (¬_)
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Reflection

private variable
  A B : Set
  P Q : A → Set

macro
  print : Term → Term → TC ⊤
  print t hole = do
    v <- normalise t
    debugPrint "print" 0 (termErr v ∷ [])
    unify hole (con (quote tt) [])

record Show (a : Set) : Set where
  constructor show:=
  field show : a → String

open Show ⦃...⦄ public

instance
  Show-ℕ : Show ℕ
  Show-ℕ = show:= ℕ.show

  Show-ℤ : Show ℤ
  Show-ℤ = show:= ℤ.show

  Show-Fin : {n : ℕ} → Show (Fin n)
  Show-Fin = show:= (show ∘ Fin.toℕ)

  Show-× : ∀ {a b : Set} → ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (a × b)
  Show-× = show:= λ{ (x , y) → show x String.++ " , " String.++ show y }

  Show-Maybe : {a : Set} → ⦃ Show a ⦄ → Show (Maybe a)
  Show-Maybe = show:= λ where
    nothing → "nothing"
    (just x) → show x

  Show-String : Show String
  Show-String = show:= id

  Show-List : {a : Set} → ⦃ Show a ⦄ → Show (List a)
  Show-List = show:= (String.unwords ∘ List.map show)

open List.TraversableA {0ℓ} Maybe.applicative public
  renaming (mapA to traverse)

readSign : String → Maybe (Sign × String)
readSign s with String.uncons s
... | just ('+' , etc) = just (Sign.+ , etc)
... | just ('-' , etc) = just (Sign.- , etc)
... | _ = nothing

readℤ : String → Maybe ℤ
readℤ s with String.toList s
... | '+' ∷ etc = Maybe.map ℤ.+_ (ℕ.readMaybe 10 (String.fromList etc))
... | '-' ∷ etc = Maybe.map (λ x → ℤ.- (ℤ.+ x)) (ℕ.readMaybe 10 (String.fromList etc))
... | _ = Maybe.map ℤ.+_ (ℕ.readMaybe 10 s)

-- Using String.uncons runs into a GHC bug!!!
-- ... | just ('+' , etc) = Maybe.map ℤ.+_ (ℕ.readMaybe 10 etc)
-- ... | just ('-' , etc) = Maybe.map (λ x → ℤ.- (ℤ.+ x)) (ℕ.readMaybe 10 etc)

_ : readℤ "+3" ≡ just (ℤ.+ 3)
_ = refl

_ : readℤ "-3" ≡ just (ℤ.- (ℤ.+ 3))
_ = refl

record Erased (@0 P : Set) : Set where
  constructor erased
  field
    @0 unerase : P

open Erased public

Erased-map : {@0 A : Set} → {@0 P : A → Set} → (@0 f : (x : A) → P x) →
  (x : Erased A) → Erased (P (unerase x))
Erased-map f (erased x) = erased (f x)

erased-⊥ : @0 ⊥ → ⊥
erased-⊥ ()

≢-proj₂ : {p q : A × B} → proj₂ p ≢ proj₂ q → p ≢ q
≢-proj₂ pp = pp ∘ cong proj₂

≢-proj₁′ : {x x′ : A} {y : B} → (x , y) ≢ (x′ , y) → x ≢ x′
≢-proj₁′ pp = pp ∘ cong (_, _)

module _ {A : Set} where

  _==_ = _≐_ {A = A} {0ℓ} {0ℓ}

  open Algebra.Definitions _==_

  ∩-mono-⊆ : _∩_ {A = A} {0ℓ} {0ℓ} Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_
  ∩-mono-⊆ P⊆ Q⊆ = Prod.map P⊆ Q⊆

  ∪-mono-⊆ : _∪_ {A = A} {0ℓ} {0ℓ} Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_
  ∪-mono-⊆ P⊆ Q⊆ = Sum.map P⊆ Q⊆

  ∪-mono-≐ : _∪_ Preserves₂ _==_ ⟶ _==_ ⟶ _==_
  ∪-mono-≐ P== Q== = Sum.map (proj₁ P==) (proj₁ Q==) , Sum.map (proj₂ P==) (proj₂ Q==)

  ∩-mono-≐ : _∩_ Preserves₂ _==_ ⟶ _==_ ⟶ _==_
  ∩-mono-≐ P== Q== = Prod.map (proj₁ P==) (proj₁ Q==) , Prod.map (proj₂ P==) (proj₂ Q==)

  ∩-distribʳ-∪ : _DistributesOverʳ_ _∩_ _∪_
  ∩-distribʳ-∪ _ _ _ =
    (λ where
      (inj₁ x , y) → inj₁ (x , y)
      (inj₂ x , y) → inj₂ (x , y)
    ) , (λ where
      (inj₁ (x , y)) → inj₁ x , y
      (inj₂ (x , y)) → inj₂ x , y)

  ∩-distribˡ-∪ : _DistributesOverˡ_ _∩_ _∪_
  ∩-distribˡ-∪ _ _ _ =
    (λ where
      (x , inj₁ y) → inj₁ (x , y)
      (x , inj₂ y) → inj₂ (x , y)
    ) , (λ where
      (inj₁ (x , y)) → x , inj₁ y
      (inj₂ (x , y)) → x , inj₂ y)

  ∪-comm : Commutative _∪_
  ∪-comm _ _ = Sum.swap , Sum.swap

  ∪-idem : Idempotent _∪_
  ∪-idem _ = Sum.reduce , inj₁

  ∪-assoc : Associative _∪_
  ∪-assoc _ _ _ = Sum.[ Sum.[ inj₁ , inj₂ ∘ inj₁ ] , inj₂ ∘ inj₂ ] , Sum.[ inj₁ ∘ inj₁ , Sum.[ inj₁ ∘ inj₂ , inj₂ ] ]

⊆-∩ˡ : P ∩ Q ⊆ P
⊆-∩ˡ (Px , _) = Px
