-- | Utils module
module Night where

open import Level using () renaming (zero to 0ℓ)
open import Function.Base using (id; _∘_)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ
open import Data.Integer.Base as ℤ using (ℤ)
import Data.Integer.Show as ℤ
open import Data.Sign.Base as Sign using (Sign)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Effectful as List
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Effectful as Maybe using (applicative)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; _≈?_; unlines)
open import Data.Unit
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection

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
readℤ s with readSign s
... | just (s , etc) = Maybe.map (s ℤ.◃_) (ℕ.readMaybe 10 etc)
... | nothing = Maybe.map ℤ.+_ (ℕ.readMaybe 10 s)

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
