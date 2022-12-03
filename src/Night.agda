-- | Utils module
module Night where

open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; _≈?_)
open import Data.Unit
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

  Show-× : ∀ {a b : Set} → ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (a × b)
  Show-× = show:= λ{ (x , y) → show x String.++ " , " String.++ show y }

  Show-Maybe : {a : Set} → ⦃ Show a ⦄ → Show (Maybe a)
  Show-Maybe = show:= λ where
    nothing → "nothing"
    (just x) → show x
