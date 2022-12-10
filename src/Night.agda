-- | Utils module
module Night where

open import Function.Base using (id; _∘_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as ℕ
open import Data.Integer.Base using (ℤ)
import Data.Integer.Show as ℤ
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; _≈?_; unlines)
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

  Show-ℤ : Show ℤ
  Show-ℤ = show:= ℤ.show

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
