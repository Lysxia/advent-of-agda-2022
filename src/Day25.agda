{-# OPTIONS --allow-exec #-}
module Day25 where

open import Agda.Builtin.FromNat using (Number; fromNat)
open import Function.Base using (_$_; _∘_; _on_; case_of_)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Integer.Base as Int using (ℤ; ∣_∣)
open import Data.Integer.Properties
import Data.Integer.DivMod
open import Data.Integer.Literals renaming (number to number-ℤ; negative to negative-ℤ)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Unit.Base using (⊤; tt)
open import Induction.WellFounded as WF using (WellFounded; Acc; acc)
open import Data.Product as Prod using (∃-syntax; _×_; _,_)
open import Data.Char.Base as Char using (Char)
open import Data.String.Base as String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
import Relation.Binary.Construct.On as On

open import SMT.Theories.Ints as Ints using (theory)
open import SMT.Theories.Ints.Extra using (+∣_∣)
open import SMT.Backend.Z3 Ints.theory
  using (solveZ3)

open import Night

instance
  _ = tt
  _ = number-ℤ
  _ = negative-ℤ

private variable
  i j k : ℤ

data Digit : Set where
  `= `- `0 `1 `2 : Digit

SNAFU : Set
SNAFU = List Digit

module _ where
  open Nat using (z≤n; s≤s)
  open Int
  open Data.Integer.DivMod

  @0 quot-decr : ∀ n q r → n ≢ 0 → n ≡ q * 5 + r → -2 ≤ r → r ≤ 2 → +∣ q ∣ < +∣ n ∣
  quot-decr = solveZ3

  wf-abs : WellFounded (Nat._<_ on ∣_∣)
  wf-abs = On.wellFounded ∣_∣ <-wellFounded

  wf-ℤ : WellFounded (_<_ on +∣_∣)
  wf-ℤ = WF.Subrelation.wellFounded drop‿+<+ wf-abs

  to-Digit : ℤ → Digit
  to-Digit (+ 0) = `0
  to-Digit (+ 1) = `1
  to-Digit (+ 2) = `2
  to-Digit -[1+ 0 ] = `-
  to-Digit _ = `=

  from-Digit : Digit → ℤ
  from-Digit `= = -2
  from-Digit `- = -1
  from-Digit `0 = 0
  from-Digit `1 = 1
  from-Digit `2 = 2

  to-from-Digit : (d : Digit) → to-Digit (from-Digit d) ≡ d
  to-from-Digit `= = refl
  to-from-Digit `- = refl
  to-from-Digit `0 = refl
  to-from-Digit `1 = refl
  to-from-Digit `2 = refl

  from-to-Digit : (d : ℤ) → @0 -2 ≤ d → @0 d ≤ 2 → from-Digit (to-Digit d) ≡ d
  from-to-Digit (+ 0) -≤+ (+≤+ z≤n) = refl
  from-to-Digit (+ 1) -≤+ (+≤+ (s≤s z≤n)) = refl
  from-to-Digit (+ 2) -≤+ (+≤+ (s≤s (s≤s z≤n))) = refl
  from-to-Digit -[1+ 0 ] (-≤- z≤n) -≤+ = refl
  from-to-Digit -[1+ 1 ] (-≤- (s≤s z≤n)) -≤+ = refl

  @0 lem1 : (n q r : ℤ) → n + 2 ≡ r + q * 5 → n ≡ q * 5 + (r - 2)
  lem1 = solveZ3

  @0 lem2 : (r : ℤ) → 0 ≤ r → -2 ≤ r - 2
  lem2 = solveZ3

  @0 lem3 : (r : ℤ) → r < 5 → r - 2 ≤ 2
  lem3 = solveZ3

  qr : (n : ℤ) → ∃[ q ] ∃[ r ] Erased (n ≡ q * 5 + r × -2 ≤ r × r ≤ 2)
  qr n with (n + 2) % 5 | (n + 2) / 5 | erased (a≡a%n+[a/n]*n (n + 2) 5) | erased (n%d<d (n + 2) 5)
  ... | r | q | erased n≡ | erased %5<5 = q , + r - 2 , erased (lem1 n q (+ r) n≡ , lem2 (+ r) (+≤+ z≤n) , lem3 (+ r) (+<+ %5<5))

  to-SNAFU-loop : (i : ℤ) → @0 Acc (_<_ on +∣_∣) i → SNAFU
  to-SNAFU-loop n (acc rec) with n ≟ 0 | qr n
  ... | yes n≡0 | _ = []
  ... | no  n≢0 | q , r , abc
      = to-Digit r ∷ to-SNAFU-loop q (
          let erased (n≡q*5+r , -2≤r , r≤2) = abc
          in rec q (quot-decr n q r n≢0 n≡q*5+r -2≤r r≤2))

  to-SNAFU : ℤ → SNAFU
  to-SNAFU n = to-SNAFU-loop n (wf-ℤ n)

  from-SNAFU : SNAFU → ℤ
  from-SNAFU [] = 0
  from-SNAFU (d ∷ n) = from-SNAFU n * 5 + from-Digit d

  @0 from-to-SNAFU-loop : (n : ℤ) → (@0 a : Acc (_<_ on +∣_∣) n) → from-SNAFU (to-SNAFU-loop n a) ≡ n
  from-to-SNAFU-loop n (acc rec) with n ≟ 0 | qr n
  ... | yes refl | _ = refl
  ... | no  n≢0  | q , r , erased (n≡q*5+r , -2≤r , r≤2)
      rewrite from-to-SNAFU-loop q (rec q (quot-decr n q r n≢0 n≡q*5+r -2≤r r≤2))
      rewrite from-to-Digit r -2≤r r≤2
      = sym n≡q*5+r

  @0 from-to-SNAFU : (n : ℤ) → from-SNAFU (to-SNAFU n) ≡ n
  from-to-SNAFU n = from-to-SNAFU-loop n (wf-ℤ n)

Input : Set
Input = List SNAFU

charToDigit : Char → Digit
charToDigit '0' = `0
charToDigit '1' = `1
charToDigit '2' = `2
charToDigit '-' = `-
charToDigit _ = `=

readSNAFU : String → SNAFU
readSNAFU = List.reverse ∘ List.map charToDigit ∘ String.toList

readInput : String → Input
readInput = List.map readSNAFU ∘ String.lines

example : Input
example = readInput $ String.unlines $
  "1=-0-2" ∷
  "12111" ∷
  "2=0=" ∷
  "21" ∷
  "2=01" ∷
  "111" ∷
  "20012" ∷
  "112" ∷
  "1=-1=" ∷
  "1-12" ∷
  "12" ∷
  "1=" ∷
  "122" ∷
  []

digitToChar : Digit → Char
digitToChar `0 = '0'
digitToChar `1 = '1'
digitToChar `2 = '2'
digitToChar `- = '-'
digitToChar `= = '='

show-SNAFU : SNAFU → String
show-SNAFU [] = "0"
show-SNAFU s@(_ ∷ _) = String.fromList (List.map digitToChar (List.reverse s))

solve-1 : Input → SNAFU
solve-1 = to-SNAFU ∘ List.foldr _+_ 0 ∘ List.map from-SNAFU
  where open Int

_ : show-SNAFU (solve-1 example) ≡ "2=-1=0"
_ = refl

sol : String → String
sol = show-SNAFU ∘ solve-1 ∘ readInput
