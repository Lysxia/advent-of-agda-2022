module Day10 where

open import Agda.Builtin.FromNat using (Number; fromNat)
open import Function.Base using (_$_; _∘_; case_of_)
open import Data.Integer.Base as ℤ using (ℤ; _-_; _+_)
open import Data.Integer.Properties using (_≤?_)
open import Data.Integer.Literals renaming (number to number-ℤ)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Literals renaming (number to number-ℕ)
open import Data.Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; from-just; maybe)
open import Data.String.Base as String using (String)
open import Data.Char using (Char)
open import Data.Product using (_×_; _,_; <_,_>)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

instance
  _ : ⊤
  _ = tt
  _ : Number ℕ
  _ = number-ℕ
  _ : Number ℤ
  _ = number-ℤ

data Instr : Set where
  addx : ℤ → Instr
  noop : Instr

Input : Set
Input = List Instr

readInput : List String → Maybe Input
readInput = traverse λ line → case String.words line of λ where
  ("noop" ∷ []) → just noop
  ("addx" ∷ n ∷ []) → Maybe.map addx (readℤ n)
  _ → nothing

record CPU-state : Set where
  constructor ⟦_⟧_
  field
    cycle : ℕ
    register : ℤ  -- value of the register during the cycle

CPU-initial : CPU-state
CPU-initial = ⟦ 1 ⟧ ℤ.1ℤ

pattern 1+_ x = ℕ.suc x
pattern 2+_ x = ℕ.suc (ℕ.suc x)

evalInstr : CPU-state → Instr → List CPU-state
evalInstr (⟦ t ⟧ r) noop = (⟦ 1+ t ⟧ r) ∷ []
evalInstr (⟦ t ⟧ r) (addx i) = (⟦ 1+ t ⟧ r) ∷ (⟦ 2+ t ⟧ (r ℤ.+ i)) ∷ []

unfold : CPU-state → List Instr → List CPU-state
unfold s [] = []
unfold s (i ∷ is) = ss List.++ unfold (Maybe.fromMaybe s (List.last ss)) is
  where ss = evalInstr s i

eval : List Instr → List CPU-state
eval is = CPU-initial ∷ unfold CPU-initial is

chunks : {A : Set} → ℕ → ℕ → List A → List (List A)
chunks size 0 xs = []
chunks size (ℕ.suc n) xs with List.splitAt size xs
... | chunk , ys = chunk ∷ chunks size n ys

sample : {A : Set} → List (List A) → List A
sample = List.mapMaybe (List.head ∘ List.drop 19)

signal-strength : CPU-state → ℤ
signal-strength (⟦ t ⟧ r) = ℤ.+ t ℤ.* r

sumℤ : {A : Set} → (A → ℤ) → List A → ℤ
sumℤ f = List.foldr (ℤ._+_ ∘ f) ℤ.0ℤ

CPU-states : Set
CPU-states = List (List CPU-state)

prep : Input → CPU-states
prep = chunks 40 6 ∘ eval

solve-1 : CPU-states → ℤ
solve-1 = sumℤ signal-strength ∘ sample

current-pixel : List (List ℤ)
current-pixel = List.replicate 6 $ List.applyUpTo ℤ.+_ 40

light-pixel : ℤ → CPU-state → Char
light-pixel i (⟦ _ ⟧ j) with i - 1 ≤? j | j ≤? i + 1 
... | yes _ | yes _ = '#'
... | _ | _ = ' '

solve-2 : CPU-states → String
solve-2 = String.unlines ∘ List.map String.fromList ∘ (List.zipWith ∘ List.zipWith) light-pixel current-pixel

example : Input
example = from-just $ readInput $
  "addx 15" ∷
  "addx -11" ∷
  "addx 6" ∷
  "addx -3" ∷
  "addx 5" ∷
  "addx -1" ∷
  "addx -8" ∷
  "addx 13" ∷
  "addx 4" ∷
  "noop" ∷
  "addx -1" ∷
  "addx 5" ∷
  "addx -1" ∷
  "addx 5" ∷
  "addx -1" ∷
  "addx 5" ∷
  "addx -1" ∷
  "addx 5" ∷
  "addx -1" ∷
  "addx -35" ∷
  "addx 1" ∷
  "addx 24" ∷
  "addx -19" ∷
  "addx 1" ∷
  "addx 16" ∷
  "addx -11" ∷
  "noop" ∷
  "noop" ∷
  "addx 21" ∷
  "addx -15" ∷
  "noop" ∷
  "noop" ∷
  "addx -3" ∷
  "addx 9" ∷
  "addx 1" ∷
  "addx -3" ∷
  "addx 8" ∷
  "addx 1" ∷
  "addx 5" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx -36" ∷
  "noop" ∷
  "addx 1" ∷
  "addx 7" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx 2" ∷
  "addx 6" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx 1" ∷
  "noop" ∷
  "noop" ∷
  "addx 7" ∷
  "addx 1" ∷
  "noop" ∷
  "addx -13" ∷
  "addx 13" ∷
  "addx 7" ∷
  "noop" ∷
  "addx 1" ∷
  "addx -33" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx 2" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx 8" ∷
  "noop" ∷
  "addx -1" ∷
  "addx 2" ∷
  "addx 1" ∷
  "noop" ∷
  "addx 17" ∷
  "addx -9" ∷
  "addx 1" ∷
  "addx 1" ∷
  "addx -3" ∷
  "addx 11" ∷
  "noop" ∷
  "noop" ∷
  "addx 1" ∷
  "noop" ∷
  "addx 1" ∷
  "noop" ∷
  "noop" ∷
  "addx -13" ∷
  "addx -19" ∷
  "addx 1" ∷
  "addx 3" ∷
  "addx 26" ∷
  "addx -30" ∷
  "addx 12" ∷
  "addx -1" ∷
  "addx 3" ∷
  "addx 1" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx -9" ∷
  "addx 18" ∷
  "addx 1" ∷
  "addx 2" ∷
  "noop" ∷
  "noop" ∷
  "addx 9" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  "addx -1" ∷
  "addx 2" ∷
  "addx -37" ∷
  "addx 1" ∷
  "addx 3" ∷
  "noop" ∷
  "addx 15" ∷
  "addx -21" ∷
  "addx 22" ∷
  "addx -6" ∷
  "addx 1" ∷
  "noop" ∷
  "addx 2" ∷
  "addx 1" ∷
  "noop" ∷
  "addx -10" ∷
  "noop" ∷
  "noop" ∷
  "addx 20" ∷
  "addx 1" ∷
  "addx 2" ∷
  "addx 2" ∷
  "addx -6" ∷
  "addx -11" ∷
  "noop" ∷
  "noop" ∷
  "noop" ∷
  []

prep-example : CPU-states
prep-example = prep example

_ : solve-1 prep-example ≡ 13140
_ = refl

_ : solve-2 prep-example ≡ String.unlines (
  "##  ##  ##  ##  ##  ##  ##  ##  ##  ##  " ∷
  "###   ###   ###   ###   ###   ###   ### " ∷
  "####    ####    ####    ####    ####    " ∷
  "#####     #####     #####     #####     " ∷
  "######      ######      ######      ####" ∷
  "#######       #######       #######     " ∷
  [])
_ = refl

sol : String → String
sol = maybe (show ∘ < solve-1 , ("\n" String.++_) ∘ solve-2 > ∘ prep) "" ∘ readInput ∘ String.lines
