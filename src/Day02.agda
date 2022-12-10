module Day02 where

open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Function using (_$_; _∘_; _-⟨_⟩-_)
open import Data.String.Base as String using (String; lines; words)
open import Data.List.Base as List
open import Data.Maybe using (Maybe; just; nothing; from-just; maybe)
open import Data.List.Effectful as List
open import Data.Maybe.Effectful as Maybe
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; <_,_>; uncurry)
open import Relation.Binary.PropositionalEquality

open import Night

data ABC : Set where
  A B C : ABC

data XYZ : Set where
  X Y Z : XYZ

Input : Set
Input = List (ABC × XYZ)

readABC : String → Maybe ABC
readABC "A" = just A
readABC "B" = just B
readABC "C" = just C
readABC _ = nothing

readXYZ : String → Maybe XYZ
readXYZ "X" = just X
readXYZ "Y" = just Y
readXYZ "Z" = just Z
readXYZ _ = nothing

readInput : String → Maybe Input
readInput = traverse (readLine ∘ words) ∘ lines
  where
    open RawApplicative Maybe.applicative using (_⊗_)

    readLine : List String → Maybe (ABC × XYZ)
    readLine (abc ∷ xyz ∷ []) = readABC abc ⊗ readXYZ xyz
    readLine _ = nothing

example : Input
example = from-just $ readInput $
  "A Y\nB X\nC Z"

data ✊✋✌ : Set where
  ✊ ✋ ✌ : ✊✋✌

data Outcome : Set where
  lose draw win : Outcome

_vs_ : ✊✋✌ → ✊✋✌ → Outcome
✊ vs ✌ = lose
✋ vs ✊ = lose
✌ vs ✋ = lose
✊ vs ✊ = draw
✋ vs ✋ = draw
✌ vs ✌ = draw
✊ vs ✋ = win
✋ vs ✌ = win
✌ vs ✊ = win

module Score where
  outcome : Outcome → ℕ
  outcome lose = 0
  outcome draw = 3
  outcome win = 6

  shape : ✊✋✌ → ℕ
  shape ✊ = 1
  shape ✋ = 2
  shape ✌ = 3

  round : ✊✋✌ → ✊✋✌ → ℕ
  round theirs yours = shape yours + outcome (theirs vs yours)

  rounds : List (✊✋✌ × ✊✋✌) → ℕ
  rounds = sum ∘ List.map (uncurry round)

ABC→✊✋✌ : ABC → ✊✋✌
ABC→✊✋✌ = λ where
  A → ✊
  B → ✋
  C → ✌

XYZ→✊✋✌ : XYZ → ✊✋✌
XYZ→✊✋✌ = λ where
  X → ✊
  Y → ✋
  Z → ✌

decode-1 : Input → List (✊✋✌ × ✊✋✌)
decode-1 = List.map (Prod.map ABC→✊✋✌ XYZ→✊✋✌)

solve-1 : Input → ℕ
solve-1 = Score.rounds ∘ decode-1

XYZ→Outcome : XYZ → Outcome
XYZ→Outcome = λ where
  X → lose
  Y → draw
  Z → win

infer : (theirs : ✊✋✌) → (goal : Outcome) →
        ∃[ yours ] (theirs vs yours) ≡ goal
infer ✊ lose = ✌ , refl
infer ✊ draw = ✊ , refl
infer ✊ win  = ✋ , refl
infer ✋ lose = ✊ , refl
infer ✋ draw = ✋ , refl
infer ✋ win  = ✌ , refl
infer ✌ lose = ✋ , refl
infer ✌ draw = ✌ , refl
infer ✌ win  = ✊ , refl

decode-2 : Input → List (✊✋✌ × ✊✋✌)
decode-2 = List.map λ{ (abc , xyz) →
  let theirs = ABC→✊✋✌ abc
      yours , _ = infer theirs (XYZ→Outcome xyz)
  in theirs , yours  }

solve-2 : Input → ℕ
solve-2 = Score.rounds ∘ decode-2

_ : solve-1 example ≡ 15
_ = refl

_ : solve-2 example ≡ 12
_ = refl

sol : String → String
sol = maybe (show ∘ < solve-1 , solve-2 >) "" ∘ readInput
