module Day21 where

open import Function.Base using (_∘_; _$_; case_of_)
open import Effect.Monad using (RawMonad)
open import Data.Bool.Base using (Bool; true; false)
open import Data.String.Base as String using (String)
open import Data.Char.Base as Char using (Char)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as Map
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Integer.Base as Int using (ℤ; _+_; _-_; _*_; _/_; +_; -_; _%_; -[1+_])
import Data.Integer.Properties as Intₚ
open import Data.Rational.Unnormalised as Rat using (ℚᵘ; mkℚᵘ)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; from-just; maybe)
open import Data.Maybe.Effectful using (monad)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Product as Prod using (_×_; _,_; <_,_>)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

data Bop : Set where
  `+ `- `* `/ : Bop

_//_ : ℤ → ℤ → ℤ
n // m@(+ suc _) = n / m
n // m@(-[1+ _ ]) = n / m
n // (+ zero) = + zero

_///_ : ℚᵘ → ℚᵘ → ℚᵘ
n /// m@(mkℚᵘ (+ suc _) _) = n Rat.÷ m
n /// m@(mkℚᵘ -[1+ _ ] _) = n Rat.÷ m
n /// m@(mkℚᵘ _ _) = n

⟦_⟧ : Bop → ℤ → ℤ → ℤ
⟦ `+ ⟧ = _+_
⟦ `- ⟧ = _-_
⟦ `* ⟧ = _*_
⟦ `/ ⟧ = _//_

⟦_⟧′ : Bop → ℚᵘ → ℚᵘ → ℚᵘ
⟦ `+ ⟧′ = Rat._+_
⟦ `- ⟧′ = Rat._-_
⟦ `* ⟧′ = Rat._*_
⟦ `/ ⟧′ = _///_


data Op : Set where
  constant : ℤ → Op
  op : String → Bop → String → Op

data Expr : Set where
  humn : Expr
  constant : ℤ → Expr
  op : Expr → Bop → Expr → Expr

instance
  Show-Bop : Show Bop
  Show-Bop = show:= λ where
    `+ → " + "
    `- → " - "
    `* → " * "
    `/ → " / "

  Show-Expr : Show Expr
  Show-Expr = show:= show-expr
    where
      show-expr : Expr → String
      show-expr humn = "X"
      show-expr (constant i) = show i
      show-expr (op x b y) = "(" String.++ show-expr x String.++ show b String.++ show-expr y String.++ ")"

smart-op : ℕ → Expr → Bop → Expr → Expr
smart-op′ : ℕ → Expr → Bop → Expr → Expr

smart-op fuel (constant n) b (constant m) = constant (⟦ b ⟧ n m)
smart-op fuel humn `+ e = smart-op′ fuel e `+ humn
smart-op fuel humn `- humn = constant (+ 0)
smart-op fuel e `+ (constant n) = smart-op′ fuel (constant n) `+ e
smart-op fuel e `- (constant n) = smart-op′ fuel (constant (- n)) `+ e
smart-op fuel e `* (constant n) = smart-op′ fuel (constant n) `* e
smart-op fuel (constant n) `+ (op (constant m) `+ e) = op (constant (n + m)) `+ e
smart-op fuel (constant n) `+ (op (constant m) `- e) = op (constant (n + m)) `- e
smart-op fuel (constant n) `- (op (constant m) `+ e) = op (constant (n - m)) `- e
smart-op fuel (constant n) `- (op (constant m) `- e) = op (constant (n - m)) `+ e
smart-op fuel (constant n) `* (op (constant m) `* e) = op (constant (n * m)) `* e
smart-op fuel z `* (op x `+ y) = op (smart-op′ fuel z `* x) `+ (smart-op′ fuel z `* y)
smart-op fuel (op x `+ y) `* z = op (smart-op′ fuel x `* z) `+ (smart-op′ fuel y `* z)
smart-op fuel z `* (op x `- y) = op (smart-op′ fuel z `* x) `- (smart-op′ fuel z `* y)
smart-op fuel (op x `- y) `* z = op (smart-op′ fuel x `* z) `- (smart-op′ fuel y `* z)
smart-op fuel (constant n) `+ (op e `/ (constant m)) = smart-op′ fuel (smart-op′ fuel (constant (n * m)) `+ e) `/ (constant m)
smart-op fuel (constant n) `- (op e `/ (constant m)) = smart-op′ fuel (smart-op′ fuel (constant (n * m)) `- e) `/ (constant m)
smart-op fuel x b y = op x b y

smart-op′ (suc n) x b y = smart-op n x b y
smart-op′ zero x b y = op x b y

Input : Set
Input = Map Op

yell : Input → String → ℕ → Maybe ℤ
yell m monkey zero = nothing
yell m monkey (suc n) = Map.lookup m monkey >>= λ where
    (constant n) → just n
    (op mx f my) → do
      x ← yell m mx n
      y ← yell m my n
      just (⟦ f ⟧ x y)
  where
    open RawMonad monad

yell-2 : Input → String → ℕ → Maybe Expr
yell-2 m "humn" _ = just humn
yell-2 m monkey zero = nothing
yell-2 m monkey (suc n) = Map.lookup m monkey >>= λ where
    (constant n) → just (constant n)
    (op mx f my) → do
      let g = case monkey of λ{ "root" → `- ; _ → f }
      x ← yell-2 m mx n
      y ← yell-2 m my n
      just (smart-op 1000 x g y)
  where
    open RawMonad monad

eval : Expr → ℚᵘ → ℚᵘ
eval (constant n) _ = n Rat./ 1
eval humn n = n
eval (op x b y) n = ⟦ b ⟧′ (eval x n) (eval y n)

sign : ℚᵘ → Bool
sign (mkℚᵘ (+ _) _) = true
sign (mkℚᵘ (-[1+ _ ]) _) = false

sameSign : Bool → Bool → Bool
sameSign true true = true
sameSign false false = true
sameSign _ _  = false

find-zero : Expr → ℕ → Bool → ℤ → ℤ → Maybe ℤ
find-zero e 0 s n m = nothing
find-zero e (suc fuel) s n m with n + Int.1ℤ Intₚ.≟ m
... | yes _ = nothing
... | no _ = let nm/2 = (n + m) / + 2
                 y = eval e (nm/2 Rat./ 1)
                 sy = sign y in
      case (ℚᵘ.numerator y , sameSign s sy) of λ where
        (+ 0 , _) → just nm/2
        (_ , true) → find-zero e fuel s nm/2 m
        (_ , false) → find-zero e fuel s n nm/2

inf : ℤ
inf = + 100000000000000

find-zero′ : Expr → Maybe ℤ
find-zero′ e with eval e (+ 0 Rat./ 1) | eval e (inf Rat./ 1)
... | mkℚᵘ (+ 0) _ | _ = just (+ 0)
... | _ | mkℚᵘ (+ 0) _ = just inf
... | mkℚᵘ (+ _) _ | mkℚᵘ -[1+ _ ] _ = find-zero e 100 true (+ 0) inf
... | mkℚᵘ -[1+ _ ] _ | mkℚᵘ (+ _) _ = find-zero e 100 false (+ 0) inf
... | _ | _ = nothing

solve-1 : Input → Maybe ℤ
solve-1 m = yell m "root" (Map.size m)

solve-2 : Input → Maybe ℤ
solve-2 m = do
  e ← yell-2 m "root" (Map.size m)
  find-zero′ e
  where
    open RawMonad monad

readOp : String → Maybe Bop
readOp "+" = just `+
readOp "-" = just `-
readOp "*" = just `*
readOp "/" = just `/
readOp _ = nothing

readLine : String → Maybe (String × Op)
readLine s with List.breakᵇ (':' Char.≈ᵇ_) (String.toList s)
... | monkey , _ ∷ _ ∷ z = case String.words (String.fromList z) of λ where
    (x ∷ o ∷ y ∷ []) → do
      q ← readOp o
      just (String.fromList monkey , op x q y)
    (p ∷ []) → do
      n ← readℤ p
      just (String.fromList monkey , constant n)
    _ → nothing
  where open RawMonad monad
... | _ = nothing

readInput : List String → Maybe (Map Op)
readInput = Maybe.map Map.fromList ∘ traverse readLine

example : Input
example = from-just $ readInput $
  "root: pppw + sjmn" ∷
  "dbpl: 5" ∷
  "cczh: sllz + lgvd" ∷
  "zczc: 2" ∷
  "ptdq: humn - dvpt" ∷
  "dvpt: 3" ∷
  "lfqf: 4" ∷
  "humn: 5" ∷
  "ljgn: 2" ∷
  "sjmn: drzm * dbpl" ∷
  "sllz: 4" ∷
  "pppw: cczh / lfqf" ∷
  "lgvd: ljgn * ptdq" ∷
  "drzm: hmdt - zczc" ∷
  "hmdt: 32" ∷
  []

_ : solve-1 example ≡ just (+ 152)
_ = refl

_ : solve-2 example ≡ just (+ 301)
_ = refl

sol : String → String
sol = maybe (show ∘ < solve-1 , solve-2 >) "" ∘ readInput ∘ String.lines
