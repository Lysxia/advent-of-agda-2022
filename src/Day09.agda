{-# OPTIONS --allow-exec #-}
module Day09 where

open import Agda.Builtin.FromNat using (Number; fromNat)
open import Function.Base using (_$_; _∘_; flip; case_of_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Literals renaming (number to number-ℕ)
open import Data.Integer.Base as Int
open import Data.Integer.Properties using (_≤?_; <-cmp; ≰⇒>; ≤-decTotalOrder)
open import Data.Integer.Literals renaming (number to number-ℤ)
open import Data.Product.Relation.Binary.Lex.NonStrict using (×-decTotalOrder)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Sort.MergeSort using (sort)
open import Data.Maybe as Maybe using (Maybe; nothing; just; from-just; maybe)
open import Data.String as String using (String; lines; words)
open import Data.Nat.Show as ℕ using (readMaybe)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; <_,_>; uncurry)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary

open import SMT.Theories.Ints as Ints using (theory)
open import SMT.Backend.Z3 Ints.theory
  using (solveZ3)
--   renaming (solveZ3 to solveZ3′)
-- postulate solveZ3 : {A : Set} -> A

open import Night

instance
  _ : ⊤
  _ = tt
  _ : Number ℕ
  _ = number-ℕ
  _ : Number ℤ
  _ = number-ℤ

data Dir : Set where
  U D L R : Dir

instance
  show-Dir : Show Dir
  show-Dir = show:= λ where
    U → "U"
    D → "D"
    L → "L"
    R → "R"

-- * Input format

Input : Set
Input = List (Dir × ℕ)

readDir : String → Maybe Dir
readDir "U" = just U
readDir "D" = just D
readDir "L" = just L
readDir "R" = just R
readDir _ = nothing

readInput : List String → Maybe Input
readInput = traverse λ line → case words line of λ where
    (d ∷ n ∷ []) → Maybe.zip (readDir d) (ℕ.readMaybe 10 n)
    _ → nothing

example : Input
example = from-just $ readInput $ 
  "R 4" ∷
  "U 4" ∷
  "L 3" ∷
  "D 1" ∷
  "R 4" ∷
  "D 1" ∷
  "L 5" ∷
  "R 2" ∷
  []

-- * Solution

Point : Set
Point = ℤ × ℤ


-- ** uniq-Point: Deduplicate a list of points

-- Lexicographic ordering of points (total order)
Point-decTotalOrder : DecTotalOrder _ _ _
Point-decTotalOrder = ×-decTotalOrder ≤-decTotalOrder ≤-decTotalOrder

-- Generic deduplication algorithm: sort and filter
module _ {a b c} (DTO : DecTotalOrder a b c) where
  open DecTotalOrder DTO using (_≟_) renaming (Carrier to A)

  uniq-sorted : List A → List A
  uniq-sorted [] = []
  uniq-sorted (x ∷ []) = x ∷ []
  uniq-sorted (x ∷ xs@(y ∷ _)) with x ≟ y | uniq-sorted xs
  ... | yes _ | r = r
  ... | no _ | r = x ∷ r

  uniq : List A → List A
  uniq = uniq-sorted ∘ sort DTO

uniq-Point : List Point → List Point
uniq-Point = uniq Point-decTotalOrder


-- ** Rope: representation of rope of arbitrary length

-- *** 1D Distance
data distance₁[_,_]≤1 : ℤ → ℤ → Set where
  _,_ : ∀ {x1 x2} →
    @0 x1 - x2 ≤ 1 →
    @0 x2 - x1 ≤ 1 →
    distance₁[ x1 , x2 ]≤1

-- *** 2D Distance (infinity norm)
data distance[_,_]≤1 : Point → Point → Set where
  _,_ : ∀ {x1 y1 x2 y2} →
    distance₁[ x1 , x2 ]≤1 →
    distance₁[ y1 , y2 ]≤1 →
    distance[ (x1 , y1) , (x2 , y2) ]≤1

distance₁[x,x]≤1 : ∀ {x : ℤ} → distance₁[ x , x ]≤1
distance₁[x,x]≤1 = solveZ3 , solveZ3

distance₁[x,x+1]≤1 : ∀ {x : ℤ} → distance₁[ x , x + 1 ]≤1
distance₁[x,x+1]≤1 = solveZ3 , solveZ3

distance₁[x,x-1]≤1 : ∀ {x : ℤ} → distance₁[ x , x - 1 ]≤1
distance₁[x,x-1]≤1 = solveZ3 , solveZ3

infixr 3 _by_∷_

-- Rope with an explicit starting knot
record RopeFrom (H : Point) : Set where
  inductive
  constructor _by_∷_
  field
    T : Point
    @0 H-T : distance[ H , T ]≤1
    more : Maybe (RopeFrom T)

infixr 3 —_

pattern nil = nothing
pattern —_ x = just x

record Rope : Set where
  constructor [_-_]
  field
    H : Point
    more : RopeFrom H


-- ** Decidability of distance[_,_]≤1

data Apartness (i j : ℤ) : Set where
  [<] : 1 < j - i → Apartness i j
  [≈] : distance₁[ i , j ]≤1 → Apartness i j
  [>] : 1 < i - j → Apartness i j

apart : (i j : ℤ) → Apartness i j
apart i j with j - i ≤? 1
... | no  j-i≰1 = [<] (≰⇒> j-i≰1)
... | yes j-i≤1 with i - j ≤? 1
...   | no  i-j≰1 = [>] (≰⇒> i-j≰1)
...   | yes i-j≤1 = [≈] (i-j≤1 , j-i≤1)

distance₁[_,_]≤1? : Decidable distance₁[_,_]≤1
distance₁[ x1 , x2 ]≤1? with apart x1 x2
... | [<] 1<x2-x1 = no λ{ (ineq1 , ineq2) → solveZ3 }
... | [≈] d[x1,x2]≤1 = yes d[x1,x2]≤1
... | [>] 1<x1-x2 = no λ{ (ineq1 , ineq2) → solveZ3 }

distance[_,_]≤1? : Decidable distance[_,_]≤1
distance[ (x1 , y1) , (x2 , y2) ]≤1? with distance₁[ x1 , x2 ]≤1? ×-dec distance₁[ y1 , y2 ]≤1?
... | yes (dx , dy) = yes (dx , dy)
... | no ¬dx,dy = no λ{ (dx , dy) → ¬dx,dy (dx , dy) }


-- ** move₁: displace one knot given the previous knot's displacement (1D version)

data Ordering (i j : ℤ) : Set where
  [<] : i < j → Ordering i j
  [≡] : i ≡ j → Ordering i j
  [>] : i > j → Ordering i j

ord : (i j : ℤ) → Ordering i j
ord i j with <-cmp i j
... | tri< i<j _ _ = [<] i<j
... | tri≈ _ i≡j _ = [≡] i≡j
... | tri> _ _ i>j = [>] i>j

move₁ : {H H2 T : ℤ} →
  @0 distance₁[ H , T ]≤1 →
  @0 distance₁[ H , H2 ]≤1 →
  ∃[ T2 ] Erased (distance₁[ H2 , T2 ]≤1 × distance₁[ T , T2 ]≤1)
move₁ {H} {H2} {T} (_ , _) (_ , _) with ord H2 T
... | [<] H2<T = T - 1 , erased ((solveZ3 , solveZ3) , distance₁[x,x-1]≤1)
... | [≡] H2≡T = T ,     erased ((solveZ3 , solveZ3) , distance₁[x,x]≤1)
... | [>] H2>T = T + 1 , erased ((solveZ3 , solveZ3) , distance₁[x,x+1]≤1)


-- ** Displace a Rope

move : {H : Point} → RopeFrom H → (H2 : Point) → @0 distance[ H , H2 ]≤1 → RopeFrom H2
move? : {H : Point} → Maybe (RopeFrom H) → (H2 : Point) → @0 distance[ H , H2 ]≤1 → Maybe (RopeFrom H2)

move (T@(xT , yT) by (xHT , yHT) ∷ more?) H2@(xH2 , yH2) (xHH2 , yHH2)
    with distance[ H2 , T ]≤1?
... | yes d[H2,T]≤1 = T by d[H2,T]≤1 ∷ more?
... | no ¬d[H2,T]≤1
    with move₁ xHT xHH2 | move₁ yHT yHH2
... | xT2 , erased (xH2T2 , xTT2) | yT2 , erased (yH2T2 , yTT2)
    = (xT2 , yT2) by (xH2T2 , yH2T2) ∷ move? more? (xT2 , yT2) (xTT2 , yTT2)

move? nothing _ _ = nothing
move? (just more) H2 H-H2≤1 = just (move more H2 H-H2≤1)

neighbor-at : Dir → (H : Point) → ∃[ H2 ] Erased distance[ H , H2 ]≤1
neighbor-at U (x , y) = (x , y + 1) , erased (distance₁[x,x]≤1 , distance₁[x,x+1]≤1)
neighbor-at D (x , y) = (x , y - 1) , erased (distance₁[x,x]≤1 , distance₁[x,x-1]≤1)
neighbor-at L (x , y) = (x - 1 , y) , erased (distance₁[x,x-1]≤1 , distance₁[x,x]≤1)
neighbor-at R (x , y) = (x + 1 , y) , erased (distance₁[x,x+1]≤1 , distance₁[x,x]≤1)

move-to : Dir → Rope → Rope
move-to d p@([ H - more ]) with neighbor-at d H
... | H2 , erased H-H2≤1 = [ H2 - move more H2 H-H2≤1 ]


-- ** Final touches

last-knot-from : {H : Point} → RopeFrom H → Point
last-knot-from (T by _ ∷ more?) with more?
... | nothing = T
... | just more = last-knot-from more

last-knot : Rope → Point
last-knot [ H - more ] = last-knot-from more

unroll : Input → List Dir
unroll = List.concatMap (uncurry (flip List.replicate))

walkFrom : Rope → List Dir → List Point
walkFrom OO = List.map last-knot ∘ List.scanl (flip move-to) OO

distance[P,P]≤1 : {P : Point} → distance[ P , P ]≤1
distance[P,P]≤1 = distance₁[x,x]≤1 , distance₁[x,x]≤1

rope-of-length-from : ℕ → {H : Point} → RopeFrom H
rope-of-length-from n {H} = H by distance[P,P]≤1 ∷ (case n of λ where
  ℕ.zero → nil
  (ℕ.suc m) → — rope-of-length-from m)

rope-of-length : ℕ → Rope
rope-of-length n = [ (0 , 0) - rope-of-length-from n ]

solve-with-length : ℕ → Input → ℕ
solve-with-length n = List.length ∘ uniq-Point ∘ walkFrom OO ∘ unroll
  where
    OO : Rope
    OO = rope-of-length n


-- ** Solutions

solve-1 : Input → ℕ
solve-1 = solve-with-length 0

_ : solve-1 example ≡ 13
_ = refl

solve-2 : Input → ℕ
solve-2 = solve-with-length 8

_ : solve-2 example ≡ 1
_ = refl

example2 : Input
example2 = from-just $ readInput $
  "R 5" ∷
  "U 8" ∷
  "L 8" ∷
  "D 3" ∷
  "R 17" ∷
  "D 10" ∷
  "L 25" ∷
  "U 20" ∷
  []

_ : solve-2 example2 ≡ 36
_ = refl

sol : String → String
sol = maybe (show ∘ < solve-1 , solve-2 >) "" ∘ readInput ∘ lines
