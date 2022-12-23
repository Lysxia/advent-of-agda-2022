module Day23 where

open import Function.Base using (_∘_; _$_)
open import Data.Bool.Base using (Bool; true; false; not)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Char.Base using (Char)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; from-just; maybe; fromMaybe; when)
open import Data.Nat.Base as Nat using (ℕ; suc; zero)
open import Data.Integer as Int using (ℤ; +_)
import Data.Integer.Properties as Intₚ
open import Data.String.Base as String using (String)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Data.Unit.Base using (⊤; tt)
import Data.Tree.AVL.Map as MkMap
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

-- x axis pointing right
-- y axis pointing down
Point : Set
Point = ℤ × ℤ

module _ where
  STO : StrictTotalOrder _ _ _
  STO = ×-strictTotalOrder Intₚ.<-strictTotalOrder Intₚ.<-strictTotalOrder

  open module Map = MkMap STO public

Input : Set
Input = Map ⊤

data Dir : Set where
  N S W E : Dir

module _ where
  open Int

  point : Dir → Point → Point
  point N (x , y) = (x , y - 1ℤ)
  point S (x , y) = (x , y + 1ℤ)
  point W (x , y) = (x - 1ℤ , y)
  point E (x , y) = (x + 1ℤ , y)

module PointDir where
  infixl 9 _+_
  _+_ : Point → Dir → Point
  p + d = point d p

RoundState : Set
RoundState = List Dir

initRS : RoundState
initRS = N ∷ S ∷ W ∷ E ∷ []

neighbors? : Map ⊤ → Point → Bool
neighbors? m p = List.any (λ q → Map.member q m) $
  p + N ∷
  p + N + E ∷
  p + E ∷
  p + S + E ∷
  p + S ∷
  p + S + W ∷
  p + W ∷
  p + N + W ∷
  []
  where open PointDir

try-dir : Dir → Map ⊤ → Point → Maybe Point
try-dir d m p = when (not (List.any (λ q → Map.member q m) (three d))) (p + d)
  where
    open PointDir
    three : Dir → List Point
    three N = p + N + W ∷ p + N ∷ p + N + E ∷ []
    three S = p + S + W ∷ p + S ∷ p + S + E ∷ []
    three W = p + N + W ∷ p + W ∷ p + S + W ∷ []
    three E = p + N + E ∷ p + E ∷ p + S + E ∷ []

try-round : RoundState → Map ⊤ → Point → Maybe Point
try-round s m p with neighbors? m p
... | true = List.foldr (λ d etc → Maybe._<∣>_ (try-dir d m p) etc) nothing s
... | false = nothing

data Intention : Set where
  Go Conflict : Intention

mapTargets : RoundState → Map ⊤ → Map (Maybe Point)
mapTargets s m = Map.mapWith (λ p _ → try-round s m p) m

mapIntentions : Map (Maybe Point) → Map Intention
mapIntentions mm = Map.foldr go Map.empty mm
  where
    incr : Maybe Intention → Intention
    incr nothing = Go
    incr (just _) = Conflict

    go : Point → Maybe Point → Map Intention → Map Intention
    go p nothing m = m
    go p (just q) m = Map.insertWith q incr m

step : Map (Maybe Point) → Map Intention → Map ⊤
step targets intentions = Map.foldr (λ p q′ m → Map.insert (go p q′) tt m) Map.empty targets
  where
    go : Point → Maybe Point → Point
    go p nothing = p
    go p (just q) with Map.lookup intentions q
    ... | just Conflict = p
    ... | just Go = q
    ... | nothing = q -- should not happen

round : RoundState → Map ⊤ → Map ⊤ × Bool
round s old = new , nobody-moved
  where
    targets = mapTargets s old
    intentions = mapIntentions targets
    new = step targets intentions
    nobody-moved = List.all (λ{ (_ , Conflict) → true ; (_ , Go) → false }) (Map.toList intentions)

rotate : RoundState → RoundState
rotate [] = []
rotate (x ∷ xs) = xs List.++ x ∷ []

roundsWith : ℕ → RoundState → Map ⊤ → ℕ × Map ⊤
roundsWith zero _ m = zero , m
roundsWith (suc n) s m with round s m
... | _ , true = n , m
... | mm , false = roundsWith n (rotate s) mm

rounds : ℕ → Map ⊤ → ℕ × Map ⊤
rounds n m with roundsWith n initRS m
... | left , mm = (n ∸ left) , mm
  where open Nat

Box : Set
Box = ℤ × ℤ × ℤ × ℤ

bounding-box : Map ⊤ → Box
bounding-box = fromMaybe (0ℤ , 0ℤ , 0ℤ , 0ℤ) ∘ Map.foldr mini nothing
  where
    open Int

    mini : Point → ⊤ → Maybe Box → Maybe Box
    mini (x , y) _ nothing = just (x , x , y , y)
    mini (x , y) _ (just (xmin , xmax , ymin , ymax)) = just (x ⊓ xmin , x ⊔ xmax , y ⊓ ymin , y ⊔ ymax)

sizeBox : Box → ℤ
sizeBox (xmin , xmax , ymin , ymax) = (1ℤ + xmax - xmin) * (1ℤ + ymax - ymin)
  where open Int

free-area : Map ⊤ → ℤ
free-area m = sizeBox (bounding-box m) - + Map.size m
  where open Int

solve-1 : Input → ℤ
solve-1 = free-area ∘ proj₂ ∘ rounds 10

readInput : String → Map ⊤
readInput = go (0ℤ , 0ℤ) ∘ String.toList
  where
    open Int

    incr-col incr-line : Point → Point
    incr-col (x , y) = (x + 1ℤ , y)
    incr-line (x , y) = (0ℤ , y + 1ℤ)

    go : Point → List Char → Map ⊤
    go p [] = Map.empty
    go p ('\n' ∷ etc) = go (incr-line p) etc
    go p ('#' ∷ etc) = Map.insert p tt (go (incr-col p) etc)
    go p (_ ∷ etc) = go (incr-col p) etc

example : Input
example = readInput $ String.unlines $
  "....." ∷
  "..##." ∷
  "..#.." ∷
  "....." ∷
  "..##." ∷
  "....." ∷
  []

example2 : Input
example2 = readInput $ String.unlines $
  "....#.." ∷
  "..###.#" ∷
  "#...#.#" ∷
  ".#...##" ∷
  "#.###.." ∷
  "##.#.##" ∷
  ".#..#.." ∷
  []

_ : solve-1 example2 ≡ + 110
_ = refl

solve-2 : Input → ℕ
solve-2 = proj₁ ∘ rounds 10000

_ : solve-2 example2 ≡ 20
_ = refl

sol : String → String
sol = show ∘ solve-1 ∘ readInput

