module Day12 where

open import Function.Base using (_$_; _∘_; _on_; flip; case_of_)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Nat as Nat using (ℕ; suc; zero; _≤ᵇ_)
open import Data.Product using (_×_; _,_; <_,_>; proj₁)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe)
open import Data.Char as Char using (Char)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.String as String using (String)
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Relation.Binary.PropositionalEquality.Properties as ≡
import Relation.Binary.Construct.On as On

open import Night
open import Graffiti

open Griddy

private variable
  A : Set
  n m : ℕ

Input : Set
Input = List (List Char)

number-from : ℕ → List A → List (ℕ × A)
number-from i [] = []
number-from i (x ∷ xs) = (i , x) ∷ number-from (suc i) xs

number : List A → List (ℕ × A)
number = number-from 0

edge : Char → Char → Bool
edge c d = nn c ≤ᵇ suc (nn d)
  where nn : Char → ℕ
        nn 'S' = Char.toℕ 'a'
        nn 'E' = Char.toℕ 'z'
        nn c = Char.toℕ c

module _ (matrix : Input) where

  open Graph matrix edge
    public

  Pt : Set
  Pt = Point nRows nCols

  findEnd : Maybe Pt
  findEnd = (Maybe._>>= toPoint {n = nRows} {m = nCols}) $ List.head $ flip List.mapMaybe (number matrix) λ{ (i , row) →
    List.head $ flip List.mapMaybe (number row) λ where
      (j , 'E') → just (i , j)
      (j , c) → nothing }

  to2 : Pt → ℕ × ℕ
  to2 = proj₁

  cmp : Trichotomous {A = Pt} _≡_ (Nat2Map._<²_ on proj₁)
  cmp (p , _) (q , _) with Nat2Map.compare p q
  ... | tri< p<q p≉q p≯q = tri< p<q (λ{ refl → p≉q (refl , refl) }) p≯q
  ... | tri≈ p≮q p≈q@(refl , refl) p≯q = tri≈ p≮q (Point-point refl) p≯q
  ... | tri> p≮q p≉q p>q = tri> p≮q (λ{ refl → p≉q (refl , refl) }) p>q


  isSTO : IsStrictTotalOrder {A = Pt} _≡_ (Nat2Map._<²_ on proj₁)
  isSTO = record
    { isEquivalence = ≡.isEquivalence
    ; trans = λ{ {p} {q} {r} → On.transitive {B = Pt} {A = ℕ × ℕ} to2 Nat2Map._<²_ Nat2Map.trans {p} {q} {r} }
    ; compare = cmp
    }

  open AVL isSTO using (Ensembles-AVL)

  open SimpleGraphTheory graph Ensembles-AVL public
    using (bfs)

  bfs′ : Maybe (List (List Pt))
  bfs′ = Maybe.map bfs findEnd

  findStart : (Char → Bool) → List (List Pt) → Maybe (ℕ × Pt)
  findStart c tr = List.head $ flip List.mapMaybe (number tr) λ{ (i , lvl) →
    List.head $ flip List.mapMaybe lvl λ{ p@(x , _) →
      case lookup vertexMap x of λ where
        (just d) → case c d of λ where
          true → just (i , p)
          false → nothing
        _ → nothing
      }}

  solve- : (Char → Bool) → Maybe ℕ
  solve- c = findEnd Maybe.>>= λ start → Maybe.map proj₁ (findStart c (bfs start))

  solve-1 : Maybe ℕ
  solve-1 = solve- ('S' Char.≈ᵇ_)

  solve-2 : Maybe ℕ
  solve-2 = solve- (λ c → ('a' Char.≈ᵇ c) ∨ ('S' Char.≈ᵇ c))

readInput : List String → Input
readInput = List.map String.toList

_ : just 27 ≡ solve-1 (readInput (String.lines "SabcdefghijklmnopqrstuvwxyzE"))
_ = refl

example : Input
example = readInput $
  "Sabqponm" ∷
  "abcryxxl" ∷
  "accszExk" ∷
  "acctuvwj" ∷
  "abdefghi" ∷
  []

_ : just 31 ≡ solve-1 example
_ = refl

_ : just 29 ≡ solve-2 example
_ = refl

sol : String → String
sol = show ∘ < solve-1 , solve-2 > ∘ readInput ∘ String.lines
