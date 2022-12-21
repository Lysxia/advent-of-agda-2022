module Day20 where

open import Function.Base using (_∘_; _$_)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; from-just; maybe)
open import Data.Nat.Base as Nat using (ℕ; suc; zero)
open import Data.Nat.GeneralisedArithmetic using (iterate)
open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂)
open import Data.Integer.Base as Int using (ℤ; +_)
open import Data.Integer.Properties as Intₚ
open import Data.String.Base as String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

private variable
  A N : Set

Input : Set
Input = List ℤ

readInput : List String → Maybe Input
readInput = traverse readℤ

number-from : ℕ → List A → List (ℕ × A)
number-from n [] = []
number-from n (x ∷ xs) = (n , x) ∷ number-from (suc n) xs

find-fst : ℕ → List (ℕ × A) → Maybe (List (ℕ × A) × A × List (ℕ × A))
find-fst n xs with List.breakᵇ ((n Nat.≡ᵇ_) ∘ proj₁) xs
... | xs₁ , (_ , x) ∷ xs₂ = just (xs₁ , x , xs₂)
... | _ , [] = nothing

reinsert : ℤ → A → List A → List A → List A
reinsert (+ i) x xs₁ xs₂ with List.splitAt i xs₂
... | xs₂′ , xs₂″@(_ ∷ _) = xs₁ ++ xs₂′ ++ x ∷ xs₂″
... | _ , [] with List.splitAt (i Nat.∸ List.length xs₂) xs₁
...   | xs₁′ , xs₁″ = xs₁′ ++ x ∷ xs₁″ ++ xs₂
reinsert Int.-[1+ i ] x xs₁ xs₂ with List.splitAt i (List.reverse xs₁)
... | xs₁″ , y ∷ xs₁′ = List.reverse xs₁′ ++ x ∷ y ∷ List.reverse xs₁″ ++ xs₂
... | _ , [] with List.splitAt (i Nat.∸ List.length xs₁) (List.reverse xs₂)
...   | xs₂″ , y ∷ xs₂′ = xs₁ ++ List.reverse xs₂′ ++ x ∷ y ∷ List.reverse xs₂″
...   | _ , [] = []

-- i mod (n-1)
_%%_ : ℤ → ℕ → ℤ
i %% 0 = i
i %% 1 = i
i %% (suc n@(suc _)) = + ((i + o) %ℕ n) - o
  where
    open Int using (_+_; _-_; _%ℕ_; _/ℕ_; ∣_∣)
    o = + Nat.⌊ n /2⌋

mix₁ : ℕ → ℕ → List (ℕ × ℤ) → List (ℕ × ℤ)
mix₁ len n xs with find-fst n xs
... | nothing = []
... | just (xs₁ , i , xs₂) = reinsert (i %% len) (n , i) xs₁ xs₂

mix′ : ℕ → List (ℕ × A) → List (ℕ × ℤ) → List (ℕ × ℤ)
mix′ len [] xs = xs
mix′ len ((n , _) ∷ ns) xs = mix′ len ns (mix₁ len n xs)

mix : List (ℕ × ℤ) → List (ℕ × ℤ)
mix xs = mix′ (List.length xs) xs xs

mix10 : List (ℕ × ℤ) → List (ℕ × ℤ)
mix10 xs = iterate (mix′ (List.length xs) xs) xs 10

align-0 : List (ℕ × ℤ) → List ℤ
align-0 xs with List.break ((+ 0) Intₚ.≟_) (List.map proj₂ xs)
... | xs₁ , xs₂ = xs₂ ++ xs₁

example : Input
example = from-just $ readInput $
  "1" ∷
  "2" ∷
  "-3" ∷
  "3" ∷
  "-2" ∷
  "0" ∷
  "4" ∷
  []

-_ : ℕ → ℤ
- i = Int.- + i


_ : align-0 (mix (number-from 0 example)) ≡ (+ 0 ∷ + 3 ∷ - 2 ∷ + 1 ∷ + 2 ∷ - 3 ∷ + 4 ∷ [])
_ = refl

rotate : ℕ → List A → List A
rotate n xs with List.splitAt n xs
... | xs₁ , xs₂ = xs₂ ++ xs₁

zoop : List ℤ → ℤ
zoop xs with xs₁ | xs₂ | xs₃
  where xs₁ = rotate 1000 xs
        xs₂ = rotate 1000 xs₁
        xs₃ = rotate 1000 xs₂
... | x ∷ _ | y ∷ _ | z ∷ _ = x + y + z
  where open Int using (_+_)
... | _ | _ | _ = + 0

solve-1 : Input → ℤ
solve-1 = zoop ∘ align-0 ∘ mix ∘ number-from 0

solve-2 : Input → ℤ
solve-2 = zoop ∘ align-0 ∘ mix10 ∘ number-from 0 ∘ List.map ((Int.+ 811589153) Int.*_)

sol : String → String
sol = maybe (show ∘ < solve-1 , solve-2 >) "" ∘ readInput ∘ String.lines
