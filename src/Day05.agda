module Day05 where

open import Function.Base using (id; flip; _∘_; _$_; case_of_)
open import Data.Bool using (_∨_; if_then_else_)
open import Data.Nat.Base as ℕ using (ℕ; _+_; _*_; _∸_)
open import Data.String as String using (String)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; _×_; <_,_>; uncurry)
open import Data.Unit
open import Data.Maybe as Maybe using (Maybe; just; nothing; from-just)
open import Data.Char as Char using (Char; _≈ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Komachi.Base Char

open import Night

private variable
  A B C : Set

char : Char → Parser ⊤
char c = token λ k → k ≈ᵇ c

chars : List Char → Parser ⊤
chars = List.foldr (_*>_ ∘ char) ε

string : String → Parser ⊤
string = chars ∘ String.toList

fromDigit : Char → Maybe ℕ
fromDigit c = if Char.isDigit c then just (Char.toℕ c ∸ Char.toℕ '0') else nothing

digit : Parser ℕ
digit = symbol fromDigit

fromDecimal : List ℕ → ℕ
fromDecimal = List.foldl (_+_ ∘ (10 *_)) 0

decimal : Parser ℕ
decimal = map fromDecimal (digit ★)

three-spaces : Parser (Maybe A)
three-spaces = char ' ' *> char ' ' *> char ' ' $> nothing

bracket-char : Parser (Maybe Char)
bracket-char = char '[' *> symbol (just ∘ just) <* char ']'

Crate : Set
Crate = Char

crate-row : Parser (List (Maybe Crate))
crate-row = ((bracket-char <∣> three-spaces) <* (char ' ' <∣> ε)) ★  -- the ambiguity about who eats what space seems a bit dangerous...

crate-rows : Parser (List (List (Maybe Crate)))
crate-rows = (crate-row <* char '\n') ★

transpose : List (List A) → List (List A)
transpose [] = []
transpose (xs ∷ []) = List.map (_∷ []) xs
transpose (xs ∷ xss@(_ ∷ _)) = List.zipWith _∷_ xs (transpose xss) -- if one list is shorter this is broken

format-crates : List (List (Maybe Crate)) → List (List Crate)
format-crates = List.map (List.mapMaybe id) ∘ transpose

Crates : Set
Crates = List (List Crate)

crates : Parser Crates
crates = map format-crates crate-rows

ignore-middle : Parser ⊤
ignore-middle =
  (token λ c → Char.isDigit c ∨ (c ≈ᵇ ' ')) ★ *> char '\n'
    *> (char ' ' ★) *> char '\n'

data Instruction : Set where
  move_from_to_ : ℕ → ℕ → ℕ → Instruction

instruction : Parser Instruction
instruction = map (λ{ (x , y , z) → move x from y to z })
  (string "move " *> decimal <,> string " from " *> decimal <,> string " to " *> decimal <* (char '\n' <∣> ε))

instructions : Parser (List Instruction)
instructions = instruction ★

Input : Set
Input = Crates × List Instruction

readInput : String → Maybe Input
readInput = parse (crates <,> ignore-middle *> instructions) ∘ String.toList

example : Input
example = from-just $ readInput $ String.unlines $
  "    [D]    " ∷
  "[N] [C]    " ∷
  "[Z] [M] [P]" ∷
  " 1   2   3 " ∷
  "" ∷
  "move 1 from 2 to 1" ∷
  "move 3 from 1 to 3" ∷
  "move 2 from 2 to 1" ∷
  "move 1 from 1 to 2" ∷
  []

data Part : Set where
  One Two : Part

reverse : Part → List A → List A
reverse One = List.reverse
reverse Two = id

perform : Part → Instruction → Crates → Crates
perform part (move x from y to z) cs =
  let ks , cs₁ = take x at y of cs
  in put (reverse part ks) at z into cs₁
  where
    take_at_of : ℕ → ℕ → Crates → List Crate × Crates
    take n at i of cs = case List.splitAt (ℕ.pred i) cs of λ where
      (cs₁ , ks ∷ cs₂) → case List.splitAt n ks of λ where
        (ks₁ , ks₂) → ks₁ , (cs₁ ++ ks₂ ∷ cs₂)
      _ → [] , []

    put_at_into : List Crate → ℕ → Crates → Crates
    put ks at i into cs = case List.splitAt (ℕ.pred i) cs of λ where
      (cs₁ , ks′ ∷ cs₂) → cs₁ ++ (ks ++ ks′) ∷ cs₂
      _ → []

performs : Part → Crates → List Instruction → Crates
performs part = List.foldl (flip (perform part))

solve : Part → Input → String
solve part = String.fromList ∘ List.map (Maybe.fromMaybe '?' ∘ List.head) ∘ uncurry (performs part)

_ : solve One example ≡ "CMZ"
_ = refl

sol : String → String
sol = Maybe.maybe (show ∘ < solve One , solve Two >) "" ∘ readInput
