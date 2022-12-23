module Day11 where

open import Effect.Monad
open import Effect.Monad.State as State using (State; runState)
open import Effect.Monad.State.Transformer as StateT using (StateT; RawMonadState; mkStateT; runStateT)
open import Function.Base using (_$_; _∘_; case_of_)
open import Data.Bool.Base as Bool using (Bool; true; false; not)
open import Data.Nat.Base as Nat using (ℕ; suc; zero; _+_; _*_; _/_; _%_)
import Data.Nat.Show as Nat using (readMaybe)
import Data.Fin.Show as Fin using (readMaybe)
open import Data.Nat.Divisibility using (_∣?_)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; from-just; maybe)
import Data.Maybe.Effectful as Maybe
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.Effectful as List
open import Data.Product as Prod using (∃-syntax; _×_; _,_; <_,_>; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; _[_]%=_; _[_]≔_)
open import Data.String.Base as String using (String)
open import Data.Char as Char using (Char)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Night

Item : Set
Item = ℕ

data Op : Set where
  old : Op
  `_ : ℕ → Op
  _`+_ : Op → Op → Op
  _`*_ : Op → Op → Op


data Test : Set where
  divisible-by : ℕ → Test

_$$_ : Op → Item → Item
old $$ i = i
(` n) $$ i = n
(t `* u) $$ i = (t $$ i) * (u $$ i)
(t `+ u) $$ i = (t $$ i) + (u $$ i)

_??_ : Test → Item → Bool
divisible-by n ?? i = does (n ∣? i)

MonkeyName : ℕ → Set
MonkeyName = Fin

record Monkey (n : ℕ) : Set where
  constructor monkey
  field
    starting-items : List Item
    operation : Op
    test : Test
    if-true : MonkeyName n
    if-false : MonkeyName n

Monkeys : ℕ → Set
Monkeys n = Vec (Monkey n) n

Monkeys-stuff : ℕ → Set
Monkeys-stuff = Vec (List Item)

Input : Set
Input = ∃[ n ] Monkeys n

record MonkeyMonad (n : ℕ) (M : Set → Set) : Set₁ where
  field
    monad : RawMonad M

    count-inspection : MonkeyName n → M ⊤
    debug : String → M ⊤  -- debugging

  open RawMonad monad public

module MonkeyLife {n : ℕ} (monkeys : Monkeys n) (relief : Item → Item) {M : Set → Set} (monkeyMonad : MonkeyMonad n M) where
  private
    S : Set
    S = Monkeys-stuff n

    SM : Set → Set
    SM = StateT S M

    starting-stuff : Monkeys-stuff n
    starting-stuff = Vec.map (List.reverse ∘ Monkey.starting-items) monkeys

    lift : {A : Set} → M A → SM A
    lift m = mkStateT λ s → m >>= λ x → pure (s , x)
      where open MonkeyMonad monkeyMonad

    count-inspection : MonkeyName n → SM ⊤
    count-inspection = lift ∘ MM.count-inspection
      where
        module MM = MonkeyMonad monkeyMonad

    debug : String → SM ⊤
    debug = lift ∘ MM.debug
      where
        module MM = MonkeyMonad monkeyMonad

  run : {A : Set} → SM A → M A
  run f = proj₂ <$> runStateT f starting-stuff
    where open MonkeyMonad monkeyMonad

  private
    monad : RawMonad SM
    monad = StateT.monad (MonkeyMonad.monad monkeyMonad)

    monadState : RawMonadState S SM
    monadState = StateT.monadState (MonkeyMonad.monad monkeyMonad)

    open RawMonad monad
    open RawMonadState monadState

    get-monkey-stuff : MonkeyName n → SM (List Item)
    get-monkey-stuff x = do
      all-stuff ← get
      let stuff = List.reverse (Vec.lookup all-stuff x)
      put (all-stuff [ x ]≔ [])
      pure stuff
      
    throw-to : MonkeyName n → Item → SM ⊤
    throw-to x i = tt <$ modify (_[ x ]%= (i ∷_))

    for-each : ∀ {A : Set} → (A → SM ⊤) → List A → SM ⊤
    for-each f [] = pure tt
    for-each f (x ∷ xs) = f x >> for-each f xs

    inspect-and-throw : MonkeyName n → Item → SM ⊤
    inspect-and-throw x i = do
      debug (show ("Monkey" , x , "inspects" , i))
      count-inspection x
      let open Monkey (Vec.lookup monkeys x)
      let i′ = relief (operation $$ i)
      let recipient = case test ?? i′ of λ where
            true → if-true
            false → if-false
      throw-to recipient i′
      debug (show ("Monkey" , x , "throws" , i′ , "to" , recipient))

    monkey-play : MonkeyName n → SM ⊤
    monkey-play x = get-monkey-stuff x >>= for-each (inspect-and-throw x)

    round : SM ⊤
    round = for-each monkey-play (List.allFin n)

    repeat : ℕ → SM ⊤ → SM ⊤
    repeat zero f = pure tt
    repeat (suc n) f = f >> repeat n f

  rounds : ℕ → SM ⊤
  rounds n = repeat n round 

module MonkeyBusiness (n : ℕ) where

  private
    S : Set
    S = Vec ℕ n

    s0 : S
    s0 = Vec.replicate 0

    M : Set → Set
    M = State S

    count-inspection- : MonkeyName n → M ⊤
    count-inspection- x = tt <$ modify (_[ x ]%= suc)
      where open RawMonadState State.monadState
            open RawMonad State.monad

    debug- : String → M ⊤
    debug- _ = pure tt
      where open RawMonad State.monad

  open MonkeyMonad

  monkeyMonad : MonkeyMonad n M
  monkeyMonad = λ where
    .monad → State.monad
    .count-inspection → count-inspection-
    .debug → debug-

  private
    open import Data.Nat.Properties using (≤-decTotalOrder)
    open import Relation.Binary.Properties.DecTotalOrder ≤-decTotalOrder using (≥-decTotalOrder)
    open import Data.List.Extrema.Nat using (max)
    open import Data.List.Sort.MergeSort ≥-decTotalOrder using (sort)

    max-two : {n : ℕ} → Vec ℕ n → ℕ
    max-two xs with sort (Vec.toList xs)
    ... | x ∷ y ∷ _ = x * y
    ... | _ = 0

  monkey-business : M ⊤ → ℕ
  monkey-business f = max-two (proj₁ (runState f s0))

  MB-debug-run : {A : Set} → M A → List ℕ × A
  MB-debug-run f = Prod.map₁ Vec.toList (runState f s0)

module Debug (n : ℕ) {M} (monkeyMonad : MonkeyMonad n M) where
  private
    S : Set
    S = List String

    s0 : S
    s0 = []

    SM : Set → Set
    SM = StateT S M

    lift : {A : Set} → M A → SM A
    lift m = mkStateT λ s → m >>= λ x → pure (s , x)
      where open MonkeyMonad monkeyMonad

    open MonkeyMonad hiding (_<$_)

    monad-S : RawMonad SM
    monad-S = StateT.monad (monad monkeyMonad)

    monadState-S : RawMonadState S SM
    monadState-S = StateT.monadState (monad monkeyMonad)

  open RawMonad monad-S using (_<$_)
  open RawMonadState monadState-S using (modify)

  monkeyMonad-debug : MonkeyMonad n SM
  monkeyMonad-debug = λ where
    .monad → monad-S
    .count-inspection → lift ∘ count-inspection monkeyMonad
    .debug s → tt <$ modify (s ∷_)

  debug-run : {A : Set} → SM A → M (List String)
  debug-run f = _<$>_ monkeyMonad (List.reverse ∘ proj₁) (runStateT f s0)

solve-1 : Input → ℕ
solve-1 (n , monkeys) = monkey-business (run (rounds 20))
  where
    relief = _/ 3
    open MonkeyBusiness n
    open MonkeyLife monkeys relief monkeyMonad

solve-1-debug : Input → List ℕ × List String 
solve-1-debug (n , monkeys) = MB-debug-run (debug-run (run (rounds 20)))
  where
    relief = _/ 3
    open MonkeyBusiness n
    open Debug n monkeyMonad
    open MonkeyLife monkeys relief monkeyMonad-debug

divisor : {n : ℕ} → Monkey n → ℕ
divisor = (λ{ (divisible-by d) → d }) ∘ Monkey.test

solve-2 : Input → ℕ
solve-2 (n , monkeys) with List.product (List.map divisor (Vec.toList monkeys))
... | zero = 0
... | d@(suc _) = monkey-business (run (rounds 10000))
  where
    relief = _% d
    open MonkeyBusiness n
    open MonkeyLife monkeys relief monkeyMonad

solve-2-debug : ℕ → Input → List ℕ × List String
solve-2-debug n-rounds (n , monkeys) with List.product (List.map divisor (Vec.toList monkeys))
... | zero = [] , []
... | d@(suc _) = MB-debug-run (debug-run (run (rounds n-rounds)))
  where
    relief = _% d
    open MonkeyBusiness n
    open Debug n monkeyMonad
    open MonkeyLife monkeys relief monkeyMonad-debug

solve-2-debug′ : ℕ → Input → List ℕ
solve-2-debug′ n-rounds (n , monkeys) with List.product (List.map divisor (Vec.toList monkeys))
... | zero = []
... | d@(suc _) = proj₁ (MB-debug-run (run (rounds n-rounds)))
  where
    relief = _% d
    open MonkeyBusiness n
    open MonkeyLife monkeys relief monkeyMonad

String-filterᵇ : (Char → Bool) → String → String
String-filterᵇ f = String.fromList ∘ List.filterᵇ f ∘ String.toList

readOperation : List String → Maybe Op
readOperation (x ∷ op ∷ y ∷ []) = do
    i ← case x of λ{ "old" → just old ; x → Maybe.map `_ (Nat.readMaybe 10 x) }
    j ← case y of λ{ "old" → just old ; y → Maybe.map `_ (Nat.readMaybe 10 y) }
    _%_ ← case op of λ{ "*" → just _`*_ ; "+" → just _`+_ ; _ → nothing }
    pure (i % j)
  where open RawMonad Maybe.monad
readOperation _ = nothing

readInput′ : (n m : ℕ) → List String → Maybe (Vec (Monkey n) m)
readInput′ n 0 _ = just []
readInput′ n (suc m)
  ( empty-line ∷
    s-monkey-id ∷
    s-starting-items ∷
    s-operation ∷
    s-test ∷
    s-if-true ∷
    s-if-false ∷
    etc
  ) = do
    "Starting" ∷ "items:" ∷ s-items ← pure (String.words (String-filterᵇ (not ∘ (',' Char.≈ᵇ_)) s-starting-items))
      where _ → nothing
    "Operation:" ∷ "new" ∷ "=" ∷ s-op ← pure (String.words s-operation)
      where _ → nothing
    "Test:" ∷ "divisible" ∷ "by" ∷ s-n ∷ [] ← pure (String.words s-test)
      where _ → nothing
    "If" ∷ "true:" ∷ "throw" ∷ "to" ∷ "monkey" ∷ s-if-true ∷ [] ← pure (String.words s-if-true)
      where _ → nothing
    "If" ∷ "false:" ∷ "throw" ∷ "to" ∷ "monkey" ∷ s-if-false ∷ [] ← pure (String.words s-if-false)
      where _ → nothing
    starting-items ← traverse (Nat.readMaybe 10) s-items
    operation ← readOperation s-op
    test ← Maybe.map divisible-by (Nat.readMaybe 10 s-n)
    if-true ← Fin.readMaybe 10 s-if-true
    if-false ← Fin.readMaybe 10 s-if-false
    let monkey = record
          { starting-items = starting-items
          ; operation = operation
          ; test = test
          ; if-true = if-true
          ; if-false = if-false
          }
    monkeys ← readInput′ n m etc
    pure (monkey ∷ monkeys)
    
  where open RawMonad Maybe.monad
readInput′ n m input = nothing

readInput : List String → Maybe Input
readInput input =
  let input′ = "" ∷ input
      n = List.length input′ / 7 in
  Maybe.map (n ,_) (readInput′ n n input′)

example : Input
example = from-just $ readInput $
  "Monkey 0:" ∷
  "Starting items: 79, 98" ∷
  "Operation: new = old * 19" ∷
  "Test: divisible by 23" ∷
  "  If true: throw to monkey 2" ∷
  "  If false: throw to monkey 3" ∷
  "" ∷
  "Monkey 1:" ∷
  "  Starting items: 54, 65, 75, 74" ∷
  "  Operation: new = old + 6" ∷
  "  Test: divisible by 19" ∷
  "    If true: throw to monkey 2" ∷
  "    If false: throw to monkey 0" ∷
  "" ∷
  "Monkey 2:" ∷
  "  Starting items: 79, 60, 97" ∷
  "  Operation: new = old * old" ∷
  "  Test: divisible by 13" ∷
  "    If true: throw to monkey 1" ∷
  "    If false: throw to monkey 3" ∷
  "" ∷
  "Monkey 3:" ∷
  "  Starting items: 74" ∷
  "  Operation: new = old + 3" ∷
  "  Test: divisible by 17" ∷
  "    If true: throw to monkey 0" ∷
  "    If false: throw to monkey 1" ∷
  []

_ : solve-1 example ≡ 10605
_ = refl

-- _ : solve-2 example ≡ ?
-- _ = ?
-- 
-- _ : solve-2-debug′ 5000 example ≡ ?
-- _ = ?

sol : String → String
sol = maybe (show ∘ < solve-1 , solve-2 >) "" ∘ readInput ∘ String.lines
