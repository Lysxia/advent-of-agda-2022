Advent of Code 2022 in Agda
===========================

Build
-----

```
sh compile.sh
./Main
```

Requirements:

- Agda
- agda-stdlib

Architecture
------------

Solutions are functions on strings (*i.e.*, they include parsing):

```
sol : String → String
```

`Main` collects them and runs them.

Uses of dependent types
-----------------------

### Day 2

> "the second column says how the round needs to end:
> X means you need to lose,
> Y means you need to end the round in a draw,
> and Z means you need to win. Good luck!"

```agda
-- Given the opponent's move, find your move that matches a goal outcome.
infer : (theirs : RPS) → (goal : Outcome) →
        ∃[ yours ] (theirs vs yours) ≡ goal
```
