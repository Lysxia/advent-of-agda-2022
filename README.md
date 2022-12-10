Advent of Code 2022 in Agda
===========================

Build
-----

```
sh compile.sh
./Main
```

### Requirements

- Agda
- agda-stdlib
- [komachi](https://github.com/Lysxia/komachi), applicative regex library
- [schmitty](https://github.com/wenkokke/schmitty) ([fork](https://github.com/Lysxia/schmitty/tree/better-error)), bindings for SMT solvers

```
# Not pictured: install Agda, install Z3 (external dependency of schmitty)

# Install libraries
git clone https://github.com/agda/agda-stdlib
git clone https://github.com/Lysxia/komachi
git clone https://github.com/gallais/agdarsec   # Dependency of schmitty
git clone https://github.com/Lysxia/schmitty -b better-error

cat >> $HOME/.agda/libraries<< EOF
`pwd`/agda-stdlib
`pwd`/komachi
`pwd`/agdarsec
`pwd`/schmitty
EOF

echo /usr/bin/z3 >> $HOME/.agda/executables
```

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

### Day 3

> the badge is the only item type carried by all three Elves.

```agda
find-intersects : (xs : List A) → (xss : List (List A)) →
                  Dec (∃[ x ] All (x ∈_) (xs ∷ xss))
```

### Day 9

> the head (H) and tail (T) must always be touching (diagonally adjacent and
> even overlapping both count as touching)

- `[ H - T by H-T≤1 ∷ nil ]`: A chain with two knots `H` and `T` with a proof `H-T≤1` that they are at distance at most 1 of each other.
- `[ H - T1 by H-T1≤1 ∷ — T2 by T1-T2≤1 ∷ — T3 by T2-T3≤1 ∷ nil ]`: etc.

```agda
record RopeFrom (H : Point) : Set where
  inductive
  constructor _by_∷_
  field
    T : Point
    @0 H-T : distance[ H , T ]≤1
    more : Maybe (RopeFrom T)
```
