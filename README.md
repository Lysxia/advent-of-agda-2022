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
