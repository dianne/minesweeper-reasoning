-- a hopefully-self-evident description of valid minesweeper moves

module Minesweeper.Moves where

open import Data.Empty
open import Relation.Nullary

open import Minesweeper.Coords
open import Minesweeper.Board
open import Minesweeper.Rules

data Tile : Set where
  known   : KnownTile → Tile
  unknown : Tile

-- tile filling: an unknown tile can be filled with anything
data _↝▣_ : Tile → KnownTile → Set where
  ↝▣known   : ∀ s → known s ↝▣ s
  ↝▣unknown : ∀ s → unknown ↝▣ s

-- board filling: can a fully filled board be reached by filling in the unknown tiles of a partial board?
_↝⊞_ : ∀ {bounds} → Board Tile bounds → Board KnownTile bounds → Set
holey ↝⊞ filled = ∀ coords → lookup coords holey ↝▣ lookup coords filled


-- move validity: a guess as to a tile's identity on a board is valid when it holds in every rule-respecting way to fill the board's unfilled tiles
_[_]↝✓_ : ∀ {bounds} → Board Tile bounds → Coords bounds → Guess → Set
grid [ coords ]↝✓ guess = ∀ grid′ →
  grid ↝⊞ grid′ →
  grid′ ✓ →
    guess ⚐✓ lookup coords grid′

-- solvable boards: a board is solvable when there is a rule-respecting way to fill its unfilled tiles
record Solvable {bounds} (unsolved : Board Tile bounds) : Set where
  field
    solution  : Board KnownTile bounds
    relevance : unsolved ↝⊞ solution
    validity  : solution ✓

-- "play" a valid move on a solvable board, giving evidence that it holds in the provided solution
play : ∀ {bounds grid} (coords : Coords bounds) {guess} →
  grid [ coords ]↝✓ guess → (solved : Solvable grid) →
    guess ⚐✓ lookup coords (Solvable.solution solved)
play coords move solved = move (Solvable.solution solved) (Solvable.relevance solved) (Solvable.validity solved)


invert⚐ : Guess → Guess
invert⚐ mine⚐ = safe⚐
invert⚐ safe⚐ = mine⚐

¬-⚐✓-invert : ∀ {guess tile} → ¬ guess ⚐✓ tile → invert⚐ guess ⚐✓ tile
¬-⚐✓-invert {mine⚐} {mine}   ¬guess⚐✓tile = ⊥-elim (¬guess⚐✓tile ⚐✓mine)
¬-⚐✓-invert {mine⚐} {safe n} ¬guess⚐✓tile = ⚐✓safe n
¬-⚐✓-invert {safe⚐} {mine}   ¬guess⚐✓tile = ⚐✓mine
¬-⚐✓-invert {safe⚐} {safe n} ¬guess⚐✓tile = ⊥-elim (¬guess⚐✓tile (⚐✓safe n))
