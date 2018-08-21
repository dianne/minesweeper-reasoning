-- the goal of this module is to present inductive tools for reasoning about minesweeper, similar to the axioms ProofSweeper provides,
-- and prove them sound and complete with respect to our formulation of minesweeper.

module Minesweeper.Reasoning where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List as List using (List)
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Nat

open import Data.Fin using (Fin)
open import Minesweeper.Enumeration as Enum using (Enumeration)
open import Minesweeper.Coords
open import Minesweeper.Board
open import Minesweeper.Rules
open import Minesweeper.Moves

-- our inductive family for minesweeper proofs! based on ProofSweeper but using our own machinery
-- and not intended for hand-writing at all
data _[_]↝★_ {bounds} (grid : Board Tile bounds) (coords : Coords bounds) : Guess → Set
record _Neighboring★_on_excluding_ {bounds} (guess : Guess) (neighbor : Coords bounds) (grid : Board Tile bounds) (exclusion : Coords bounds) : Set

data _[_]↝★_ {bounds} grid coords where
  -- known tiles already have a proven identity
  known★ : ∀ tile guess → lookup coords grid ≡ known tile → guess ↝⚐ tile → grid [ coords ]↝★ guess

  -- a tile is safe if an adjacent safe tile already has as many adjacent mines as it can
  safe★ : ∀ neighborMineCount
    (safeNeighbor : known (safe neighborMineCount) Neighboring coords on grid)
    (neighborMines : List (mine⚐ Neighboring★ proj₁ (proj₁ safeNeighbor) on grid excluding coords)) →
    List.length neighborMines ≡ neighborMineCount →
      grid [ coords ]↝★ safe⚐

  -- a tile is a mine if an adjacent safe tile already has as many adjacent safe tiles as it can
  mine★ : ∀ neighborMineCount
    (safeNeighbor : known (safe neighborMineCount) Neighboring coords on grid)
    (neighborSafes : List (safe⚐ Neighboring★ proj₁ (proj₁ safeNeighbor) on grid excluding coords)) →
    List.length neighborSafes + neighborMineCount ≡ List.length (Enumeration.list (neighbors (proj₁ (proj₁ safeNeighbor)))) →
      grid [ coords ]↝★ mine⚐

record _Neighboring★_on_excluding_ {bounds} guess neighbor grid exclusion where
  inductive
  field
    coords : Coords bounds
    deduction : grid [ coords ]↝★ guess
    ≢exclusion : coords ≢ exclusion
