-- the rules of filled minesweeper boards: do the numbers tell the truth?

module Minesweeper.Rules where

open import Data.Unit
open import Data.Product
open import Data.Nat as ℕ using (ℕ)
open import Data.List hiding (lookup)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary

open import Minesweeper.Coords
open import Minesweeper.Board
open import Minesweeper.Enumeration as Enum using (Enumeration)

data KnownTile : Set where
  mine : KnownTile
  safe : ℕ → KnownTile

data Guess : Set where
  mine⚐ : Guess
  safe⚐ : Guess

-- guessing: is a guess of a tile's type valid for that tile?
data _⚐✓_ : Guess → KnownTile → Set where
  ⚐✓mine : mine⚐ ⚐✓ mine
  ⚐✓safe : ∀ n → safe⚐ ⚐✓ safe n


-- a numbered tile is good if the number on it matches the number of mines adjacent to it.
-- since all Enumerations of a type have the same length, it's sufficient to provide only one as evidence
_[_]✓ : ∀ {bounds} → Board KnownTile bounds → Coords bounds → Set
_[_]✓ {bounds} grid coords with lookup coords grid
... | mine = ⊤
... | safe n = Σ[ neighboringMines ∈ Enumeration ((mine⚐ ⚐✓_) Neighboring coords on grid) ] n ≡ length (Enumeration.list neighboringMines)

-- a board is good if all positions on it are good
_✓ : ∀ {bounds} → Board KnownTile bounds → Set
_✓ {bounds} grid = ∀ coords → grid [ coords ]✓


_⚐✓?_ : Decidable (_⚐✓_)
mine⚐ ⚐✓? mine   = yes ⚐✓mine
mine⚐ ⚐✓? safe _ = no λ { () }
safe⚐ ⚐✓? mine   = no λ { () }
safe⚐ ⚐✓? safe n = yes (⚐✓safe n)

⚐✓-irrelevance : Irrelevant _⚐✓_
⚐✓-irrelevance ⚐✓mine     ⚐✓mine      = refl
⚐✓-irrelevance (⚐✓safe n) (⚐✓safe .n) = refl

neighboringMines : ∀ {bounds} (grid : Board KnownTile bounds) (coords : Coords bounds) → Enumeration ((mine⚐ ⚐✓_) Neighboring coords on grid)
neighboringMines grid coords = Enum.filter ⚐✓-irrelevance (λ { (neighbor , _) → mine⚐ ⚐✓? (lookup neighbor grid) }) (neighbors coords)

_[_]✓? : ∀ {bounds} → Decidable (_[_]✓ {bounds})
_[_]✓? {bounds} grid coords with lookup coords grid
... | mine = yes tt
... | safe n with n ℕ.≟ length (Enumeration.list (neighboringMines grid coords))
...             | yes n≡len = yes (neighboringMines grid coords , n≡len)
...             | no  n≢len = no  λ { (mines′ , n≡len) → n≢len (begin
  n
    ≡⟨ n≡len ⟩
  length (Enumeration.list mines′)
    ≡⟨ Enum.enumeration-length-uniform mines′ (neighboringMines grid coords) ⟩
  length (Enumeration.list (neighboringMines grid coords)) ∎) }
  where open ≡-Reasoning
