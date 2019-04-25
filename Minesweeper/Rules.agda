-- here we describe the "rules" of minesweeper,
-- or what it means for the tiles of an entirely known board to be consistent with each other

module Minesweeper.Rules where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat as ℕ using (ℕ)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Unary  renaming (Decidable to Decidable₁; Irrelevant to Irrelevant₁)
open import Relation.Binary renaming (Decidable to Decidable₂; Irrelevant to Irrelevant₂)
open import Relation.Binary.PropositionalEquality

open import Minesweeper.Coords
open import Minesweeper.Board
open import Minesweeper.Enumeration as Enum using (Enumeration)

-- KnownTile represents the tiles of a completely filled board:
-- they're all either mines, or safe tiles labeled with how many mines there are adjacent to them
data KnownTile : Set where
  mine : KnownTile
  safe : ℕ → KnownTile

-- Guess represents the type of a tile. the name is due to how they're used to reason about the identities of unknown tiles,
-- since a `safe⚐` guess could correspond to a safe tile `safe n` for any `n`. following the name, the "⚐" mnemonic is meant
-- to evoke placing flags over unknown tiles with mines in Windows minesweeper to mark them as such.
data Guess : Set where
  mine⚐ : Guess
  safe⚐ : Guess

-- guessing: is a guess of a tile's type valid for that tile?
data _⚐✓_ : Guess → KnownTile → Set where
  ⚐✓mine : mine⚐ ⚐✓ mine
  ⚐✓safe : ∀ n → safe⚐ ⚐✓ safe n


-- consistency: `grid [ coords ]✓` means that if `grid` has a safe tile at `coords`, then the number on it agrees with the number of mines adjacent to it.
-- since only safe tiles are checked in this way, coordinates with mines are always regarded as valid, regardless of if they have adjacent inconsistent safe tiles.
_[_]✓ : ∀ {bounds} → Board KnownTile bounds → Coords bounds → Set
_[_]✓ {bounds} grid coords with lookup coords grid
... | mine = ⊤
... | safe n = Σ[ neighboringMines ∈ Enumeration ((mine⚐ ⚐✓_) Neighboring coords on grid) ] n ≡ Enumeration.cardinality neighboringMines

-- a board `grid` is consistent (written `grid ✓`) if every tile on it is consistent with its neighbors
_✓ : ∀ {bounds} → Board KnownTile bounds → Set
_✓ {bounds} grid = ∀ coords → grid [ coords ]✓


_⚐✓?_ : Decidable₂ (_⚐✓_)
mine⚐ ⚐✓? mine   = yes ⚐✓mine
mine⚐ ⚐✓? safe _ = no λ { () }
safe⚐ ⚐✓? mine   = no λ { () }
safe⚐ ⚐✓? safe n = yes (⚐✓safe n)

_≟⚐_ : Decidable₂ (_≡_ {A = Guess})
mine⚐ ≟⚐ mine⚐ = yes refl
mine⚐ ≟⚐ safe⚐ = no λ ()
safe⚐ ≟⚐ mine⚐ = no λ ()
safe⚐ ≟⚐ safe⚐ = yes refl

tileType : KnownTile → Guess
tileType mine     = mine⚐
tileType (safe _) = safe⚐

tileType-⚐✓ : ∀ tile → tileType tile ⚐✓ tile
tileType-⚐✓ mine     = ⚐✓mine
tileType-⚐✓ (safe n) = ⚐✓safe n

neighboringMines : ∀ {bounds} (grid : Board KnownTile bounds) (coords : Coords bounds) → Enumeration ((mine⚐ ⚐✓_) Neighboring coords on grid)
neighboringMines = filterNeighbors (mine⚐ ⚐✓?_)

_[_]✓? : ∀ {bounds} → Decidable₂ (_[_]✓ {bounds})
grid [ coords ]✓? with lookup coords grid
... | mine = yes tt
... | safe n with n ℕ.≟ Enumeration.cardinality (neighboringMines grid coords)
...             | yes n≡len = yes (neighboringMines grid coords , n≡len)
...             | no  n≢len = no  λ { (mines′ , n≡len) → n≢len (begin
  n
    ≡⟨ n≡len ⟩
  Enumeration.cardinality mines′
    ≡⟨ Enum.cardinality-≡ mines′ (neighboringMines grid coords) ⟩
  Enumeration.cardinality (neighboringMines grid coords) ∎) }
  where open ≡-Reasoning

_✓? : ∀ {bounds} → Decidable₁ (_✓ {bounds})
grid ✓? = all? (grid [_]✓?)

-- if a board is *not* valid, then there must be a specific safe tile on it whose label does not match the number of mines neighboring it
identify-contradiction : ∀ {bounds} (grid : Board KnownTile bounds) →
  ¬ grid ✓ → ∃[ coords ] (¬ grid [ coords ]✓)
identify-contradiction grid ¬grid✓ = ¬∀⟶∃¬ _ (grid [_]✓) (grid [_]✓?) ¬grid✓
