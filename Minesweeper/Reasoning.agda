-- the goal of this module is to present inductive tools for reasoning about minesweeper, similar to the axioms ProofSweeper provides,
-- and prove them sound and complete with respect to our formulation of minesweeper.

module Minesweeper.Reasoning where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product as Σ
open import Data.Product.Properties
open import Data.Product.Relation.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin.Properties as Fin
open import Data.Fin using (Fin; zero; suc)
open import Function
open import Function.Equality                 using (_⟨$⟩_)
open import Function.Equivalence              using (_⇔_; equivalence) 
open import Function.Injection  as Injection  using (Injection)
open import Function.Surjection as Surjection using (Surjective)
open import Function.Inverse    as Inverse    using (Inverse)

open import Minesweeper.Enumeration as Enum using (Enumeration)
open import Minesweeper.Coords as Coords using (Coords ; Neighbor)
open import Minesweeper.Board as Board using (Board ; _Neighboring_on_ ; lookup ; _[_]≔_)
open import Minesweeper.Rules
open import Minesweeper.Moves

open Enumeration using (cardinality)


-- our inductive family for minesweeper proofs!
data _[_]↝★_ {bounds} (grid : Board Tile bounds) (coords : Coords bounds) : Guess → Set
record Contradiction {bounds} (grid : Board Tile bounds) : Set

-- noticing contradictions lets us narrow our resoning by dismissing impossible board states.
-- here we define a contradiction as the existence of a known safe tile whose neighbors we can identify
-- and whose reported neighboring mine count does not match with the number of mines among those neighbors.
record Contradiction {bounds} grid where
  inductive
  field
    coords : Coords bounds
    supposedMineCount : ℕ
    coords-mineCount : lookup coords grid ≡ known (safe supposedMineCount)
    neighborGuesses : Fin (cardinality (Coords.neighbors coords)) → Guess
    neighborsKnown★ : ∀ i → grid [ proj₁ (Inverse.to (Enumeration.lookup (Coords.neighbors coords)) ⟨$⟩ i) ]↝★ neighborGuesses i
    disparity : supposedMineCount ≢ Enum.count (mine⚐ ≟⚐_) neighborGuesses

data _[_]↝★_ {bounds} grid coords where
  -- known tiles already have a proven identity
  known★ : ∀ tile guess → lookup coords grid ≡ known tile → guess ⚐✓ tile → grid [ coords ]↝★ guess

  -- case analysis: in a filled board the tile at `testCoords` will either be safe or a mine, so if we can
  -- prove that our `guess` holds for the tile at `coords` regardless of which of those it is, then it will always hold.
  cases★ : ∀ testCoords guess →
    (∀ tile → (grid [ testCoords ]≔ known tile) [ coords ]↝★ guess) →
      grid [ coords ]↝★ guess

  -- ex falso quodlibet: a board with a contradiction in it has no way of being filled in, so it doesn't matter what we say about it.
  exfalso★ : ∀ guess → Contradiction grid → grid [ coords ]↝★ guess


-- let's do soundness first!
-- roughly, this says that if you use the rules given by _[_]↝★_ to determine whether a tile is safe or a mine,
-- it will indeed be that, for every possible way the unknown board tiles could be "filled in"
★⇒✓ : ∀ {bounds guess} (grid : Board Tile bounds) coords → grid [ coords ]↝★ guess → grid [ coords ]↝✓ guess

-- when the tile we're looking at is already known, it will stay the same in all ways of completing the board.
-- so as long as our guess agrees with its current state, it's valid
★⇒✓ grid coords (known★ tile guess coords↦tile guess⚐✓tile) grid′ grid↝⊞grid′ grid′✓ = subst (guess ⚐✓_) (known-↝▣⇒≡ coords↦tile (grid↝⊞grid′ coords)) guess⚐✓tile

-- for a proof by cases★ on the final board, only the case that applies to our actual final board `grid′` applies
★⇒✓ grid coords (cases★ testCoords guess cases) grid′ grid↝⊞grid′ grid′✓ = ★⇒✓ _ _ (cases (lookup testCoords grid′)) grid′ gridWithTest↝⊞grid′ grid′✓ where
  -- proofs by case analysis include information gained from which case is being inspected in the `grid`.
  -- in the relevant case, our updated `grid` still can complete to `grid′`:
  gridWithTest↝⊞grid′ : (grid [ testCoords ]≔ known (lookup testCoords grid′)) ↝⊞ grid′
  gridWithTest↝⊞grid′ coords′ with coords′ Coords.≟ testCoords
  -- at the test coordinates, it updates to be the known tile at those coordinates on `grid′`, which is present on `grid′`
  ... | yes refl rewrite Board.lookup∘update coords′ grid (known (lookup coords′ grid′)) = ↝▣known (lookup coords′ grid′)
  -- and elsewhere it is the same as in `grid`, which is compatible with `grid′` by our assumption `grid↝⊞grid′` that `grid` and `grid′` are compatible
  ... | no coords′≢testCoords rewrite Board.lookup∘update′ coords′≢testCoords grid (known (lookup testCoords grid′)) = grid↝⊞grid′ coords′

-- when we have a Contradiction, there's no valid completion of our board; consequently, any guess will hold, vacuously
★⇒✓ grid coords (exfalso★ guess contradiction) grid′ grid↝⊞grid′ grid′✓ = ⊥-elim (disparity (begin
  supposedMineCount
    ≡⟨ testCoords-mineCount✓ ⟩
  cardinality (neighboringMines grid′ testCoords)
    ≡⟨ Enum.count-≡ _ _ _ _ (λ i → guesses-agree✓ (★⇒✓ _ _ (neighborsKnown★ i) _ grid↝⊞grid′ grid′✓)) ⟩
  Enum.count (mine⚐ ≟⚐_) neighborGuesses ∎))
  where
  open ≡-Reasoning
  open Contradiction contradiction renaming (coords to testCoords ; coords-mineCount to testCoords-mineCount)

  guesses-agree✓ : ∀ {guess tile} → guess ⚐✓ tile → mine⚐ ⚐✓ tile ⇔ mine⚐ ≡ guess
  guesses-agree✓ ⚐✓mine     = equivalence (const refl) (const ⚐✓mine)
  guesses-agree✓ (⚐✓safe n) = equivalence (λ ())       (λ ())

  testCoords-mineCount✓ : supposedMineCount ≡ cardinality (neighboringMines grid′ testCoords)
  testCoords-mineCount✓ with known-safe-✓ testCoords grid grid′ testCoords-mineCount grid↝⊞grid′ grid′✓
  ... | mines′ , supposedMineCount≡cardinality-mines′ =
    trans supposedMineCount≡cardinality-mines′ (Enum.cardinality-≡ mines′ (neighboringMines grid′ testCoords))



-- now we'll also show that some familiar reasoning principles used in proofsweeper are sound
-- (and thus as a corrollary of the completeness of `_[_]↝★_`, they can be expressed in terms of those rules).
-- specifically, we want to capture that if you have a known safe tile that already has as many adjacent safe
-- tiles or mines as it can, then any other tile neighboring it must be of the other sort. for representing
-- that conveniently, here's the following record: a given number of unique neighbors of a tile, all either
-- safe or mines, excluding some other tile (which we wish to prove is of the opposite type)
record _Unique_Neighboring_on_Excluding_ {bounds} (count : ℕ) (guess : Guess) (coords : Coords bounds) (grid : Board Tile bounds) (other : Coords bounds) : Set where
  field
    neighbors : Injection (Fin.setoid count) (Neighbor coords)
    neighbors↝✓guess : ∀ i → grid [ proj₁ (Injection.to neighbors ⟨$⟩ i) ]↝✓ guess
    other∉neighbors  : ∀ i → proj₁ (Injection.to neighbors ⟨$⟩ i) ≢ other

-- our core lemma: if a list of mines or safe tiles neighboring some coordinates agrees in length with the
-- complete list of such neighboring tiles in a filled board, then any other neighbor not in that list
-- must be of the opposite tile type
neighborsAlreadyFull : ∀ {bounds} (grid : Board Tile bounds) grid′ coords (other : Setoid.Carrier (Neighbor coords)) guess
  (every : Enumeration ((guess ⚐✓_) Neighboring coords on grid′)) →
  cardinality every Unique guess Neighboring coords on grid Excluding proj₁ other →
  grid ↝⊞ grid′ →
  grid′ ✓ →
    invert⚐ guess ⚐✓ lookup (proj₁ other) grid′
neighborsAlreadyFull grid grid′ coords other guess every neighbors′ grid↝⊞grid′ grid′✓ = ¬-⚐✓-invert ¬other↦guess where
  open _Unique_Neighboring_on_Excluding_ neighbors′

  -- by observing that `neighbors`'s elements are of type `guess` and there are as many of them as there are neighbors of `coords` in `grid′`,
  -- we can see that `neighbors` contains every `guess`-type neighbor of `coords`
  neighbors✓ : Injection (Fin.setoid (cardinality every)) ((guess ⚐✓_) Neighboring coords on grid′)
  neighbors✓ = record
    { to = →-to-⟶ λ i → Injection.to neighbors ⟨$⟩ i , neighbors↝✓guess i grid′ grid↝⊞grid′ grid′✓
    ; injective = Injection.injective neighbors }

  neighbors✓-full : Surjective (Injection.to neighbors✓)
  neighbors✓-full = Enum.injection-surjective every neighbors✓

  -- `other` is not of type `guess`: it isn't in `neighbors`, so it isn't in `neighbors✓`, which it would be if it was of type `guess`
  ¬other↦guess : ¬ guess ⚐✓ lookup (proj₁ other) grid′
  ¬other↦guess other↦guess = other∉neighbors
    (Surjective.from neighbors✓-full ⟨$⟩ (other , other↦guess))
    (≡×≡⇒≡ (Surjective.right-inverse-of neighbors✓-full (other , other↦guess)))

-- from this we get that, given a safe tile with as many adjacent mines as it can have, its other neighbors must be safe
otherNeighborIsSafe : ∀ {bounds} (grid : Board Tile bounds) neighborMineCount otherNeighbor
  (safeCoords : Setoid.Carrier ((known (safe neighborMineCount) ≡_) Neighboring otherNeighbor on grid)) →
  neighborMineCount Unique mine⚐ Neighboring proj₁ (proj₁ safeCoords) on grid Excluding otherNeighbor →
    grid [ otherNeighbor ]↝✓ safe⚐
otherNeighborIsSafe grid neighborMineCount otherNeighbor ((safeCoords , safeCoords-Adj) , safeCoords-safe) neighborMines grid′ grid↝⊞grid′ grid′✓
  with known-safe-✓ safeCoords grid grid′ (sym safeCoords-safe) grid↝⊞grid′ grid′✓
...  | mineEnumeration , neighborMineCount≡enumCardinality =
  neighborsAlreadyFull grid grid′ safeCoords (otherNeighbor , Coords.Adjacent-sym otherNeighbor safeCoords safeCoords-Adj)
    mine⚐
    mineEnumeration
    (subst _ neighborMineCount≡enumCardinality neighborMines)
    grid↝⊞grid′
    grid′✓

-- and likewise, given a safe tile with as many adjacent safe tiles as it can have, its other neighbors must be mines
otherNeighborIsMine : ∀ {bounds} (grid : Board Tile bounds) neighborMineCount otherNeighbor
  (safeCoords : Setoid.Carrier ((known (safe neighborMineCount) ≡_) Neighboring otherNeighbor on grid)) →
  (Coords.neighborCount (proj₁ (proj₁ safeCoords)) ∸ neighborMineCount) Unique safe⚐ Neighboring proj₁ (proj₁ safeCoords) on grid Excluding otherNeighbor →
    grid [ otherNeighbor ]↝✓ mine⚐
otherNeighborIsMine grid neighborMineCount otherNeighbor ((safeCoords , safeCoords-Adj) , safeCoords-safe) neighborSafes grid′ grid↝⊞grid′ grid′✓
  with known-safe-✓ safeCoords grid grid′ (sym safeCoords-safe) grid↝⊞grid′ grid′✓
...  | mineEnumeration , neighborMineCount≡enumCardinality =
  neighborsAlreadyFull grid grid′ safeCoords (otherNeighbor , Coords.Adjacent-sym otherNeighbor safeCoords safeCoords-Adj)
    safe⚐
    safeEnumeration
    (subst (_Unique safe⚐ Neighboring safeCoords on grid Excluding otherNeighbor) enoughSafes neighborSafes)
    grid↝⊞grid′
    grid′✓
  where
    -- since the number of safe neighbors a tile has is defined by how many are left when you take away the mines,
    -- we need to do a bit of arithmetic--splitting all of safeNeighbor's neighbors into safe tiles and mines--to see that our list really has all of them.
    safeEnumeration : Enumeration ((safe⚐ ⚐✓_) Neighboring safeCoords on grid′)
    safeEnumeration = Board.filterNeighbors (safe⚐ ⚐✓?_) grid′ safeCoords

    -- Enum.cardinality-partition gives us that the number total number of neighbors a tile has equals the sum of its safe and non-safe neighbors.
    -- this bijection gets us the rest of the way there: the non-safe neighbors and mines are the same:
    mine⚐↔¬safe⚐ : Inverse ((mine⚐ ⚐✓_) Neighboring safeCoords on grid′) ((¬_ ∘ (safe⚐ ⚐✓_)) Neighboring safeCoords on grid′)
    mine⚐↔¬safe⚐ = record
      { to   = record { _⟨$⟩_ = Σ.map₂ mine⚐⇒¬safe⚐ ; cong = id }
      ; from = record { _⟨$⟩_ = Σ.map₂ ¬safe⚐⇒mine⚐ ; cong = id }
      ; inverse-of = record
        { left-inverse-of  = λ _ → refl , refl
        ; right-inverse-of = λ _ → refl , refl } }
      where
      mine⚐⇒¬safe⚐ : ∀ {tile} → mine⚐ ⚐✓ tile → ¬ safe⚐ ⚐✓ tile
      mine⚐⇒¬safe⚐ ⚐✓mine ()
      ¬safe⚐⇒mine⚐ : ∀ {tile} → ¬ safe⚐ ⚐✓ tile → mine⚐ ⚐✓ tile
      ¬safe⚐⇒mine⚐ {mine}   ¬safe⚐ = ⚐✓mine
      ¬safe⚐⇒mine⚐ {safe n} ¬safe⚐ = ⊥-elim (¬safe⚐ (⚐✓safe n))

    enoughSafes : Coords.neighborCount safeCoords ∸ neighborMineCount ≡ cardinality safeEnumeration
    enoughSafes = begin
      Coords.neighborCount safeCoords ∸ neighborMineCount                                     ≡⟨ cong (_∸ neighborMineCount)
                                                                                                   (Enum.cardinality-partition
                                                                                                     (subst ((safe⚐ ⚐✓_) ∘ flip lookup grid′) ∘ ≡×≡⇒≡)
                                                                                                     (Coords.neighbors safeCoords)
                                                                                                     safeEnumeration
                                                                                                     (Enum.map mine⚐↔¬safe⚐ mineEnumeration)) ⟩
      cardinality safeEnumeration + cardinality mineEnumeration ∸ neighborMineCount           ≡⟨ cong (cardinality safeEnumeration + cardinality mineEnumeration ∸_)
                                                                                                   neighborMineCount≡enumCardinality ⟩
      cardinality safeEnumeration + cardinality mineEnumeration ∸ cardinality mineEnumeration ≡⟨ m+n∸n≡m (cardinality safeEnumeration) (cardinality mineEnumeration) ⟩
      cardinality safeEnumeration ∎
      where open ≡-Reasoning
