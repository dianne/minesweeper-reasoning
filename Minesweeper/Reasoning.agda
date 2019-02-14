-- the goal of this module is to present inductive tools for reasoning about minesweeper, similar to the axioms ProofSweeper provides,
-- and prove them sound and complete with respect to our formulation of minesweeper.

module Minesweeper.Reasoning where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (there-injective)
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.Product as Σ
open import Data.Product.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Function
open import Function.Inverse as Inverse using (_↔_)

open import Data.Fin using (Fin)
open import Minesweeper.Enumeration as Enum using (Enumeration)
open import Minesweeper.Coords as Coords using (Coords ; Neighbor ; neighbors)
open import Minesweeper.Board as Board using (Board ; _Neighboring_on_ ; lookup ; _[_]≔_)
open import Minesweeper.Rules
open import Minesweeper.Moves

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
    neighborGuesses : List Guess
    neighborsKnown★ : Pointwise (λ neighbor guess → grid [ proj₁ neighbor ]↝★ guess) (Enumeration.list (neighbors coords)) neighborGuesses
    disparity : supposedMineCount ≢ List.length (List.filter (mine⚐ ≟⚐_) neighborGuesses)

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
  List.length (Enumeration.list (neighboringMines grid′ testCoords))
    ≡⟨ mineCountsConsistent neighborsKnown★ ⟩
  List.length (List.filter (mine⚐ ≟⚐_) neighborGuesses) ∎))
  where
  open ≡-Reasoning
  open Contradiction contradiction renaming (coords to testCoords ; coords-mineCount to testCoords-mineCount)
  open Enum.Filter {A = Neighbor testCoords} (λ { (neighbor , _) → mine⚐ ⚐✓? (lookup neighbor grid′) }) renaming (Σfilter to filterMines)

  mineCountsConsistent : ∀ {neighbors : List (Neighbor testCoords)} {guesses} → Pointwise (λ neighbor guess → grid [ proj₁ neighbor ]↝★ guess) neighbors guesses →
    List.length (filterMines neighbors) ≡ List.length (List.filter (mine⚐ ≟⚐_) guesses)
  mineCountsConsistent [] = refl
  mineCountsConsistent {(neighbor , _) ∷ _} (neighbor↝★guess ∷ _) with mine⚐ ⚐✓? (lookup neighbor grid′) | ★⇒✓ _ _ neighbor↝★guess _ grid↝⊞grid′ grid′✓
  mineCountsConsistent {(neighbor , _) ∷ _} (_ ∷ _)                  | yes mine⚐✓tile | guess⚐✓tile with lookup neighbor grid′
  mineCountsConsistent                      (_ ∷ neighbors↝★guesses) | yes ⚐✓mine     | ⚐✓mine         | .mine = cong suc (mineCountsConsistent neighbors↝★guesses)
  mineCountsConsistent {(neighbor , _) ∷ _} (_ ∷ _)                  | no ¬mine⚐✓tile | guess⚐✓tile with lookup neighbor grid′ | ¬-⚐✓-invert ¬mine⚐✓tile
  mineCountsConsistent                      (_ ∷ neighbors↝★guesses) | no ¬mine⚐✓tile | ⚐✓safe .n      | .(safe n)             | ⚐✓safe n = mineCountsConsistent neighbors↝★guesses

  testCoords-mineCount✓ : supposedMineCount ≡ List.length (Enumeration.list (neighboringMines grid′ testCoords))
  testCoords-mineCount✓ with known-safe-✓ testCoords grid grid′ testCoords-mineCount grid↝⊞grid′ grid′✓
  ... | mines′ , supposedMineCount≡length-mines′ =
    trans supposedMineCount≡length-mines′ (Enum.enumeration-length-uniform mines′ (neighboringMines grid′ testCoords))



-- now we'll also show that some familiar reasoning principles used in proofsweeper are sound
-- (and thus as a corrollary of the completeness of `_[_]↝★_`, they can be expressed in terms of those rules).
-- our core lemma: if a list of mines or safe tiles neighboring some coordinates agrees in length with the
-- complete list of such neighboring tiles in a filled board, then any other neighbor not in that list
-- must be of the opposite tile type
neighborsAlreadyFull : ∀ {bounds} (grid : Board Tile bounds) grid′ coords (other : Neighbor coords) guess
  (every : Enumeration ((guess ⚐✓_) Neighboring coords on grid′)) →
  (neighbors : List (Neighbor coords)) →
  (∀ {neighbor} (ix₁ ix₂ : neighbor ∈ neighbors) → ix₁ ≡ ix₂) →
  All (λ neighbor → grid [ proj₁ neighbor ]↝✓ guess) neighbors →
  All (λ neighbor → proj₁ other ≢ proj₁ neighbor) neighbors →
  grid ↝⊞ grid′ → grid′ ✓ →
  List.length neighbors ≡ List.length (Enumeration.list every) →
    invert⚐ guess ⚐✓ lookup (proj₁ other) grid′
neighborsAlreadyFull grid grid′ coords other guess every neighbors neighbors-unique neighbors↝✓guess other∉neighbors grid↝⊞grid′ grid′✓ lengths-agree = ¬-⚐✓-invert ¬other↦guess where
  -- to see that `neighbors` is the complete list of `coords`' neighbors of type `guess`, we first need to inductively verify✓ that `guess` indeed holds for them.
  neighbors★⇒✓ : ∀ {neighbors : List (Neighbor coords)} → All (λ elem → grid [ proj₁ elem ]↝✓ guess) neighbors → List ((guess ⚐✓_) Neighboring coords on grid′)
  neighbors★⇒✓ {_} [] = []
  neighbors★⇒✓ {neighbor ∷ _} (neighbor↝✓guess ∷ neighbors↝✓guess) = (neighbor , neighbor↝✓guess grid′ grid↝⊞grid′ grid′✓) ∷ neighbors★⇒✓ neighbors↝✓guess

  neighbors✓ : List (Σ[ neighbor ∈ Neighbor coords ] (guess ⚐✓ lookup (proj₁ neighbor) grid′))
  neighbors✓ = neighbors★⇒✓ neighbors↝✓guess

  -- `neighbors✓` has unique entries since `neighbors` does. we need a couple helpers first to see the connection, though
  ∈-neighbors★⇒✓⁻ : ∀ {neighbors neighbor neighbor✓} neighbors-valid★ →
    (neighbor , neighbor✓) ∈ neighbors★⇒✓ {neighbors} neighbors-valid★ →
      neighbor ∈ neighbors
  ∈-neighbors★⇒✓⁻ [] ()
  ∈-neighbors★⇒✓⁻ (_ ∷ neighbors-valid★) (here refl) = here refl
  ∈-neighbors★⇒✓⁻ (_ ∷ neighbors-valid★) (there ix)  = there (∈-neighbors★⇒✓⁻ neighbors-valid★ ix)

  ∈-neighbors★⇒✓⁻-injective : ∀ {neighbors neighbor✓} neighbors-valid★ (ix₁ ix₂ : neighbor✓ ∈ neighbors★⇒✓ {neighbors} neighbors-valid★) →
    ∈-neighbors★⇒✓⁻ neighbors-valid★ ix₁ ≡ ∈-neighbors★⇒✓⁻ neighbors-valid★ ix₂ →
      ix₁ ≡ ix₂
  ∈-neighbors★⇒✓⁻-injective [] () ix₂ ★⇒✓⁻₁≡★⇒✓⁻₂
  ∈-neighbors★⇒✓⁻-injective (_ ∷ neighbors-valid★) (here refl) (here refl) ★⇒✓⁻₁≡★⇒✓⁻₂ = refl
  ∈-neighbors★⇒✓⁻-injective (_ ∷ neighbors-valid★) (here refl) (there _) ()
  ∈-neighbors★⇒✓⁻-injective (_ ∷ neighbors-valid★) (there _) (here refl) ()
  ∈-neighbors★⇒✓⁻-injective (_ ∷ neighbors-valid★) (there ix₁) (there ix₂) ★⇒✓⁻₁≡★⇒✓⁻₂ = cong there (∈-neighbors★⇒✓⁻-injective neighbors-valid★ ix₁ ix₂ (there-injective ★⇒✓⁻₁≡★⇒✓⁻₂))

  neighbors✓-unique : ∀ {neighbor✓} (ix₁ ix₂ : neighbor✓ ∈ neighbors✓) → ix₁ ≡ ix₂
  neighbors✓-unique ix₁ ix₂ = ∈-neighbors★⇒✓⁻-injective _ ix₁ ix₂ (neighbors-unique (∈-neighbors★⇒✓⁻ _ ix₁) (∈-neighbors★⇒✓⁻ _ ix₂))

  -- `neighbors★⇒✓` preserves length so `neighbor✓` is the same length as `Neighbors★.list neighbors★`
  length-neighbors★⇒✓ : ∀ {neighbors} neighbors-valid★ → List.length (neighbors★⇒✓ {neighbors} neighbors-valid★) ≡ List.length neighbors
  length-neighbors★⇒✓ [] = refl
  length-neighbors★⇒✓ (_ ∷ neighbors★-valid) = cong suc (length-neighbors★⇒✓ neighbors★-valid)

  -- because its elements are unique and it's as long as the complete list of all neighbors of type `guess`, `neighbors✓` is also complete
  neighbors✓-complete : ∀ neighbor✓ → neighbor✓ ∈ neighbors✓
  neighbors✓-complete = Enum.long-list-complete every neighbors✓ neighbors✓-unique (begin
    List.length neighbors✓
      ≡⟨ length-neighbors★⇒✓ neighbors↝✓guess ⟩
    List.length neighbors
      ≡⟨ lengths-agree ⟩
    List.length (Enumeration.list every) ∎)
    where open ≡-Reasoning

  -- `other` is not of type `guess`: it isn't in `neighbors`, so it isn't in `neighbors✓`, which is complete
  ¬other↦guess : ¬ guess ⚐✓ lookup (proj₁ other) grid′
  ¬other↦guess other↦guess = All¬⇒¬Any other∉neighbors (Any.map (cong proj₁) (∈-neighbors★⇒✓⁻ _ (neighbors✓-complete (other , other↦guess))))

-- from this we get that, given a safe tile with as many adjacent mines as it can have, its other neighbors must be safe
otherNeighborIsSafe : ∀ {bounds} (grid : Board Tile bounds) neighborMineCount otherNeighbor
  (safeCoords : (known (safe neighborMineCount) ≡_) Neighboring otherNeighbor on grid)
  (neighborMines : List (Neighbor (proj₁ (proj₁ safeCoords)))) →
  (∀ {neighbor} (ix₁ ix₂ : neighbor ∈ neighborMines) → ix₁ ≡ ix₂) →
  All (λ neighbor → grid [ proj₁ neighbor ]↝✓ mine⚐) neighborMines →
  All (λ neighbor → otherNeighbor ≢ proj₁ neighbor) neighborMines →
  List.length neighborMines ≡ neighborMineCount →
    grid [ otherNeighbor ]↝✓ safe⚐
otherNeighborIsSafe grid neighborMineCount otherNeighbor ((safeCoords , safeCoords-Adj) , safeCoords-safe) neighborMines neighborMines-unique neighborMines↝✓mine⚐ otherNeighbor∉neighborMines neighborMines-length grid′ grid↝⊞grid′ grid′✓
  with known-safe-✓ safeCoords grid grid′ (sym safeCoords-safe) grid↝⊞grid′ grid′✓
...  | mineEnumeration , neighborMineCount≡enumLength =
  neighborsAlreadyFull grid grid′ safeCoords (otherNeighbor , Coords.Adjacent-sym otherNeighbor safeCoords safeCoords-Adj) mine⚐ mineEnumeration neighborMines neighborMines-unique neighborMines↝✓mine⚐ otherNeighbor∉neighborMines grid↝⊞grid′ grid′✓ enoughMines
  where
    enoughMines : List.length neighborMines ≡ List.length (Enumeration.list mineEnumeration)
    enoughMines = trans neighborMines-length neighborMineCount≡enumLength

-- and likewise, given a safe tile with as many adjacent safe tiles as it can have, its other niehgbors must be mines
otherNeighborIsMine : ∀ {bounds} (grid : Board Tile bounds) neighborMineCount otherNeighbor
  (safeCoords : (known (safe neighborMineCount) ≡_) Neighboring otherNeighbor on grid)
  (neighborSafes : List (Neighbor (proj₁ (proj₁ safeCoords)))) →
  (∀ {neighbor} (ix₁ ix₂ : neighbor ∈ neighborSafes) → ix₁ ≡ ix₂) →
  All (λ neighbor → grid [ proj₁ neighbor ]↝✓ safe⚐) neighborSafes →
  All (λ neighbor → otherNeighbor ≢ proj₁ neighbor) neighborSafes →
  List.length neighborSafes + neighborMineCount ≡ List.length (Enumeration.list (neighbors (proj₁ (proj₁ safeCoords)))) →
    grid [ otherNeighbor ]↝✓ mine⚐
otherNeighborIsMine grid neighborMineCount otherNeighbor ((safeCoords , safeCoords-Adj) , safeCoords-safe) neighborSafes neighborSafes-unique neighborSafes↝✓safe⚐ otherNeighbor∉neighborSafes neighborSafes-length grid′ grid↝⊞grid′ grid′✓
  with known-safe-✓ safeCoords grid grid′ (sym safeCoords-safe) grid↝⊞grid′ grid′✓
...  | mineEnumeration , neighborMineCount≡enumLength =
  neighborsAlreadyFull grid grid′ safeCoords (otherNeighbor , Coords.Adjacent-sym otherNeighbor safeCoords safeCoords-Adj) safe⚐ safeEnumeration neighborSafes neighborSafes-unique neighborSafes↝✓safe⚐ otherNeighbor∉neighborSafes grid↝⊞grid′ grid′✓ enoughSafes
  where
    -- since the number of safe neighbors a tile has is defined by how many are left when you take away the mines,
    -- we need to do a bit of arithmetic--splitting all of safeNeighbor's neighbors into safe tiles and mines--to see that our list really has all of them
    splitNeighbors : Enumeration ((safe⚐ ⚐✓_) Neighboring safeCoords on grid′) × Enumeration ((mine⚐ ⚐✓_) Neighboring safeCoords on grid′)
    splitNeighbors = Enum.partition ⚐✓-irrelevance ⚐✓-irrelevance (tileType ∘ flip lookup grid′ ∘ proj₁) guessesDisjoint (neighbors safeCoords)

    safeEnumeration : Enumeration ((safe⚐ ⚐✓_) Neighboring safeCoords on grid′)
    safeEnumeration = proj₁ splitNeighbors

    enoughSafes : List.length neighborSafes ≡ List.length (Enumeration.list safeEnumeration)
    enoughSafes = +-cancelʳ-≡ (List.length neighborSafes) (List.length (Enumeration.list safeEnumeration)) length-splitNeighbors where
      open ≡-Reasoning
      length-splitNeighbors : List.length neighborSafes + neighborMineCount ≡ List.length (Enumeration.list safeEnumeration) + neighborMineCount
      length-splitNeighbors = begin
        List.length neighborSafes + neighborMineCount
          ≡⟨ neighborSafes-length ⟩
        List.length (Enumeration.list (neighbors safeCoords))
           ≡⟨ Enum.length-partition ⚐✓-irrelevance ⚐✓-irrelevance (tileType ∘ flip lookup grid′ ∘ proj₁) guessesDisjoint (neighbors safeCoords) ⟩
        List.length (Enumeration.list safeEnumeration) + List.length (Enumeration.list (proj₂ splitNeighbors))
          ≡⟨ cong (List.length (Enumeration.list safeEnumeration) +_) (Enum.enumeration-length-uniform (proj₂ splitNeighbors) mineEnumeration) ⟩
        List.length (Enumeration.list safeEnumeration) + List.length (Enumeration.list mineEnumeration)
          ≡⟨ cong (List.length (Enumeration.list safeEnumeration) +_) (sym neighborMineCount≡enumLength) ⟩
        List.length (Enumeration.list safeEnumeration) + neighborMineCount ∎
