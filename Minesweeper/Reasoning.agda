-- here, inspired by proofsweeper, we present inductive rules for describing valid minesweeper moves, and prove them
-- equivalent to the direct definition of move validity in Moves.agda. then, as a corollary, at the end of this module,
-- we prove that some principles closer to the rules used in proofsweeper also also sound.

module Minesweeper.Reasoning where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Product as Σ
open import Data.Product.Properties
open import Data.Product.Relation.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Sum
open import Data.Nat hiding (_>_)
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


-- our inductive family for proofs that minesweeper moves are valid!
data _[_]↝★_ {bounds} (grid : Board Tile bounds) (coords : Coords bounds) : Guess → Set
record Contradiction {bounds} (grid : Board Tile bounds) : Set

-- noticing contradictions lets us narrow our resoning by dismissing impossible board states.
-- here we define a contradiction as the existence of a known safe tile whose neighbors we can identify
-- and whose reported neighboring mine count does not match with the number of mines among that provided list of neighbors.
record Contradiction {bounds} grid where
  inductive
  field
    coords : Coords bounds
    supposedMineCount : ℕ
    coords-mineCount : lookup grid coords ≡ known (safe supposedMineCount)
    neighborGuesses : Fin (cardinality (Coords.neighbors coords)) → Guess
    neighborsKnown★ : ∀ i → grid [ proj₁ (Inverse.to (Enumeration.lookup (Coords.neighbors coords)) ⟨$⟩ i) ]↝★ neighborGuesses i
    disparity : supposedMineCount ≢ Enum.count (mine⚐ ≟⚐_) neighborGuesses

data _[_]↝★_ {bounds} grid coords where
  -- known tiles already have a proven identity
  known★ : ∀ tile guess → lookup grid coords ≡ known tile → guess ⚐✓ tile → grid [ coords ]↝★ guess

  -- case analysis: in a filled board the tile at `testCoords` will either be safe or a mine, so if we can
  -- prove that our `guess` holds for the tile at `coords` regardless of which of those it is, then it will always hold.
  cases★ : ∀ testCoords guess →
    (∀ tile → (grid [ testCoords ]≔ known tile) [ coords ]↝★ guess) →
      grid [ coords ]↝★ guess

  -- ex falso quodlibet: a board with a contradiction in it has no way of being filled in, so it doesn't matter what we say about it.
  exfalso★ : ∀ guess → Contradiction grid → grid [ coords ]↝★ guess



-- let's do soundness first!
-- roughly, this says that if you use the rules given by _[_]↝★_ to determine (or "guess") whether a tile is safe or a mine,
-- it will indeed be that, for every possible way the unknown board tiles could be "filled in"
★⇒✓ : ∀ {bounds guess} (grid : Board Tile bounds) coords → grid [ coords ]↝★ guess → grid [ coords ]↝✓ guess

-- if the tile we're looking at is already known, it will stay the same in all ways of completing the board,
-- so it's sound to use the known★ rule to guess that a tile has the type you already know it has.
★⇒✓ grid coords (known★ tile guess coords↦tile guess⚐✓tile) grid′ grid↝⊞grid′ grid′✓ = subst (guess ⚐✓_) (known-↝▣⇒≡ coords↦tile (grid↝⊞grid′ coords)) guess⚐✓tile

-- when considering proofs formed with the cases★ rule, for any way of completing our board, we can see which case actually applies to that final board.
-- inductively, we may assume the proof given by that case is sound, so our guess holds for whichever tile we're looking at.
★⇒✓ grid coords (cases★ testCoords guess cases) grid′ grid↝⊞grid′ grid′✓ = ★⇒✓ _ _ (cases (lookup grid′ testCoords)) grid′ gridWithTest↝⊞grid′ grid′✓ where
  -- when looking at a specific case given by cases★, we update our board `grid` to include information about which case we're in.
  -- in order to show that the results we get from this still apply to whichever final board `grid′` we're looking at, we have the following lemma:
  gridWithTest↝⊞grid′ : (grid [ testCoords ]≔ known (lookup grid′ testCoords)) ↝⊞ grid′
  gridWithTest↝⊞grid′ coords′ with coords′ Coords.≟ testCoords
  -- at the test coordinates, we've updated the tile to be the known tile at those coordinates on `grid′`. this is fine since it's present on `grid′` by construction
  ... | yes refl rewrite Board.lookup∘update coords′ grid (known (lookup grid′ coords′)) = ↝▣known (lookup grid′ coords′)
  -- and elsewhere it is the same as in `grid`, which is compatible with `grid′` by our assumption `grid↝⊞grid′` that `grid` and `grid′` are compatible
  ... | no coords′≢testCoords rewrite Board.lookup∘update′ coords′≢testCoords grid (known (lookup grid′ testCoords)) = grid↝⊞grid′ coords′

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



-- _[_]↝★_ is complete with respect to _[_]↝✓_ !
-- roughly, this says that, given a partially filled board, and any tile on it that is either always safe or always a mine,
-- we can construct a proof that it always has that identity using only the rules given by _[_]↝★_
✓⇒★ : ∀ {bounds} (grid : Board Tile bounds) coords guess → grid [ coords ]↝✓ guess → grid [ coords ]↝★ guess

-- we proceed by induction on how "filled in" `grid` is. see the definition of _>_ in Minesweeper.Moves for more details
✓⇒★ {bounds} = >-rec _ ✓⇒★′ where
  ✓⇒★′ : ∀ (grid : Board Tile bounds) →
    (∀ filled → filled > grid → ∀ coords guess → filled [ coords ]↝✓ guess → filled [ coords ]↝★ guess) →
      ∀ coords guess → grid [ coords ]↝✓ guess → grid [ coords ]↝★ guess

  -- through case analysis, we can exhaustively consider every possible choice until we've filled the entire board
  ✓⇒★′ grid ✓⇒★-rec coords guess coords↝✓guess with holey⊎filled grid

  -- if there's an unfilled tile left, we can apply the `cases★` rule to consider all possible ways of filling it
  ✓⇒★′ grid ✓⇒★-rec coords guess coords↝✓guess | inj₁ (unfilledCoords , unfilledCoords-unknown) =
    cases★ unfilledCoords guess
      λ tile → ✓⇒★-rec
        (grid [ unfilledCoords ]≔ known tile)
        (fill-> unfilledCoords grid tile unfilledCoords-unknown)
        coords
        guess
        λ fullyFilled filled↝⊞fullyFilled fullyFilled✓ → coords↝✓guess
          fullyFilled
          (≥-↝⊞-trans (grid [ unfilledCoords ]≔ known tile) grid (>⇒≥ (fill-> unfilledCoords grid tile unfilledCoords-unknown)) fullyFilled filled↝⊞fullyFilled)
          fullyFilled✓

  -- otherwise, `grid` is entirely filled. our assumption `coords↝✓guess` that `grid [ coords ]↝✓ guess` guarantees that
  -- if there are no contradictions in `grid`, then we can find `guess` at `coords`.
  ✓⇒★′ grid ✓⇒★-rec coords guess coords↝✓guess | inj₂ grid-filled with unwrap grid grid-filled ✓?

  -- in the case that `guess` can be found on `grid` at `coords`, we can use the `known★` rule
  ✓⇒★′ grid ✓⇒★-rec coords guess coords↝✓guess | inj₂ grid-filled | yes grid′✓ with coords↝✓guess (unwrap grid grid-filled) (↝⊞-unwrap grid grid-filled) grid′✓
  ... | guess⚐✓tile rewrite lookup∘unwrap grid grid-filled coords =
    known★ (proj₁ (grid-filled coords)) guess (proj₂ (grid-filled coords)) guess⚐✓tile

  -- otherwise, there must be a contradiction somewhere on `grid`, so we can use the `exfalso★` rule
  ✓⇒★′ grid ✓⇒★-rec coords guess coords↝✓guess | inj₂ grid-filled | no ¬grid′✓ with identify-contradiction (unwrap grid grid-filled) ¬grid′✓
  ... | badCoords , ¬grid′[badCoords]✓ rewrite lookup∘unwrap grid grid-filled badCoords with grid-filled badCoords

  -- the contradiction can't be at a mine, since only safe tiles are considered when determining if a board is consistent
  ... | mine , badCoords↦badTile = ⊥-elim (¬grid′[badCoords]✓ tt)

  -- at a safe tile reporting `n` neighboring mines, our assumption that there's a contradiction at that tile gives us that
  -- there is *no* `Enumeration` of its neighboring mines with cardinality `n`. we can use this to build a `Contradiction`
  -- in order to apply the `exfalso★` rule.
  ... | safe n , badCoords↦badTile =
    exfalso★ guess record
      { coords = badCoords
      ; supposedMineCount = n
      ; coords-mineCount = badCoords↦badTile
      ; neighborGuesses = neighborGuesses
      ; neighborsKnown★ = λ i →
        known★
          (proj₁ (neighbors-filled i))
          (neighborGuesses i)
          (proj₂ (neighbors-filled i))
          (tileType-⚐✓ _)
      ; disparity = n≢mineCount }
    where
      neighbors : Fin (Coords.neighborCount badCoords) → Coords bounds
      neighbors = proj₁ ∘ (Inverse.to (Enumeration.lookup (Coords.neighbors badCoords)) ⟨$⟩_)

      neighbors-filled : ∀ i → ∃[ tile ] (lookup grid (neighbors i) ≡ known tile)
      neighbors-filled = grid-filled ∘ neighbors

      neighborGuesses : Fin (Coords.neighborCount badCoords) → Guess
      neighborGuesses = tileType ∘ proj₁ ∘ neighbors-filled

      mineCounts-agree : Enum.count (mine⚐ ≟⚐_) neighborGuesses ≡ cardinality (neighboringMines (unwrap grid grid-filled) badCoords)
      mineCounts-agree = Enum.count-≡ _ _ _ _ (guesses-agree ∘ neighbors) where
        guesses-agree : ∀ coords → mine⚐ ≡ tileType (proj₁ (grid-filled coords)) ⇔ mine⚐ ⚐✓ lookup (unwrap grid grid-filled) coords
        guesses-agree coords rewrite lookup∘unwrap grid grid-filled coords with proj₁ (grid-filled coords)
        ...                                                                   | mine   = equivalence (const ⚐✓mine) (const refl)
        ...                                                                   | safe _ = equivalence (λ ())         (λ ())

      n≢mineCount : n ≢ Enum.count (mine⚐ ≟⚐_) neighborGuesses
      n≢mineCount = ¬grid′[badCoords]✓ ∘ (neighboringMines (unwrap grid grid-filled) badCoords ,_) ∘ flip trans mineCounts-agree



-- now we'll also show that some familiar reasoning principles used in proofsweeper are sound
-- (and thus as a corrollary of the completeness of `_[_]↝★_`, they can be expressed in terms of our inductive rules).
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
    invert⚐ guess ⚐✓ lookup grid′ (proj₁ other)
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
  ¬other↦guess : ¬ guess ⚐✓ lookup grid′ (proj₁ other)
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
                                                                                                     (subst ((safe⚐ ⚐✓_) ∘ lookup grid′) ∘ ≡×≡⇒≡)
                                                                                                     (Coords.neighbors safeCoords)
                                                                                                     safeEnumeration
                                                                                                     (Enum.map mine⚐↔¬safe⚐ mineEnumeration)) ⟩
      cardinality safeEnumeration + cardinality mineEnumeration ∸ neighborMineCount           ≡⟨ cong (cardinality safeEnumeration + cardinality mineEnumeration ∸_)
                                                                                                   neighborMineCount≡enumCardinality ⟩
      cardinality safeEnumeration + cardinality mineEnumeration ∸ cardinality mineEnumeration ≡⟨ m+n∸n≡m (cardinality safeEnumeration) (cardinality mineEnumeration) ⟩
      cardinality safeEnumeration ∎
      where open ≡-Reasoning
