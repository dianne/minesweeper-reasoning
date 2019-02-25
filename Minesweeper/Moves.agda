-- a hopefully-self-evident description of valid minesweeper moves
-- and several lemmas about it

module Minesweeper.Moves where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Vec as Vec using (Vec; []; _∷_; _++_)
import      Data.Vec.Properties as VecProp
open import Data.Vec.Relation.Unary.Any as Any using (Any; any)
import      Data.Vec.Relation.Unary.Any.Properties as AnyProp
open import Data.Vec.Relation.Binary.Pointwise.Inductive as VecPointwise using ([]; _∷_)
open import Data.Vec.Membership.Propositional using (_∈_)
import      Data.Vec.Membership.Propositional.Properties as ∈
open import Data.Nat hiding (_>_; _≥_)
import      Data.Nat.Properties as ℕProp
open import Data.Fin as Fin using (Fin; zero; suc)
open import Relation.Nullary
open import Relation.Unary  renaming (Decidable to Decidable₁) using ()
open import Relation.Binary renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.Reflexive as Refl renaming (Refl to ReflexiveClosure)
open import Induction
open import Induction.WellFounded as WF
open import Induction.Nat using (<-wellFounded)
open import Function

open import Minesweeper.Enumeration using (Enumeration)
open import Minesweeper.Coords as Coords
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
_↝⊞_ = Pointwise _↝▣_


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

unknown? : Decidable₁ (unknown ≡_)
unknown? (known s) = no λ ()
unknown? unknown   = yes refl

-- if a tile is already known, it can only be filled that way.
-- usually when we know a tile is known it's from a separate equality such as `known tile ≡ lookup coords grid`,
-- so this is specialized to account for that case
known-↝▣⇒≡ : ∀ {tile knowntile knowntile′} → tile ≡ known knowntile → tile ↝▣ knowntile′ → knowntile ≡ knowntile′
known-↝▣⇒≡ refl (↝▣known _) = refl

-- if a tile is specifically known to be safe with `n` adjacent mines on a consistent board `grid′`, we can go further:
-- `grid′ ✓` gives us an Enumeration of that tile's neighboring mines with exactly `n` members.
-- that is, on `grid′` it indeed does have `n` adjacent mines
known-safe-✓ : ∀ {bounds} (coords : Coords bounds) grid grid′ {n} → lookup coords grid ≡ known (safe n) → grid ↝⊞ grid′ → grid′ ✓ →
  Σ[ neighboringMines ∈ Enumeration ((mine⚐ ⚐✓_) Neighboring coords on grid′) ] n ≡ Enumeration.cardinality neighboringMines
known-safe-✓ coords grid grid′ coords↦safe grid↝⊞grid′ grid′✓ with grid′✓ coords
...                                                              | grid′[coords]✓ rewrite sym (known-↝▣⇒≡ coords↦safe (grid↝⊞grid′ coords)) = grid′[coords]✓


-- specificity: a partially filled board is more specific than another if it agrees on all known tiles
-- and has strictly more tiles known. this is helpful in writing inductive proofs as it is well-founded:
-- boards are finite, so by filling one in step-by-step, eventually you'll have filled the whole board
data _≻_ : Tile → Tile → Set where
  known≻unknown : ∀ {s} → known s ≻ unknown

_≽_ : Rel Tile _
_≽_ = ReflexiveClosure _≻_

_≥_ : ∀ {bounds} → Rel (Board Tile bounds) _
_≥_ = Pointwise _≽_

record _>_ {bounds} (filled : Board Tile bounds) (holey : Board Tile bounds) : Set where
  field
    >⇒≥ : filled ≥ holey
    >-strict : ∃[ coords ] (lookup coords filled ≻ lookup coords holey)

open _>_ public

>-Rec : ∀ {ℓ bounds} → RecStruct (Board Tile bounds) ℓ ℓ
>-Rec = WfRec _>_

-- more specific boards have fewer unknown tiles. then since _<_ on ℕ is well-founded, so is _>_ on Boards
countUnknowns : ∀ {bounds} → Board Tile bounds → ℕ
countUnknowns grid = Vec.count unknown? (Vec.concat grid)

countUnknowns-strict-monotone : ∀ {bounds} → _>_ {bounds} =[ countUnknowns ]⇒ _<_
countUnknowns-strict-monotone filled>holey = uncurry countUnknowns-strict-monotone′ (>-strict filled>holey) (Pointwise⇒VecPointwise (>⇒≥ filled>holey)) where
  count-++ : ∀ {m n} (xs : Vec Tile m) (ys : Vec Tile n) → Vec.count unknown? (xs Vec.++ ys) ≡ Vec.count unknown? xs + Vec.count unknown? ys
  count-++ [] ys = refl
  count-++ (known _ ∷ xs) ys = count-++ xs ys
  count-++ (unknown ∷ xs) ys = cong suc (count-++ xs ys)

  countUnknowns♭-monotone : ∀ {m} → VecPointwise.Pointwise _≽_ {m = m} =[ Vec.count unknown? ]⇒ _≤_
  countUnknowns♭-monotone [] = z≤n
  countUnknowns♭-monotone ([ known≻unknown ] ∷ ts≽us) = ℕProp.≤-step (countUnknowns♭-monotone ts≽us)
  countUnknowns♭-monotone (refl {known _}    ∷ ts≽us) = countUnknowns♭-monotone ts≽us
  countUnknowns♭-monotone (refl {unknown}    ∷ ts≽us) = s≤s (countUnknowns♭-monotone ts≽us)

  countUnknowns♭-strict-monotone : ∀ {n} {filled holey : Vec Tile n} ix → Vec.lookup ix filled ≻ Vec.lookup ix holey →
    VecPointwise.Pointwise _≽_ filled holey → Vec.count unknown? filled < Vec.count unknown? holey
  countUnknowns♭-strict-monotone zero    known≻unknown (_ ∷ ts≽us)                 = s≤s (countUnknowns♭-monotone ts≽us)
  countUnknowns♭-strict-monotone (suc i) ti≻ui         ([ known≻unknown ] ∷ ts≽us) = ℕProp.≤-step (countUnknowns♭-strict-monotone i ti≻ui ts≽us)
  countUnknowns♭-strict-monotone (suc i) ti≻ui         (refl {known _}    ∷ ts≽us) = countUnknowns♭-strict-monotone i ti≻ui ts≽us
  countUnknowns♭-strict-monotone (suc i) ti≻ui         (refl {unknown}    ∷ ts≽us) = s≤s (countUnknowns♭-strict-monotone i ti≻ui ts≽us)

  countUnknowns-strict-monotone′ : ∀ {bounds} {filled holey : Board Tile bounds} coords → lookup coords filled ≻ lookup coords holey →
    VecPointwise.Pointwise (VecPointwise.Pointwise _≽_) filled holey → countUnknowns filled < countUnknowns holey
  countUnknowns-strict-monotone′ {_} {ts ∷ tss} {us ∷ uss} (x , zero) ti≻ui (ts≽us ∷ tss≽uss) = begin-strict
    countUnknowns (ts ∷ tss)                                    ≡⟨ count-++ ts (Vec.concat tss) ⟩

    Vec.count unknown? ts + Vec.count unknown? (Vec.concat tss) <⟨ ℕProp.+-mono-<-≤ (countUnknowns♭-strict-monotone x ti≻ui ts≽us)
                                                                                    (countUnknowns♭-monotone (VecPointwise.concat⁺ tss≽uss)) ⟩
    Vec.count unknown? us + Vec.count unknown? (Vec.concat uss) ≡˘⟨ count-++ us (Vec.concat uss) ⟩

    countUnknowns (us ∷ uss) ∎
    where open ℕProp.≤-Reasoning
  countUnknowns-strict-monotone′ {_} {ts ∷ tss} {us ∷ uss} (x , suc y) ti≻ui (ts≽us ∷ tss≽uss) = begin-strict
    countUnknowns (ts ∷ tss)                                    ≡⟨ count-++ ts (Vec.concat tss) ⟩

    Vec.count unknown? ts + Vec.count unknown? (Vec.concat tss) <⟨ ℕProp.+-mono-≤-< (countUnknowns♭-monotone ts≽us)
                                                                                    (countUnknowns-strict-monotone′ (x , y) ti≻ui tss≽uss) ⟩
    Vec.count unknown? us + Vec.count unknown? (Vec.concat uss) ≡˘⟨ count-++ us (Vec.concat uss) ⟩

    countUnknowns (us ∷ uss) ∎
    where open ℕProp.≤-Reasoning
  
>-wellFounded : ∀ {bounds} → WellFounded (_>_ {bounds})
>-wellFounded = WF.Subrelation.wellFounded countUnknowns-strict-monotone (WF.Inverse-image.wellFounded countUnknowns <-wellFounded)

module _ {ℓ bounds} where
  open WF.All (>-wellFounded {bounds}) ℓ public
    renaming ( wfRecBuilder to >-recBuilder
             ; wfRec to >-rec )

-- in order to use this, a helper: filling in an unknown tile results in a more specific board
fill-> : ∀ {bounds} coords (grid : Board Tile bounds) tile → lookup coords grid ≡ unknown →
  (grid [ coords ]≔ known tile) > grid
fill-> coords grid tile coords↦unknown = record
  { >⇒≥ = fill-≥
  ; >-strict = coords , fill-≻ }
  where
    fill-≻ : lookup coords (grid [ coords ]≔ known tile) ≻ lookup coords grid
    fill-≻ rewrite lookup∘update coords grid (known tile) | coords↦unknown = known≻unknown

    fill-≥ : (grid [ coords ]≔ known tile) ≥ grid
    fill-≥ coords′ with coords Coords.≟ coords′
    ... | yes refl = [ fill-≻ ]
    ... | no coords≢coords′ rewrite lookup∘update′ (coords≢coords′ ∘ sym) grid (known tile) = refl

-- and also to help: a board either has an unknown tile or all of its tiles are known
holey⊎filled : ∀ {bounds} (grid : Board Tile bounds) →
  (∃ λ coords → lookup coords grid ≡ unknown) ⊎ (∀ coords → ∃ λ tile → lookup coords grid ≡ known tile)
holey⊎filled grid with any (any unknown?) grid
... | yes any-unknown = inj₁ ( (Any.index (AnyProp.lookup-index any-unknown) , Any.index any-unknown)
                             , sym (AnyProp.lookup-index (AnyProp.lookup-index any-unknown)) )
... | no ¬any-unknown = inj₂ allKnown where
  allKnown : ∀ coords → ∃ λ tile → lookup coords grid ≡ known tile
  allKnown coords with lookup coords grid | inspect (lookup coords) grid
  ... | known tile | _ = tile , refl
  ... | unknown    | [ coords↦unknown ] = ⊥-elim (¬any-unknown
    (∈.toAny (∈.∈-lookup (proj₂ coords) grid)
      (subst (_∈ Vec.lookup (proj₂ coords) grid) coords↦unknown
        (∈.∈-lookup (proj₁ coords) (Vec.lookup (proj₂ coords) grid)))))


-- _≥_ and _↝⊞_ obey a sort of transitivity: if you can fill in a board, then any more general board
-- can be filled the same way
≽-↝▣-trans : ∀ {filled holey} → filled ≽ holey → ∀ {definitelyFilled} → filled ↝▣ definitelyFilled → holey ↝▣ definitelyFilled
≽-↝▣-trans [ known≻unknown ] (↝▣known tile)   = ↝▣unknown tile
≽-↝▣-trans refl              (↝▣known tile)   = ↝▣known tile
≽-↝▣-trans refl              (↝▣unknown tile) = ↝▣unknown tile

≥-↝⊞-trans : ∀ {bounds} {filled holey : Board Tile bounds} → filled ≥ holey → ∀ {fullyFilled} → filled ↝⊞ fullyFilled → holey ↝⊞ fullyFilled
≥-↝⊞-trans filled≥holey filled↝⊞fullyFilled coords = ≽-↝▣-trans (filled≥holey coords) (filled↝⊞fullyFilled coords)


-- if we know all the tiles of a board, we can get a board of KnownTiles from it in order to
-- check it against the rules for filled boards in Minesweeper.Rules
unwrap : ∀ {bounds} {grid : Board Tile bounds} → (∀ coords → ∃ λ tile → lookup coords grid ≡ known tile) → Board KnownTile bounds
unwrap grid-filled = Vec.tabulate (λ y → Vec.tabulate (λ x → proj₁ (grid-filled (x , y))))

lookup∘unwrap : ∀ {bounds} {grid} grid-filled coords → lookup coords (unwrap {bounds} {grid} grid-filled) ≡ proj₁ (grid-filled coords)
lookup∘unwrap {grid = grid} grid-filled coords = begin
  lookup coords (unwrap grid-filled)
    ≡⟨ cong (Vec.lookup (proj₁ coords)) (VecProp.lookup∘tabulate (λ y → Vec.tabulate (λ x → proj₁ (grid-filled (x , y)))) (proj₂ coords)) ⟩
  Vec.lookup (proj₁ coords) (Vec.tabulate (λ x → proj₁ (grid-filled (x , proj₂ coords))))
    ≡⟨ VecProp.lookup∘tabulate (λ x → proj₁ (grid-filled (x , proj₂ coords))) (proj₁ coords) ⟩
  proj₁ (grid-filled coords) ∎
  where open ≡-Reasoning

↝⊞-unwrap : ∀ {bounds} {grid} grid-filled →
  grid ↝⊞ unwrap {bounds} {grid} grid-filled
↝⊞-unwrap grid-filled coords
  rewrite proj₂ (grid-filled coords)
        | lookup∘unwrap grid-filled coords = ↝▣known (proj₁ (grid-filled coords))
