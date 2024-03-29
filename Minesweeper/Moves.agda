-- this module is dedicated to definitions and lemmas regarding partially known boards. importantly, we want to reason about when
-- an unknown tile will, when revealed, always be a mine or a safe tile. I refer to assigning guesses like that as "moves" and
-- call them "valid" when they will always hold, in reference to the actions of marking tiles as mines or revealing safe tiles
-- when playing minesweeper.

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

-- Tile represents the tiles of a board that may have a mix of known and unknown tiles, like those in a game of minesweeper
data Tile : Set where
  known   : KnownTile → Tile
  unknown : Tile

-- tile filling: to relate filled and partial boards, we can fill in the tiles of a partial board to make a full board.
-- known tiles can only be "filled" with themselves, whereas unknown tiles can be filled with anything.
data _↝▣_ : Tile → KnownTile → Set where
  ↝▣known   : ∀ s → known s ↝▣ s
  ↝▣unknown : ∀ s → unknown ↝▣ s

-- board filling: can a fully filled board be reached by filling in the unknown tiles of a partial board?
_↝⊞_ : ∀ {bounds} → Board Tile bounds → Board KnownTile bounds → Set
_↝⊞_ = Pointwise _↝▣_


-- move validity: a guess as to a tile's identity on a board is valid when it holds in every rule-respecting way to fill the board's unfilled tiles.
-- here, "rule-respecting" means that we're only considering the filled boards where the numbers on the safe tiles match with the number of mines
-- adjacent to them. see Rules.agda for more details
-- in a game of minesweeper, a guess that a tile is safe or a mine being valid means that it definitely will be that. an invalid guess can still by
-- chance be right in a specific game you're playing, but there is some way of assigning the unknown tiles where you will be wrong.
_[_]↝✓_ : ∀ {bounds} → Board Tile bounds → Coords bounds → Guess → Set
grid [ coords ]↝✓ guess = ∀ grid′ →
  grid ↝⊞ grid′ →
  grid′ ✓ →
    guess ⚐✓ lookup grid′ coords



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
known-safe-✓ : ∀ {bounds} (coords : Coords bounds) grid grid′ {n} → lookup grid coords ≡ known (safe n) → grid ↝⊞ grid′ → grid′ ✓ →
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
    >-strict : ∃[ coords ] (lookup filled coords ≻ lookup holey coords)

open _>_ public

>-Rec : ∀ {ℓ bounds} → RecStruct (Board Tile bounds) ℓ ℓ
>-Rec = WfRec _>_

-- more specific boards have fewer unknown tiles. then since _<_ on ℕ is well-founded, so is _>_ on Boards
countUnknowns : ∀ {bounds} → Board Tile bounds → ℕ
countUnknowns grid = Vec.count unknown? (Vec.concat grid)

countUnknowns-strict-monotone : ∀ {bounds} → _>_ {bounds} =[ countUnknowns ]⇒ _<_
countUnknowns-strict-monotone {_} {filled} {holey} filled>holey = uncurry (countUnknowns-strict-monotone′ filled holey) (>-strict filled>holey) (Pointwise⇒VecPointwise (>⇒≥ filled>holey)) where
  count-++ : ∀ {m n} (xs : Vec Tile m) (ys : Vec Tile n) → Vec.count unknown? (xs Vec.++ ys) ≡ Vec.count unknown? xs + Vec.count unknown? ys
  count-++ [] ys = refl
  count-++ (known _ ∷ xs) ys = count-++ xs ys
  count-++ (unknown ∷ xs) ys = cong suc (count-++ xs ys)

  countUnknowns♭-monotone : ∀ {m} → VecPointwise.Pointwise _≽_ {m = m} =[ Vec.count unknown? ]⇒ _≤_
  countUnknowns♭-monotone [] = z≤n
  countUnknowns♭-monotone ([ known≻unknown ] ∷ ts≽us) = ℕProp.≤-step (countUnknowns♭-monotone ts≽us)
  countUnknowns♭-monotone (refl {known _}    ∷ ts≽us) = countUnknowns♭-monotone ts≽us
  countUnknowns♭-monotone (refl {unknown}    ∷ ts≽us) = s≤s (countUnknowns♭-monotone ts≽us)

  countUnknowns♭-strict-monotone : ∀ {n} {filled holey : Vec Tile n} ix → Vec.lookup filled ix ≻ Vec.lookup holey ix →
    VecPointwise.Pointwise _≽_ filled holey → Vec.count unknown? filled < Vec.count unknown? holey
  countUnknowns♭-strict-monotone zero    known≻unknown (_ ∷ ts≽us)                 = s≤s (countUnknowns♭-monotone ts≽us)
  countUnknowns♭-strict-monotone (suc i) ti≻ui         ([ known≻unknown ] ∷ ts≽us) = ℕProp.≤-step (countUnknowns♭-strict-monotone i ti≻ui ts≽us)
  countUnknowns♭-strict-monotone (suc i) ti≻ui         (refl {known _}    ∷ ts≽us) = countUnknowns♭-strict-monotone i ti≻ui ts≽us
  countUnknowns♭-strict-monotone (suc i) ti≻ui         (refl {unknown}    ∷ ts≽us) = s≤s (countUnknowns♭-strict-monotone i ti≻ui ts≽us)

  countUnknowns-strict-monotone′ : ∀ {bounds} (filled holey : Board Tile bounds) coords → lookup filled coords ≻ lookup holey coords →
    VecPointwise.Pointwise (VecPointwise.Pointwise _≽_) filled holey → countUnknowns filled < countUnknowns holey
  countUnknowns-strict-monotone′ (ts ∷ tss) (us ∷ uss) (x , zero) ti≻ui (ts≽us ∷ tss≽uss) = begin-strict
    countUnknowns (ts ∷ tss)                                    ≡⟨ count-++ ts (Vec.concat tss) ⟩

    Vec.count unknown? ts + Vec.count unknown? (Vec.concat tss) <⟨ ℕProp.+-mono-<-≤ (countUnknowns♭-strict-monotone x ti≻ui ts≽us)
                                                                                    (countUnknowns♭-monotone (VecPointwise.concat⁺ tss≽uss)) ⟩
    Vec.count unknown? us + Vec.count unknown? (Vec.concat uss) ≡˘⟨ count-++ us (Vec.concat uss) ⟩

    countUnknowns (us ∷ uss) ∎
    where open ℕProp.≤-Reasoning
  countUnknowns-strict-monotone′ (ts ∷ tss) (us ∷ uss) (x , suc y) ti≻ui (ts≽us ∷ tss≽uss) = begin-strict
    countUnknowns (ts ∷ tss)                                    ≡⟨ count-++ ts (Vec.concat tss) ⟩

    Vec.count unknown? ts + Vec.count unknown? (Vec.concat tss) <⟨ ℕProp.+-mono-≤-< (countUnknowns♭-monotone ts≽us)
                                                                                    (countUnknowns-strict-monotone′ tss uss (x , y) ti≻ui tss≽uss) ⟩
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
fill-> : ∀ {bounds} coords (grid : Board Tile bounds) tile → lookup grid coords ≡ unknown →
  (grid [ coords ]≔ known tile) > grid
fill-> coords grid tile coords↦unknown = record
  { >⇒≥ = fill-≥
  ; >-strict = coords , fill-≻ }
  where
    fill-≻ : lookup (grid [ coords ]≔ known tile) coords ≻ lookup grid coords
    fill-≻ rewrite lookup∘update coords grid (known tile) | coords↦unknown = known≻unknown

    fill-≥ : (grid [ coords ]≔ known tile) ≥ grid
    fill-≥ coords′ with coords Coords.≟ coords′
    ... | yes refl = [ fill-≻ ]
    ... | no coords≢coords′ rewrite lookup∘update′ (coords≢coords′ ∘ sym) grid (known tile) = refl

-- and also to help: a board either has an unknown tile or all of its tiles are known
holey⊎filled : ∀ {bounds} (grid : Board Tile bounds) →
  (∃ λ coords → lookup grid coords ≡ unknown) ⊎ (∀ coords → ∃ λ tile → lookup grid coords ≡ known tile)
holey⊎filled grid with any (any unknown?) grid
... | yes any-unknown = inj₁ ( (Any.index (AnyProp.lookup-index any-unknown) , Any.index any-unknown)
                             , sym (AnyProp.lookup-index (AnyProp.lookup-index any-unknown)) )
... | no ¬any-unknown = inj₂ allKnown where
  allKnown : ∀ coords → ∃ λ tile → lookup grid coords ≡ known tile
  allKnown coords with lookup grid coords | inspect (lookup grid) coords
  ... | known tile | _ = tile , refl
  ... | unknown    | [ coords↦unknown ] = ⊥-elim (¬any-unknown
    (∈.toAny (∈.∈-lookup (proj₂ coords) grid)
      (subst (_∈ Vec.lookup grid (proj₂ coords)) coords↦unknown
        (∈.∈-lookup (proj₁ coords) (Vec.lookup grid (proj₂ coords))))))


-- _≥_ and _↝⊞_ obey a sort of transitivity: if you can fill in a board, then any more general board
-- can be filled the same way
≽-↝▣-trans : ∀ {filled holey} → filled ≽ holey → ∀ {definitelyFilled} → filled ↝▣ definitelyFilled → holey ↝▣ definitelyFilled
≽-↝▣-trans [ known≻unknown ] (↝▣known tile)   = ↝▣unknown tile
≽-↝▣-trans refl              (↝▣known tile)   = ↝▣known tile
≽-↝▣-trans refl              (↝▣unknown tile) = ↝▣unknown tile

≥-↝⊞-trans : ∀ {bounds} (filled holey : Board Tile bounds) → filled ≥ holey → ∀ fullyFilled → filled ↝⊞ fullyFilled → holey ↝⊞ fullyFilled
≥-↝⊞-trans filled holey filled≥holey fullyFilled filled↝⊞fullyFilled coords = ≽-↝▣-trans (filled≥holey coords) (filled↝⊞fullyFilled coords)


-- if we know all the tiles of a board, we can get a board of KnownTiles from it in order to
-- check it against the rules for filled boards in Minesweeper.Rules
unwrap : ∀ {bounds} (grid : Board Tile bounds) → (∀ coords → ∃ λ tile → lookup grid coords ≡ known tile) → Board KnownTile bounds
unwrap grid grid-filled = Vec.tabulate (λ y → Vec.tabulate (λ x → proj₁ (grid-filled (x , y))))

lookup∘unwrap : ∀ {bounds} grid grid-filled coords → lookup (unwrap {bounds} grid grid-filled) coords ≡ proj₁ (grid-filled coords)
lookup∘unwrap grid grid-filled coords = begin
  lookup (unwrap grid grid-filled) coords
    ≡⟨ cong (flip Vec.lookup (proj₁ coords)) (VecProp.lookup∘tabulate (λ y → Vec.tabulate (λ x → proj₁ (grid-filled (x , y)))) (proj₂ coords)) ⟩
  Vec.lookup (Vec.tabulate (λ x → proj₁ (grid-filled (x , proj₂ coords)))) (proj₁ coords)
    ≡⟨ VecProp.lookup∘tabulate (λ x → proj₁ (grid-filled (x , proj₂ coords))) (proj₁ coords) ⟩
  proj₁ (grid-filled coords) ∎
  where open ≡-Reasoning

↝⊞-unwrap : ∀ {bounds} grid grid-filled →
  grid ↝⊞ unwrap {bounds} grid grid-filled
↝⊞-unwrap grid grid-filled coords
  rewrite proj₂ (grid-filled coords)
        | lookup∘unwrap grid grid-filled coords = ↝▣known (proj₁ (grid-filled coords))
