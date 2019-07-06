module Minesweeper.Board where

open import Data.Vec as Vec using (Vec)
import Data.Vec.Properties as VecProp
import Data.Vec.Relation.Binary.Pointwise.Inductive   as VecIndPointwise
import Data.Vec.Relation.Binary.Pointwise.Extensional as VecExtPointwise
open import Data.Fin using (_≟_)
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent using (≡×≡⇒≡)
open import Function
open import Relation.Nullary
open import Relation.Unary  using  (Decidable)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.On as On
open ≡-Reasoning

open import Minesweeper.Enumeration as Enum using (Enumeration)
open import Minesweeper.Coords hiding (_≟_)

-- Boards are 2D grids of tiles. they're parameterized over a type of tile, which we'll either instantiate with
-- `KnownTile` (when all tiles' identities are known) or `Tile` (when the board may have some unknown tiles).
-- for more about tiles, see Rules.agda and Moves.agda
Board : Set → Bounds → Set
Board A (w , h) = Vec (Vec A w) h

lookup : ∀ {A bounds} → Board A bounds → Coords bounds → A
lookup grid (x , y) = Vec.lookup (Vec.lookup grid y) x

_[_]≔_ : ∀ {A bounds} → Board A bounds → Coords bounds → A → Board A bounds
grid [ (x , y) ]≔ value = Vec.updateAt y (Vec._[ x ]≔ value) grid

-- `P Neighboring coords on grid` are the adjacent tiles to `coords` that satisfy the predicate `P`:
-- a `Neighbor coords` paired with a proof that its coordinates, when looked up on `grid`, satisfy `P`.
-- we don't compare the proofs for equality, so we define their setoid equality as equality on the Neighbors
_Neighboring_on_ : ∀ {p A bounds} → (A → Set p) → Coords bounds → Board A bounds → Setoid _ _
P Neighboring coords on grid = On.setoid
  {B = Σ[ neighbor ∈ Setoid.Carrier (Neighbor coords) ] P (lookup grid (proj₁ neighbor))}
  (Neighbor coords)
  proj₁

-- in order to get the neighbors of some coords satisfying P, we can filter all of its neighbors to just the ones satisfying P
filterNeighbors : ∀ {p A bounds} {P : A → Set p} (P? : Decidable P) (grid : Board A bounds) (coords : Coords bounds) → Enumeration (P Neighboring coords on grid)
filterNeighbors {P = P} P? grid coords = Enum.filter (P? ∘ lookup grid ∘ proj₁) (subst (P ∘ lookup grid) ∘ ≡×≡⇒≡) (neighbors coords)


Pointwise : ∀ {ℓ A B} (_∼_ : REL A B ℓ) {bounds} → REL (Board A bounds) (Board B bounds) _
Pointwise _∼_ grid₁ grid₂ = ∀ coords → lookup grid₁ coords ∼ lookup grid₂ coords

Pointwise⇒VecPointwise : ∀ {ℓ A B} {_∼_ : REL A B ℓ} {bounds} {grid₁ : Board A bounds} {grid₂ : Board B bounds} →
  Pointwise _∼_ grid₁ grid₂ →
    VecIndPointwise.Pointwise (VecIndPointwise.Pointwise _∼_) grid₁ grid₂
Pointwise⇒VecPointwise ₁∼₂ =
  VecExtPointwise.extensional⇒inductive (VecExtPointwise.ext λ y →
    VecExtPointwise.extensional⇒inductive (VecExtPointwise.ext λ x →
      ₁∼₂ (x , y) ) )


lookup∘update : ∀ {A bounds} (coords : Coords bounds) (grid : Board A bounds) value →
  lookup (grid [ coords ]≔ value) coords ≡ value
lookup∘update (x , y) grid value = begin
  lookup (grid [ x , y ]≔ value) (x , y)
    ≡⟨⟩
  Vec.lookup (Vec.lookup (Vec.updateAt y (Vec._[ x ]≔ value) grid) y) x
    ≡⟨ cong (flip Vec.lookup x) (VecProp.lookup∘updateAt y grid) ⟩
  Vec.lookup (Vec.lookup grid y Vec.[ x ]≔ value) x
    ≡⟨ VecProp.lookup∘update x (Vec.lookup grid y) value ⟩
  value ∎

lookup∘update′ : ∀ {A bounds} {coords₁ coords₂ : Coords bounds} → coords₁ ≢ coords₂ → ∀ (grid : Board A bounds) value →
  lookup (grid [ coords₂ ]≔ value) coords₁ ≡ lookup grid coords₁
lookup∘update′ {coords₁ = x₁ , y₁} {x₂ , y₂} coords₁≢coords₂ grid value with y₁ ≟ y₂
... | no y₁≢y₂ = cong (flip Vec.lookup x₁) (VecProp.lookup∘updateAt′ y₁ y₂ y₁≢y₂ grid)
... | yes refl = begin
  lookup (grid [ x₂ , y₁ ]≔ value) (x₁ , y₁)
    ≡⟨ cong (flip Vec.lookup x₁) (VecProp.lookup∘updateAt y₁ grid) ⟩
  Vec.lookup (Vec.lookup grid y₁ Vec.[ x₂ ]≔ value) x₁
    ≡⟨ VecProp.lookup∘update′ (coords₁≢coords₂ ∘ flip (curry ≡×≡⇒≡) refl) (Vec.lookup grid y₁) value ⟩
  Vec.lookup (Vec.lookup grid y₁) x₁ ∎
