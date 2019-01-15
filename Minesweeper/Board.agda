module Minesweeper.Board where

open import Data.Vec as Vec using (Vec)
import Data.Vec.Properties as VecProp
import Data.Vec.Relation.Pointwise.Inductive   as VecIndPointwise
import Data.Vec.Relation.Pointwise.Extensional as VecExtPointwise
open import Data.Fin using (_≟_)
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent using (≡×≡⇒≡)
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Minesweeper.Coords hiding (_≟_)

Board : Set → Bounds → Set
Board A (w , h) = Vec (Vec A w) h

lookup : ∀ {A bounds} → Coords bounds → Board A bounds → A
lookup (x , y) grid = Vec.lookup x (Vec.lookup y grid)

_[_]≔_ : ∀ {A bounds} → Board A bounds → Coords bounds → A → Board A bounds
grid [ (x , y) ]≔ value = Vec.updateAt y (Vec._[ x ]≔ value) grid

_Neighboring_on_ : ∀ {A bounds} → (A → Set) → Coords bounds → Board A bounds → Set
P Neighboring coords on grid = Σ[ neighbor ∈ Neighbor coords ] P (lookup (proj₁ neighbor) grid)


Pointwise : ∀ {ℓ A B} (_∼_ : REL A B ℓ) {bounds} → REL (Board A bounds) (Board B bounds) _
Pointwise _∼_ grid₁ grid₂ = ∀ coords → lookup coords grid₁ ∼ lookup coords grid₂

Pointwise⇒VecPointwise : ∀ {ℓ A B} {_∼_ : REL A B ℓ} {bounds} {grid₁ : Board A bounds} {grid₂ : Board B bounds} →
  Pointwise _∼_ grid₁ grid₂ →
    VecIndPointwise.Pointwise (VecIndPointwise.Pointwise _∼_) grid₁ grid₂
Pointwise⇒VecPointwise ₁∼₂ =
  VecExtPointwise.extensional⇒inductive (VecExtPointwise.ext λ y →
    VecExtPointwise.extensional⇒inductive (VecExtPointwise.ext λ x →
      ₁∼₂ (x , y) ) )


lookup∘update : ∀ {A bounds} (coords : Coords bounds) (grid : Board A bounds) value →
  lookup coords (grid [ coords ]≔ value) ≡ value
lookup∘update (x , y) grid value = begin
  lookup (x , y) (grid [ x , y ]≔ value)
    ≡⟨⟩
  Vec.lookup x (Vec.lookup y (Vec.updateAt y (Vec._[ x ]≔ value) grid))
    ≡⟨ cong (Vec.lookup x) (VecProp.lookup∘updateAt y grid) ⟩
  Vec.lookup x (Vec.lookup y grid Vec.[ x ]≔ value)
    ≡⟨ VecProp.lookup∘update x (Vec.lookup y grid) value ⟩
  value ∎

lookup∘update′ : ∀ {A bounds} {coords₁ coords₂ : Coords bounds} → coords₁ ≢ coords₂ → ∀ (grid : Board A bounds) value →
  lookup coords₁ (grid [ coords₂ ]≔ value) ≡ lookup coords₁ grid
lookup∘update′ {coords₁ = x₁ , y₁} {x₂ , y₂} coords₁≢coords₂ grid value with y₁ ≟ y₂
... | no y₁≢y₂ = cong (Vec.lookup x₁) (VecProp.lookup∘updateAt′ y₁ y₂ y₁≢y₂ grid)
... | yes refl = begin
  lookup (x₁ , y₁) (grid [ x₂ , y₁ ]≔ value)
    ≡⟨ cong (Vec.lookup x₁) (VecProp.lookup∘updateAt y₁ grid) ⟩
  Vec.lookup x₁ (Vec.lookup y₁ grid Vec.[ x₂ ]≔ value)
    ≡⟨ VecProp.lookup∘update′ (coords₁≢coords₂ ∘ flip (curry ≡×≡⇒≡) refl) (Vec.lookup y₁ grid) value ⟩
  Vec.lookup x₁ (Vec.lookup y₁ grid) ∎
