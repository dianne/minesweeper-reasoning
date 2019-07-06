module Minesweeper.Coords where

open import Data.Nat renaming (_≟_ to _ℕ≟_)
open import Data.Integer using (∣_∣; _⊖_)
open import Data.Integer.Properties using (∣m⊖n∣≡∣n⊖m∣)
open import Data.Product
import      Data.Product.Properties as ×
open import Data.Product.Relation.Pointwise.NonDependent using (×-setoid; ≡×≡⇒≡)
open import Data.Fin renaming (_≟_ to _Fin≟_)
import      Data.Fin.Properties as Fin
open import Relation.Nullary
import      Relation.Nullary.Decidable as Dec
open import Relation.Unary  using ()       renaming (Decidable to Decidable₁)
open import Relation.Binary using (Setoid) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
import      Relation.Binary.Construct.On as On
open import Function

open import Minesweeper.Enumeration as Enum using (Enumeration)

-- Bounds are board boundaries/dimensions
Bounds : Set
Bounds = ℕ × ℕ

-- Coords are coordinates on a board of a given size, used as a way to point to a specific tile.
Coords : Bounds → Set
Coords (w , h) = Fin w × Fin h

Adjacent : ∀ {bounds} (coords₁ coords₂ : Coords bounds) → Set
Adjacent (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣ ≡ 1

adjacent? : ∀ {bounds} → Decidable₂ (Adjacent {bounds})
adjacent? (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣ ℕ≟ 1

-- a Neighbor to `coords` is an adjacent tile: another coordinate pair and a proof that it's adjacent to `coords`.
-- we don't compare the proofs for equality, so we define their setoid equality as equality on the coordinates
Neighbor : ∀ {bounds} (coords : Coords bounds) → Setoid _ _
Neighbor {w , h} coords = On.setoid {B = ∃ (Adjacent coords)} (×-setoid (Fin.setoid w) (Fin.setoid h)) proj₁

neighbors : ∀ {bounds} (coords : Coords bounds) → Enumeration (Neighbor coords)
neighbors {w , h} coords = Enum.filter (adjacent? coords) (subst (Adjacent coords) ∘ ≡×≡⇒≡) (Enum.allFin w Enum.⊗ Enum.allFin h)

neighborCount : ∀ {bounds} (coords : Coords bounds) → ℕ
neighborCount = Enumeration.cardinality ∘ neighbors


Adjacent-sym : ∀ {bounds} (coords₁ coords₂ : Coords bounds) → Adjacent coords₁ coords₂ → Adjacent coords₂ coords₁
Adjacent-sym (x₁ , y₁) (x₂ , y₂) coords₁-coords₂-Adj = begin
  (∣ toℕ x₂ ⊖ toℕ x₁ ∣ ⊔ ∣ toℕ y₂ ⊖ toℕ y₁ ∣)
    ≡⟨ cong₂ _⊔_ (∣m⊖n∣≡∣n⊖m∣ (toℕ x₂) (toℕ x₁)) (∣m⊖n∣≡∣n⊖m∣ (toℕ y₂) (toℕ y₁)) ⟩
  (∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣)
    ≡⟨ coords₁-coords₂-Adj ⟩
  1 ∎
  where open ≡-Reasoning



_≟_ : ∀ {bounds} → Decidable₂ (_≡_ {A = Coords bounds})
_≟_ = ×.≡-dec _Fin≟_ _Fin≟_


all? : ∀ {bounds p} {P : Coords bounds → Set p} → Decidable₁ P →
  Dec (∀ coords → P coords)
all? P? = Dec.map′ uncurry curry (Fin.all? (Fin.all? ∘ curry P?))

¬∀⟶∃¬ : ∀ bounds {p} (P : Coords bounds → Set p) → Decidable₁ P →
  ¬ (∀ coords → P coords) → (∃ λ coords → ¬ P coords)
¬∀⟶∃¬ bounds P P? ¬P with Fin.¬∀⟶∃¬ _ (λ x → ∀ y → P (x , y)) (Fin.all? ∘ curry P?) (¬P ∘ uncurry)
...                     | x , ¬Px with Fin.¬∀⟶∃¬ _ (λ y → P (x , y)) (curry P? x) ¬Px
...                                  | y , ¬Pxy = (x , y) , ¬Pxy
