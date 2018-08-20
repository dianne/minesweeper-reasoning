module Minesweeper.Coords where

open import Data.Nat
open import Data.Integer using (∣_∣; _⊖_)
open import Data.Product
open import Data.Fin hiding (_≟_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import Minesweeper.Enumeration as Enum using (Enumeration)

Bounds : Set
Bounds = ℕ × ℕ

Coords : Bounds → Set
Coords (w , h) = Fin w × Fin h

Adjacent : ∀ {bounds} (coords₁ coords₂ : Coords bounds) → Set
Adjacent (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ x₂ ⊖ toℕ x₂ ∣ ≡ 1

adjacent? : ∀ {bounds} → Decidable (Adjacent {bounds})
adjacent? (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ x₂ ⊖ toℕ x₂ ∣ ≟ 1

Neighbor : ∀ {bounds} (coords : Coords bounds) → Set
Neighbor coords = Σ[ neighbor ∈ _ ] Adjacent coords neighbor

neighbors : ∀ {bounds} (coords : Coords bounds) → Enumeration (Neighbor coords)
neighbors {w , h} coords = Enum.filter ≡-irrelevance (adjacent? coords) (Enum.allFin w Enum.⊗ Enum.allFin h)
