module Minesweeper.Coords where

open import Data.Nat
open import Data.Integer using (∣_∣; _⊖_)
open import Data.Integer.Properties using (∣m⊖n∣≡∣n⊖m∣)
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
Adjacent (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣ ≡ 1

adjacent? : ∀ {bounds} → Decidable (Adjacent {bounds})
adjacent? (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣ ≟ 1

Neighbor : ∀ {bounds} (coords : Coords bounds) → Set
Neighbor coords = Σ[ neighbor ∈ _ ] Adjacent coords neighbor

neighbors : ∀ {bounds} (coords : Coords bounds) → Enumeration (Neighbor coords)
neighbors {w , h} coords = Enum.filter ≡-irrelevance (adjacent? coords) (Enum.allFin w Enum.⊗ Enum.allFin h)


Adjacent-sym : ∀ {bounds} (coords₁ coords₂ : Coords bounds) → Adjacent coords₁ coords₂ → Adjacent coords₂ coords₁
Adjacent-sym (x₁ , y₁) (x₂ , y₂) coords₁-coords₂-Adj = begin
  (∣ toℕ x₂ ⊖ toℕ x₁ ∣ ⊔ ∣ toℕ y₂ ⊖ toℕ y₁ ∣)
    ≡⟨ cong₂ _⊔_ (∣m⊖n∣≡∣n⊖m∣ (toℕ x₂) (toℕ x₁)) (∣m⊖n∣≡∣n⊖m∣ (toℕ y₂) (toℕ y₁)) ⟩
  (∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣)
    ≡⟨ coords₁-coords₂-Adj ⟩
  1 ∎
  where open ≡-Reasoning

neighbor-sym : ∀ {bounds} {coords : Coords bounds} (neighbor : Neighbor coords) → Neighbor (proj₁ neighbor)
neighbor-sym {coords = coords} (neighbor , adjacency) = coords , Adjacent-sym coords neighbor adjacency
