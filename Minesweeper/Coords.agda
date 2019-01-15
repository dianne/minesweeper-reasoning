module Minesweeper.Coords where

open import Data.Nat renaming (_≟_ to _ℕ≟_)
open import Data.Integer using (∣_∣; _⊖_)
open import Data.Integer.Properties using (∣m⊖n∣≡∣n⊖m∣)
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent using (≡?×≡?⇒≡?)
open import Data.Fin renaming (_≟_ to _Fin≟_)
import      Data.Fin.Properties as Fin
open import Relation.Nullary
open import Relation.Unary  using () renaming (Decidable to Decidable₁)
open import Relation.Binary using () renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.WithK
open import Function

open import Minesweeper.Enumeration as Enum using (Enumeration)

Bounds : Set
Bounds = ℕ × ℕ

Coords : Bounds → Set
Coords (w , h) = Fin w × Fin h

Adjacent : ∀ {bounds} (coords₁ coords₂ : Coords bounds) → Set
Adjacent (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣ ≡ 1

adjacent? : ∀ {bounds} → Decidable₂ (Adjacent {bounds})
adjacent? (x₁ , y₁) (x₂ , y₂) = ∣ toℕ x₁ ⊖ toℕ x₂ ∣ ⊔ ∣ toℕ y₁ ⊖ toℕ y₂ ∣ ℕ≟ 1

Neighbor : ∀ {bounds} (coords : Coords bounds) → Set
Neighbor coords = Σ[ neighbor ∈ _ ] Adjacent coords neighbor

neighbors : ∀ {bounds} (coords : Coords bounds) → Enumeration (Neighbor coords)
neighbors {w , h} coords = Enum.filter ≡-irrelevant (adjacent? coords) (Enum.allFin w Enum.⊗ Enum.allFin h)


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


_≟_ : ∀ {bounds} → Decidable₂ (_≡_ {A = Coords bounds})
_≟_ = ≡?×≡?⇒≡? _Fin≟_ _Fin≟_


¬∀⟶∃¬ : ∀ bounds {p} (P : Coords bounds → Set p) → Decidable₁ P →
  ¬ (∀ coords → P coords) → (∃ λ coords → ¬ P coords)
¬∀⟶∃¬ bounds P P? ¬P with Fin.¬∀⟶∃¬ _ (λ x → ∀ y → P (x , y)) (Fin.all? ∘ curry P?) (¬P ∘ uncurry)
...                     | x , ¬Px with Fin.¬∀⟶∃¬ _ (λ y → P (x , y)) (curry P? x) ¬Px
...                                  | y , ¬Pxy = (x , y) , ¬Pxy
