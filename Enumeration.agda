module Enumeration where

open import Data.List as List using (List; []; _∷_)
import Data.List.Categorical as List
open import Data.List.Any
import Data.List.Any.Properties as AnyProp
open import Data.List.Membership.Propositional
import Data.List.Membership.Propositional.Properties as ∈Prop
open import Data.List.Relation.BagAndSetEquality
open import Data.Fin
import Data.Fin.Properties as FinProp
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕProp
open import Data.Maybe using (Maybe; just; nothing)
open import Function
open import Function.Inverse as Inverse using (Inverse; _↔_)
open import Function.Injection as Injection using (Injection; _↣_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary using (Decidable)
open import Data.Product
open import Data.Sum as Sum
open import Category.Monad
import Level

record Enumeration A : Set where
  field
    list : List A
    complete : ∀ a → a ∈ list
    entries-unique : ∀ {a} (ix₁ ix₂ : a ∈ list) → ix₁ ≡ ix₂

open Enumeration


private
  there-injective : ∀ {A : Set} {P : A → Set} {x xs} {p₁ p₂ : Any P xs} → there {x = x} p₁ ≡ there p₂ → p₁ ≡ p₂
  there-injective refl = refl

  remove : ∀ {A : Set} {ys} {y : A} → y ∈ ys → List A
  remove {ys = _ ∷ ys} (here _) = ys
  remove {ys = y ∷ ys} (there y∈ys) = y ∷ remove y∈ys

  remove-subbag′ : ∀ {A : Set} (x : A) xs ys ys′ (x∈ys : x ∈ ys) (inclusion : ∀ {a} → (a ∈ x ∷ xs) ↣ (a ∈ ys ⊎ a ∈ ys′)) →
    inj₁ x∈ys ≡ Injection.to inclusion ⟨$⟩ here refl →
      ∀ {a} → (a ∈ xs) ↣ (a ∈ remove x∈ys ⊎ a ∈ ys′)
  remove-subbag′ x xs (.x ∷ ys) ys′ (here refl) inclusion x∈ys-≡ {a} = record
    { to = →-to-⟶ inclusion′
    ; injective = inclusion′-injective }
    where
      inclusion′-helper : ∀ {a∈xs : a ∈ xs} (a∈yss : a ∈ x ∷ ys ⊎ a ∈ ys′) → (Injection.to inclusion ⟨$⟩ there a∈xs ≡ a∈yss) → a ∈ ys ⊎ a ∈ ys′
      inclusion′-helper (inj₁ (here refl)) a↦x with Injection.injective inclusion (trans a↦x x∈ys-≡)
      ...                                         | ()
      inclusion′-helper (inj₁ (there a∈ys)) _ = inj₁ a∈ys
      inclusion′-helper (inj₂ a∈ys′)        _ = inj₂ a∈ys′

      inclusion′ : a ∈ xs → a ∈ ys ⊎ a ∈ ys′
      inclusion′ a∈xs = inclusion′-helper (Injection.to inclusion ⟨$⟩ there a∈xs) refl where

      inclusion′-helper-spec : ∀ {a∈xs : a ∈ xs} a∈yss a↦x →
        Sum.map there id (inclusion′-helper {a∈xs} a∈yss a↦x) ≡ Injection.to inclusion ⟨$⟩ there a∈xs
      inclusion′-helper-spec (inj₁ (here refl)) a↦x with Injection.injective inclusion (trans a↦x x∈ys-≡)
      ... | ()
      inclusion′-helper-spec (inj₁ (there a∈ys)) a↦x rewrite a↦x = refl
      inclusion′-helper-spec (inj₂ a∈ys′)        a↦x rewrite a↦x = refl

      inclusion′-spec : ∀ {a∈xs : a ∈ xs} → Sum.map there id (inclusion′ a∈xs) ≡ Injection.to inclusion ⟨$⟩ there a∈xs
      inclusion′-spec = inclusion′-helper-spec _ refl

      inclusion′-injective : ∀ {a∈xs₁ a∈xs₂ : a ∈ xs} → inclusion′ a∈xs₁ ≡ inclusion′ a∈xs₂ → a∈xs₁ ≡ a∈xs₂
      inclusion′-injective {a∈xs₁} {a∈xs₂} inclusion′-≡ = there-injective (Injection.injective inclusion
        (begin
          Injection.to inclusion ⟨$⟩ there a∈xs₁
            ≡⟨ sym inclusion′-spec ⟩
          Sum.map there id (inclusion′ a∈xs₁)
            ≡⟨ cong (Sum.map there id) inclusion′-≡ ⟩
          Sum.map there id (inclusion′ a∈xs₂)
            ≡⟨ inclusion′-spec ⟩
          Injection.to inclusion ⟨$⟩ there a∈xs₂ ∎)) where open ≡-Reasoning
  remove-subbag′ x xs (y ∷ ys) ys′ (there x∈ys) inclusion x∈ys-≡ =
    shiftHead₂ ⟪∘⟫ remove-subbag′ x xs ys (y ∷ ys′) x∈ys (shiftHead₁ ⟪∘⟫ inclusion) x∈ys-≡′ where
      shiftHead₂ : ∀ {a} → (a ∈ remove x∈ys ⊎ a ∈ y ∷ ys′) ↣ (a ∈ y ∷ remove x∈ys ⊎ a ∈ ys′)
      shiftHead₂ = record
        { to = →-to-⟶ [ (inj₁ ∘ there) , (λ { (here a≡y) → inj₁ (here a≡y) ; (there a∈ys′) → inj₂ a∈ys′ }) ]′
        ; injective = λ
          { {inj₁ _} {inj₁ _} refl → refl
          ; {inj₁ _} {inj₂ (here _)} () ; {inj₁ _} {inj₂ (there _)} () ; {inj₂ (here _)} {inj₁ _} () ; {inj₂ (there _)} {inj₁ _} ()
          ; {inj₂ (here _)} {inj₂ (here _)} refl → refl ; {inj₂ (there _)} {inj₂ (there _)} refl → refl
          ; {inj₂ (here _)} {inj₂ (there _)} () ; {inj₂ (there _)} {inj₂ (here _)} () } }
      shiftHead₁ : ∀ {a} → (a ∈ y ∷ ys ⊎ a ∈ ys′) ↣ (a ∈ ys ⊎ a ∈ y ∷ ys′)
      shiftHead₁ = record
        { to = →-to-⟶ [ (λ { (here a≡y) → inj₂ (here a≡y) ; (there a∈ys′) → inj₁ a∈ys′ }) , (inj₂ ∘ there) ]′
        ; injective = λ
          { {inj₁ (here _)} {inj₁ (here _)} refl → refl ; {inj₁ (there _)} {inj₁ (there _)} refl → refl
          ; {inj₁ (here _)} {inj₁ (there _)} () ; {inj₁ (there _)} {inj₁ (here _)} ()
          ; {inj₁ (here _)} {inj₂ _} () ; {inj₁ (there _)} {inj₂ _} () ; {inj₂ _} {inj₁ (here _)} () ; {inj₂ _} {inj₁ (there _)} ()
          ; {inj₂ _} {inj₂ _} refl → refl } }
      x∈ys-≡′ : inj₁ x∈ys ≡ Injection.to (shiftHead₁ ⟪∘⟫ inclusion) ⟨$⟩ here refl
      x∈ys-≡′ = begin
        inj₁ x∈ys
          ≡⟨⟩
        Injection.to shiftHead₁ ⟨$⟩ inj₁ (there x∈ys)
          ≡⟨ cong (_⟨$⟩_ (Injection.to shiftHead₁)) x∈ys-≡ ⟩
        Injection.to shiftHead₁ ⟨$⟩ (Injection.to inclusion ⟨$⟩ here refl)
          ≡⟨⟩
        Injection.to (shiftHead₁ ⟪∘⟫ inclusion) ⟨$⟩ here refl ∎ where open ≡-Reasoning

  remove-subbag : ∀ {A : Set} (x : A) xs ys → (inclusion : (x ∷ xs) ∼[ subbag ] ys) → xs ∼[ subbag ] remove (Injection.to inclusion ⟨$⟩ here refl)
  remove-subbag x xs ys inclusion = remove-⊎ ⟪∘⟫ remove-subbag′ x xs ys [] (Injection.to inclusion ⟨$⟩ here refl) (inj₁-Injection ⟪∘⟫ inclusion) refl where
    inj₁-Injection : ∀ {a} → (a ∈ ys) ↣ (a ∈ ys ⊎ a ∈ [])
    inj₁-Injection = record
      { to = →-to-⟶ inj₁
      ; injective = λ { refl → refl } }
    remove-⊎ : ∀ {a ys′} → (a ∈ ys′ ⊎ a ∈ []) ↣ (a ∈ ys′)
    remove-⊎ = record
      { to = →-to-⟶ λ { (inj₁ a∈ys′) → a∈ys′ ; (inj₂ ()) }
      ; injective = λ
        { {inj₁ _} {inj₁ _} refl → refl
        ; {inj₁ _} {inj₂ ()} _ ; {inj₂ ()} {inj₁ _} _ ; {inj₂ ()} {inj₂ ()} _ } }

  remove-length : ∀ {A : Set} {x : A} {xs} (x∈xs : x ∈ xs) → List.length xs ≡ suc (List.length (remove x∈xs))
  remove-length (here _) = refl
  remove-length (there x∈xs) = cong suc (remove-length x∈xs)

  subbag-length-≤ : ∀ {A : Set} {xs ys : List A} → xs ∼[ subbag ] ys → List.length xs ℕ.≤ List.length ys
  subbag-length-≤ {xs = []} {ys} xs⊑ys = z≤n
  subbag-length-≤ {xs = x ∷ xs} {ys} xs⊑ys = begin
    List.length (x ∷ xs)
      ≈⟨⟩
    suc (List.length xs)
      ≤⟨ s≤s (subbag-length-≤ (remove-subbag x xs ys xs⊑ys)) ⟩
    suc (List.length (remove (Injection.to xs⊑ys ⟨$⟩ here refl)))
      ≡⟨ sym (remove-length (Injection.to xs⊑ys ⟨$⟩ here refl)) ⟩
    List.length ys ∎ where open ℕProp.≤-Reasoning

-- enumerations of the same set are permutations of each other
enumeration-bag-equals : ∀ {A} (enum₁ enum₂ : Enumeration A) → list enum₁ ∼[ bag ] list enum₂
enumeration-bag-equals enum₁ enum₂ = record
  { to   = →-to-⟶ (λ _ → complete enum₂ _)
  ; from = →-to-⟶ (λ _ → complete enum₁ _)
  ; inverse-of = record
    { left-inverse-of  = λ _ → entries-unique enum₁ _ _
    ; right-inverse-of = λ _ → entries-unique enum₂ _ _ } }

-- as a consequence, they are equal in length
enumeration-length-uniform : ∀ {A} (enum₁ enum₂ : Enumeration A) → List.length (list enum₁) ≡ List.length (list enum₂)
enumeration-length-uniform enum₁ enum₂ = ℕProp.≤-antisym
  (subbag-length-≤ (bag-=⇒ (enumeration-bag-equals enum₁ enum₂)))
  (subbag-length-≤ (bag-=⇒ (enumeration-bag-equals enum₂ enum₁)))


private
  fsuc-Injection : ∀ {n} → Fin n ↣ Fin (suc n)
  fsuc-Injection = record
    { to = →-to-⟶ suc
    ; injective = FinProp.suc-injective }

  tabulate⁻-injective : ∀ {A : Set} {n} (f : Fin n ↣ A) → ∀ {x} (ix₁ ix₂ : x ∈ List.tabulate (λ y → Injection.to f ⟨$⟩ y)) → ix₁ ≡ ix₂
  tabulate⁻-injective {n = zero} f () ()
  tabulate⁻-injective {n = suc n} f (here refl) (here refl) = refl
  tabulate⁻-injective {n = suc n} f (here x≡fz) (there ix₂) with AnyProp.tabulate⁻ ix₂
  ... | _ , x≡fs with Injection.injective f (trans (sym x≡fz) (x≡fs))
  ...            | ()
  tabulate⁻-injective {n = suc n} f (there ix₁) (here x≡fz) with AnyProp.tabulate⁻ ix₁
  ... | _ , x≡fs with Injection.injective f (trans (sym x≡fz) (x≡fs))
  ...            | ()
  tabulate⁻-injective {n = suc n} f (there ix₁) (there ix₂) = cong there (tabulate⁻-injective (f Injection.∘ fsuc-Injection) ix₁ ix₂)

allFin : ∀ n → Enumeration (Fin n)
allFin n = record
  { list = List.allFin n
  ; complete = λ i → AnyProp.tabulate⁺ i refl
  ; entries-unique = tabulate⁻-injective Injection.id }


private
  module Product {A B} (enum₁ : Enumeration A) (enum₂ : Enumeration B) where
    open RawMonad (List.monad {Level.zero})

    product-list : List (A × B)
    product-list = list enum₁ ⊗ list enum₂

    product-complete : ∀ xy → xy ∈ product-list
    product-complete (x , y) = Inverse.to ∈Prop.⊗-∈↔ ⟨$⟩ (complete enum₁ x , complete enum₂ y)

    abstract
      -- hide the internals of ⊗-∈↔ away from the typechecker so it doesn't diverge (?? agda bug ??)
      ⊗-∈↔-abstract : ∀ {x y} → (x ∈ list enum₁ × y ∈ list enum₂) ↔ (x , y) ∈ product-list
      ⊗-∈↔-abstract = ∈Prop.⊗-∈↔

    split-∈ : ∀ {x y} → (x , y) ∈ product-list → x ∈ list enum₁ × y ∈ list enum₂
    split-∈ xy-ix = Inverse.from ⊗-∈↔-abstract ⟨$⟩ xy-ix

    pairs-unique : ∀ {x y} (ixs₁ ixs₂ : x ∈ list enum₁ × y ∈ list enum₂) → ixs₁ ≡ ixs₂
    pairs-unique (x-ix₁ , y-ix₁) (x-ix₂ , y-ix₂) with entries-unique enum₁ x-ix₁ x-ix₂ | entries-unique enum₂ y-ix₁ y-ix₂
    ... | refl | refl = refl

    product-unique : ∀ {xy} (xy-ix₁ xy-ix₂ : xy ∈ product-list) → xy-ix₁ ≡ xy-ix₂
    product-unique xy-ix₁ xy-ix₂ = Inverse.injective (Inverse.sym ⊗-∈↔-abstract) (pairs-unique (split-∈ xy-ix₁) (split-∈ xy-ix₂))

_⊗_ : ∀ {A B} → Enumeration A → Enumeration B → Enumeration (A × B)
enum₁ ⊗ enum₂ = record
  { list = product-list
  ; complete = product-complete
  ; entries-unique = product-unique }
  where open Product enum₁ enum₂


private
  module Filter {A : Set} {P : A → Set} (P-irrelevant : IrrelevantPred P) (P? : Decidable P) where
    discardNo : ∀ {a} → Dec (P a) → Maybe (Σ A P)
    discardNo {a = a} (yes p) = just (a , p)
    discardNo (no ¬p) = nothing

    Σfilter : List A → List (Σ A P)
    Σfilter = List.mapMaybe (discardNo ∘ P?)

    Σfilter-∈ : ∀ {xs x} → x ∈ xs → (Px : P x) → (x , Px) ∈ Σfilter xs
    Σfilter-∈ {x ∷ xs} (here refl) Px with P? x
    ... | yes Px′ rewrite P-irrelevant Px Px′ = here refl
    ... | no ¬Px = contradiction Px ¬Px
    Σfilter-∈ {y ∷ xs} (there x∈xs) Px with P? y
    ... | yes _ = there (Σfilter-∈ x∈xs Px)
    ... | no  _ = Σfilter-∈ x∈xs Px

    Σfilter-∋ : ∀ {xs x} (Px : P x) → (x , Px) ∈ Σfilter xs → x ∈ xs
    Σfilter-∋ {[]} Px ()
    Σfilter-∋ {y ∷ xs} Px x∈xs with P? y
    Σfilter-∋ {y ∷ xs} _ (here refl) | yes _ = here refl
    Σfilter-∋ {y ∷ xs} Px (there x∈xs) | yes _ = there (Σfilter-∋ Px x∈xs)
    ... | no _ = there (Σfilter-∋ Px x∈xs)

    Σfilter-∋-injective : ∀ {xs x} Px (ix₁ ix₂ : (x , Px) ∈ Σfilter xs) → Σfilter-∋ {xs} Px ix₁ ≡ Σfilter-∋ Px ix₂ → ix₁ ≡ ix₂
    Σfilter-∋-injective {[]} Px () () eq
    Σfilter-∋-injective {y ∷ xs} Px ix₁ ix₂ eq with P? y
    Σfilter-∋-injective {y ∷ xs} .p (here refl) (here refl) eq | yes p = refl
    Σfilter-∋-injective {y ∷ xs} .p (here refl) (there ix₂) () | yes p
    Σfilter-∋-injective {y ∷ xs} .p (there ix₁) (here refl) () | yes p
    Σfilter-∋-injective {y ∷ xs} Px (there ix₁) (there ix₂) eq | yes p = cong there (Σfilter-∋-injective _ _ _ (there-injective eq))
    Σfilter-∋-injective {y ∷ xs} Px ix₁ ix₂ eq | no ¬p = Σfilter-∋-injective _ _ _ (there-injective eq)

filter : ∀ {A : Set} {P : A → Set} → IrrelevantPred P → Decidable P → Enumeration A → Enumeration (Σ A P)
filter P-irrelevant P? enum = record
  { list = Σfilter (list enum)
  ; complete = λ { (x , Px) → Σfilter-∈ (complete enum x) Px }
  ; entries-unique = λ ix₁ ix₂ → Σfilter-∋-injective _ _ _ (entries-unique enum (Σfilter-∋ _ ix₁) (Σfilter-∋ _ ix₂)) }
  where open Filter P-irrelevant P?
