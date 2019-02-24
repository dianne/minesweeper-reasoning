module Minesweeper.Enumeration where

open import Data.Fin as Fin using (Fin; zero; suc)
import      Data.Fin.Properties as Fin
import      Data.Fin.Permutation as Fin
open import Data.Nat as ℕ hiding (_⊔_)
import      Data.Nat.Properties as ℕ
open import Data.Empty
open import Data.Product as Σ using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Function
open import Function.Equality                 using (Π; _⟶_; _⟨$⟩_)                        renaming (_∘_ to _∘⟵_)
open import Function.Equivalence              using (Equivalence; _⇔_)
open import Function.Injection  as Injection  using (Injective; Injection; _↣_; injection) renaming (_∘_ to _∘↢_)
open import Function.Surjection as Surjection using (Surjective)                           renaming (_∘_ to _∘↞_)
open import Function.Bijection  as Bijection  using (Bijective)
open import Function.Inverse    as Inverse    using (Inverse; _↔_)                         renaming (_∘_ to _∘↔_; id to id↔; sym to sym↔)
open import Relation.Nullary
open import Relation.Nullary.Negation
import      Relation.Nullary.Decidable as Decidable
open import Relation.Unary  using (Decidable)
open import Relation.Binary using (Setoid; _Respects_) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; →-to-⟶)
import      Relation.Binary.Construct.On as On
open import Level renaming (zero to lzero; suc to lsuc)

-- in order to talk about the number of mines adjacent to a tile, we define Enumeration:
-- a bijective correspondence between some type and the set of natural numbers less
-- than some `n`. then, `n` can be seen as the number of elements of that type.
-- by enumerating a type corresponding to the mines adjacent to a given tile, we can get
-- the number of how many there are.
-- our goal here is to develop the necessary machinery to do that. specifically, we need
-- that all Enumerations of a type have the same number of elements, we need to be able to
-- be able to enumerate the adjacent mines of a tile, (which we get by enumerating any m×n
-- grid and filtering by a predicate), and we need that a list with unique entries with
-- the same length as an Enumeration is itself complete
record Enumeration {c ℓ} (A : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    cardinality : ℕ
    lookup : Inverse (Fin.setoid cardinality) A

open Enumeration


-- first, Enumerations of the same type are equal in `cardinality`
cardinality-≡ : ∀ {c ℓ} {A : Setoid c ℓ} (enum₁ enum₂ : Enumeration A) →
  cardinality enum₁ ≡ cardinality enum₂
cardinality-≡ enum₁ enum₂ = Fin.↔⇒≡ (sym↔ (lookup enum₂) ∘↔ lookup enum₁)

-- next, if you have enough unique elements of a type, then you have all of them!
injection-surjective : ∀ {c ℓ} {A : Setoid c ℓ} (enum : Enumeration A) (f : Injection (Fin.setoid (cardinality enum)) A) →
  Surjective (Injection.to f)
injection-surjective {A = A} enum f = record
  { from = translateIndex-enum⟶f ∘⟵ Inverse.from (lookup enum)
  ; right-inverse-of = λ a →
    Inverse.injective (sym↔ (lookup enum))
      (Surjective.right-inverse-of (fin-injection-surjective translateIndex-f↣enum)
        (Inverse.from (lookup enum) ⟨$⟩ a)) }
  where
  -- any injection `f : Fin n ↣ Fin n` is also surjective: by the pigeonhole principle,
  -- if there is any `m` for which no `n` exists such that `f n ≡ m`, then there must
  -- be distinct `i` and `j` with `f i ≡ f j`; however, this cannot happen, since `f`
  -- is injective.
  fin-injection-surjective : ∀ {n} (g : Fin n ↣ Fin n) → Surjective (Injection.to g)
  fin-injection-surjective g = record
    { from = →-to-⟶ (proj₁ ∘ g⁻¹)
    ; right-inverse-of = proj₂ ∘ g⁻¹ }
    where
    -- for a constructive proof we have to find the `n` for which `f n ≡ m` for each `m`.
    -- conveniently, Fin.pigeonhole also gives us that: if we extend `f` with a duplicate mapping to `m`,
    -- then Fin.pigeonhole finds the other one. there are no other duplicates because f is injective.
    g⁻¹ : ∀ m → ∃ λ n → Injection.to g ⟨$⟩ n ≡ m
    g⁻¹ m with Fin.pigeonhole ℕ.≤-refl λ { zero → m ; (suc i) → Injection.to g ⟨$⟩ i }
    g⁻¹ m | zero  , zero  , zero≢zero , m≡m   = contradiction ≡.refl zero≢zero
    g⁻¹ m | zero  , suc j , zero≢sucj , m≡gj  = j , ≡.sym m≡gj
    g⁻¹ m | suc i , zero  , suci≢zero , gi≡m  = i , gi≡m
    g⁻¹ m | suc i , suc j , suci≢sucj , gi≡gj = contradiction (≡.cong suc (Injection.injective g gi≡gj)) suci≢sucj

  translateIndex-f↣enum : Fin (cardinality enum) ↣ Fin (cardinality enum)
  translateIndex-f↣enum = Inverse.injection (sym↔ (lookup enum)) ∘↢ f

  translateIndex-enum⟶f : Fin.setoid (cardinality enum) ⟶ Fin.setoid (cardinality enum)
  translateIndex-enum⟶f = Surjective.from (fin-injection-surjective translateIndex-f↣enum)


-- if we have two setoids, a pair of inverse functions between them, and Enumeration for one, we can get an Enumeration of the same cardinality for the other
map : ∀ {a b ℓ₁ ℓ₂} {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} (f : Inverse A B) → Enumeration A → Enumeration B
map f enum = record
  { cardinality = cardinality enum
  ; lookup = f ∘↔ lookup enum }


-- next, we build towards the ability to enumerate neighboring tiles on a grid

-- to number the rows and columns of the board, we use allFin
allFin : ∀ n → Enumeration (Fin.setoid n)
allFin n = record
  { cardinality = n
  ; lookup = id↔ }


-- _⊗_:
-- to enumerate coordinates on a board, we take the cartesian product of the rows and columns
module _ {a b ℓ₁ ℓ₂} {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} where
  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  open import Data.Unit
  open import Data.List as List hiding (lookup)
  open import Data.List.Properties using (length-replicate)
  open import Data.List.Relation.Unary.Any
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)

  -- from what I can tell, the easiest way to witness a bijection `(Fin m × Fin n) ↔ Fin (m * n)`,
  -- which we want in order to construct a product enumeration, seems to be a be indirectly through
  -- Data.List.Membership.Propositional.Properties.⊗-∈↔
  -- so to that end, we want bijections `Fin n ↔ tt ∈ replicate n tt`, or equivalently
  -- `tt ∈ tts ↔ Fin (length tts)` in order to utilize it

  abstract
    private
      module _ {ℓ} {T : Set ℓ} (t : T) (T-prop : ∀ t′ → t′ ≡ t) where
        ∈-lookup′ : ∀ {ts} → Fin (length ts) → t ∈ ts
        ∈-lookup′ {ts} i = ≡.subst (_∈ ts) (T-prop (List.lookup ts i)) (∈-lookup ts i)

        index∘∈-lookup : (ts : List T) (i : Fin (length ts)) → index (∈-lookup ts i) ≡ i
        index∘∈-lookup []       ()
        index∘∈-lookup (t ∷ ts) zero    = ≡.refl
        index∘∈-lookup (t ∷ ts) (suc i) = ≡.cong suc (index∘∈-lookup ts i)

        index∘∈-lookup′ : ∀ {ts : List T} (i : Fin (length ts)) → index (∈-lookup′ {ts} i) ≡ i
        index∘∈-lookup′ {ts} i with T-prop (List.lookup ts i)
        index∘∈-lookup′ {ts} i    | ≡.refl = index∘∈-lookup ts i

        ∈-lookup∘index : ∀ {ts} (t∈ts : t ∈ ts) → ∈-lookup ts (index t∈ts) ≅ t∈ts
        ∈-lookup∘index           (here ≡.refl) = ≅.refl
        ∈-lookup∘index {t′ ∷ ts} (there t∈ts)  = ≅.icong (_∈ ts) (T-prop _) there (∈-lookup∘index t∈ts)

        ∈-lookup′∘index : ∀ {ts} (t∈ts : t ∈ ts) → ∈-lookup′ (index t∈ts) ≡ t∈ts
        ∈-lookup′∘index {ts} t∈ts with ∈-lookup∘index t∈ts
        ...                          | ∈-lookup∘index≅id with index t∈ts
        ...                                                 | i with T-prop (List.lookup ts i)
        ∈-lookup′∘index {ts} t∈ts    | ≅.refl               | i    | ≡.refl = ≡.refl

        index↔ : ∀ {ts} → t ∈ ts ↔ Fin (length ts)
        index↔ = record
          { to   = →-to-⟶ index
          ; from = →-to-⟶ ∈-lookup′
          ; inverse-of = record
            { left-inverse-of  = ∈-lookup′∘index
            ; right-inverse-of = index∘∈-lookup′ } }

        index↔′ : ∀ {n} → t ∈ replicate n t ↔ Fin n
        index↔′ {n} = ≡.subst (λ m → t ∈ replicate n t ↔ Fin m) (length-replicate n) (index↔ {replicate n t})

    _⊗_ : Enumeration A → Enumeration B → Enumeration (×-setoid A B)
    enum₁ ⊗ enum₂ = record
      { cardinality = _ -- incidentally (and not proven here), this is `cardinality enum₁ * cardinality enum₂`
      ; lookup =
        (lookup enum₁ ×-inverse lookup enum₂)                             ∘↔
        sym↔ Pointwise-≡↔≡                                                ∘↔
        index↔′ tt (λ { tt → ≡.refl }) ×-↔ index↔′ tt (λ { tt → ≡.refl }) ∘↔
        sym↔ ⊗-∈↔                                                         ∘↔
        sym↔ (index↔ (tt , tt) (λ { (tt , tt) → ≡.refl })) }


-- filter:
-- to enumerate the neighbors of a tile, or the mines or safe tiles neighboring a tile,
-- we filter the enumeration of all coordinates to just the ones satisfying an appropriate prdciate
count : ∀ {a p m} {A : Set a} {P : A → Set p} → Decidable P → (Fin m → A) → ℕ
count {m = zero}  P? f = zero
count {m = suc m} P? f with P? (f zero)
...                       | yes Pz = suc (count P? (f ∘ suc))
...                       | no ¬Pz = count P? (f ∘ suc)

count-≡ : ∀ {a b p q m} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
  (P? : Decidable P) (Q? : Decidable Q) (f : Fin m → A) (g : Fin m → B) →
    (∀ i → P (f i) ⇔ Q (g i)) → count P? f ≡ count Q? g
count-≡ {m = zero}  P? Q? f g Pf⇔Qg = ≡.refl
count-≡ {m = suc m} P? Q? f g Pf⇔Qg with P? (f zero) | Q? (g zero)
count-≡ {m = suc m} P? Q? f g Pf⇔Qg    | yes Pfz     | yes Qgz = ≡.cong suc (count-≡ P? Q? (f ∘ suc) (g ∘ suc) (Pf⇔Qg ∘ suc))
count-≡ {m = suc m} P? Q? f g Pf⇔Qg    | yes Pfz     | no ¬Qgz = contradiction (Equivalence.to   (Pf⇔Qg zero) ⟨$⟩ Pfz) ¬Qgz
count-≡ {m = suc m} P? Q? f g Pf⇔Qg    | no ¬Pfz     | yes Qgz = contradiction (Equivalence.from (Pf⇔Qg zero) ⟨$⟩ Qgz) ¬Pfz
count-≡ {m = suc m} P? Q? f g Pf⇔Qg    | no ¬Pfz     | no ¬Qgz = count-≡ P? Q? (f ∘ suc) (g ∘ suc) (Pf⇔Qg ∘ suc)

filter′ : ∀ {a p m} {A : Set a} {P : A → Set p} (P? : Decidable P) (f : Fin m → A) →
  Fin (count P? f) → ∃ P
filter′ {m = zero}  P? f = λ ()
filter′ {m = suc m} P? f with P? (f zero)
...                         | yes Pz = λ { zero    → f zero , Pz
                                         ; (suc i) → filter′ P? (f ∘ suc) i }
...                         | no ¬Pz = filter′ P? (f ∘ suc)


-- filter′ preserves Enumerations:
-- the result of filtering by a predicate P is an Enumeration of all elements satisfying P
module _ {a ℓ p} {A : Setoid a ℓ} {P : Setoid.Carrier A → Set p} where
  open Setoid A
  open import Relation.Binary.Reasoning.Setoid A

  private
    ∃-setoid : Setoid (a ⊔ p) ℓ
    ∃-setoid = On.setoid {B = ∃ P} A proj₁

    module _ (P? : Decidable P) where
      filter-index : ∀ {m} (f : Fin m → Carrier) (i : Fin m) →
        P (f i) → ∃ λ i′ → proj₁ (filter′ P? f i′) ≈ f i
      filter-index {zero}  f ()
      filter-index {suc m} f i    with P? (f zero)
      filter-index {suc m} f zero    | yes Pz = const (zero , refl)
      filter-index {suc m} f (suc i) | yes Pz = Σ.map suc id ∘ filter-index (f ∘ suc) i
      filter-index {suc m} f zero    | no ¬Pz = ⊥-elim ∘ ¬Pz
      filter-index {suc m} f (suc i) | no ¬Pz = filter-index (f ∘ suc) i

      filter-index-cong : ∀ {m} (f : Fin m → Carrier) {i j : Fin m} (Pfi : P (f i)) (Pfj : P (f j)) →
        P Respects _≈_ → i ≡ j → proj₁ (filter-index f i Pfi) ≡ proj₁ (filter-index f j Pfj)
      filter-index-cong {zero}  f {}      Pfi Pfj P-resp-≈ i≡j
      filter-index-cong {suc m} f {i}     Pfi Pfj P-resp-≈ ≡.refl with P? (f zero)
      filter-index-cong {suc m} f {zero}  Pfi Pfj P-resp-≈ ≡.refl    | yes Pz = ≡.refl
      filter-index-cong {suc m} f {suc i} Pfi Pfj P-resp-≈ ≡.refl    | yes Pz = ≡.cong suc (filter-index-cong (f ∘ suc) Pfi Pfj P-resp-≈ ≡.refl)
      filter-index-cong {suc m} f {zero}  Pfi Pfj P-resp-≈ ≡.refl    | no ¬Pz = ⊥-elim (¬Pz Pfi)
      filter-index-cong {suc m} f {suc i} Pfi Pfj P-resp-≈ ≡.refl    | no ¬Pz = filter-index-cong (f ∘ suc) Pfi Pfj P-resp-≈ ≡.refl

      unfilter-index : ∀ {m} (f : Fin m → Carrier) (i′ : Fin (count P? f)) →
        ∃ λ i → proj₁ (filter′ P? f i′) ≈ f i
      unfilter-index {zero}  f ()
      unfilter-index {suc m} f i′ with P? (f zero)
      unfilter-index {suc m} f zero     | yes Pz = zero , refl
      unfilter-index {suc m} f (suc i′) | yes Pz = Σ.map suc id (unfilter-index (f ∘ suc) i′)
      unfilter-index {suc m} f i′       | no ¬Pz = Σ.map suc id (unfilter-index (f ∘ suc) i′)

      unfilter-index-injective : ∀ {m} (f : Fin m → Carrier) →
        Injective (→-to-⟶ {B = Fin.setoid m} (proj₁ ∘ unfilter-index f))
      unfilter-index-injective {zero}  f {}       {}       ui′≡uj′
      unfilter-index-injective {suc m} f {i′}     {j′}     ui′≡uj′ with P? (f zero)
      unfilter-index-injective {suc m} f {zero}   {zero}   ui′≡uj′    | yes Pz = ≡.refl
      unfilter-index-injective {suc m} f {zero}   {suc j′} ()         | yes Pz
      unfilter-index-injective {suc m} f {suc i′} {zero}   ()         | yes Pz
      unfilter-index-injective {suc m} f {suc i′} {suc j′} ui′≡uj′    | yes Pz = ≡.cong suc (unfilter-index-injective (f ∘ suc) (Fin.suc-injective ui′≡uj′))
      unfilter-index-injective {suc m} f {i′}     {j′}     ui′≡uj′    | no ¬Pz = unfilter-index-injective (f ∘ suc) (Fin.suc-injective ui′≡uj′)

  filter : Decidable P → P Respects _≈_ → Enumeration A → Enumeration ∃-setoid
  filter P? P-resp-≈ enum = record
    { cardinality = count P? enum-lookup
    ; lookup = Inverse.fromBijection record
      { to = →-to-⟶ (filter′ P? enum-lookup)
      ; bijective = filter′-bijective } }
    where
    enum-lookup : Fin (cardinality enum) → Carrier
    enum-lookup = Inverse.to (lookup enum) ⟨$⟩_

    enum-index : Carrier → Fin (cardinality enum)
    enum-index = Inverse.from (lookup enum) ⟨$⟩_

    lookup∘index : ∀ x → enum-lookup (enum-index x) ≈ x
    lookup∘index = Inverse.right-inverse-of (lookup enum)

    abstract
      filter′-bijective : Bijective (→-to-⟶ (filter′ P? enum-lookup))
      filter′-bijective = record
        { injective = λ {i′} {j′} f′i′≈f′j′ →
          unfilter-index-injective P? enum-lookup
            (Inverse.injective (lookup enum)
              (begin
                enum-lookup (proj₁ (unfilter-index P? enum-lookup i′)) ≈⟨ sym (proj₂ (unfilter-index P? enum-lookup i′)) ⟩
                proj₁ (filter′ P? enum-lookup i′)                      ≈⟨ f′i′≈f′j′ ⟩
                proj₁ (filter′ P? enum-lookup j′)                      ≈⟨ proj₂ (unfilter-index P? enum-lookup j′) ⟩
                enum-lookup (proj₁ (unfilter-index P? enum-lookup j′)) ∎))
        ; surjective = record
          { from = record
            { _⟨$⟩_ = λ { (x , Px) →
              proj₁ (filter-index P? enum-lookup
                (enum-index x)
                (P-resp-≈ (sym (lookup∘index x)) Px)) }
            ; cong = λ { {x , Px} {y , Py} x≈y →
              filter-index-cong P? enum-lookup
                (P-resp-≈ (sym (lookup∘index x)) Px)
                (P-resp-≈ (sym (lookup∘index y)) Py)
                P-resp-≈
                (Π.cong (Inverse.from (lookup enum)) x≈y) } }
          ; right-inverse-of = λ { (x , Px) →
            begin
              _                          ≈⟨ proj₂ (filter-index P? enum-lookup (enum-index x) (P-resp-≈ (sym (lookup∘index x)) Px)) ⟩
              enum-lookup (enum-index x) ≈⟨ lookup∘index x ⟩
              x                          ∎ } } }


-- the total number of neighbors a tile has equals the sum of its safe neighbors and mine-containing neighbors.
-- in general, given an enumeration of a setoid, an enumeration of its elements satisfying a predicate, and another
-- of those satisfying its negation, the cardinality of the whole setoid will equal the sum of the cardinalities of
-- the two parts.
module _ {a ℓ p} {A : Setoid a ℓ} {P : Setoid.Carrier A → Set p} (P? : Decidable P) (P-resp-≈ : P Respects (Setoid._≈_ A)) where
  open import Relation.Binary.Consequences using (P-resp⟶¬P-resp)

  filter¬ : Enumeration A → Enumeration (On.setoid {B = ∃ (¬_ ∘ P)} A proj₁)
  filter¬ = filter (¬? ∘ P?) (P-resp⟶¬P-resp {P = P} (Setoid.sym A) P-resp-≈)

  cardinality-filter : ∀ enum →
    cardinality enum ≡ cardinality (filter P? P-resp-≈ enum) ℕ.+ cardinality (filter¬ enum)
  cardinality-filter enum = count-partition′ (Inverse.to (lookup enum) ⟨$⟩_) where
    count-partition′ : ∀ {m} (f : Fin m → Setoid.Carrier A) → m ≡ count P? f ℕ.+ count (¬? ∘ P?) f
    count-partition′ {zero}  f = ≡.refl
    count-partition′ {suc m} f with P? (f zero)
    count-partition′ {suc m} f | yes Pz = ≡.cong suc (count-partition′ (f ∘ suc))
    count-partition′ {suc m} f | no ¬Pz = ≡.trans (≡.cong suc (count-partition′ (f ∘ suc))) (≡.sym (ℕ.+-suc _ _))

cardinality-partition : ∀ {a ℓ p} {A : Setoid a ℓ} {P : Setoid.Carrier A → Set p} (P-resp-≈ : P Respects (Setoid._≈_ A))
  (enumA : Enumeration A)
  (enum∃P  : Enumeration (On.setoid {B = ∃ P}        A proj₁))
  (enum∃¬P : Enumeration (On.setoid {B = ∃ (¬_ ∘ P)} A proj₁)) →
    cardinality enumA ≡ cardinality enum∃P ℕ.+ cardinality enum∃¬P
cardinality-partition {A = A} {P = P} P-resp-≈ enumA enum∃P enum∃¬P = begin
  cardinality enumA                                                                   ≡⟨ cardinality-filter P? P-resp-≈ enumA ⟩
  cardinality (filter P? P-resp-≈ enumA) ℕ.+ cardinality (filter¬ P? P-resp-≈ enumA)  ≡⟨ ≡.cong₂ ℕ._+_
                                                                                           (cardinality-≡ (filter P? P-resp-≈ enumA) enum∃P)
                                                                                           (cardinality-≡ (filter¬ P? P-resp-≈ enumA) enum∃¬P) ⟩
  cardinality enum∃P                     ℕ.+ cardinality enum∃¬P                      ∎
  where
  open ≡.≡-Reasoning
  open Setoid A

  _≈?_ : Decidable₂ _≈_
  _≈?_ = Decidable.via-injection (Inverse.injection (sym↔ (lookup enumA))) Fin._≟_

  P? : Decidable P 
  P? x with Fin.any? ((_≈? x) ∘ proj₁ ∘ (Inverse.to (lookup enum∃P) ⟨$⟩_))
  P? x | yes ∃i = yes (P-resp-≈ (proj₂ ∃i) (proj₂ (Inverse.to (lookup enum∃P) ⟨$⟩ proj₁ ∃i)))
  P? x | no ¬∃i = no (¬∃i ∘ λ Px → Inverse.from (lookup enum∃P) ⟨$⟩ (x , Px) , Inverse.right-inverse-of (lookup enum∃P) (x , Px))
