open import Data.Vec as Vec using (Vec)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Coords

Board : Set → Bounds → Set
Board A (w , h) = Vec (Vec A w) h

lookup : ∀ {A bounds} → Coords bounds → Board A bounds → A
lookup (x , y) grid = Vec.lookup x (Vec.lookup y grid)

_[_]≔_ : ∀ {A bounds} → Board A bounds → Coords bounds → A → Board A bounds
grid [ (x , y) ]≔ value = grid Vec.[ y ]≔ (Vec.lookup y grid Vec.[ x ]≔ value)

_Neighboring_on_ : ∀ {A bounds} → A → Coords bounds → Board A bounds → Set
tile Neighboring coords on grid = Σ[ neighbor ∈ Neighbor coords ] tile ≡ lookup (proj₁ neighbor) grid
