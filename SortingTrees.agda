-- Section 6.1

open import Level
open import Relation.Binary

module SortingTrees {c ℓ≈ ℓ≤} (totalOrder : TotalOrder c ℓ≈ ℓ≤) where

open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum

open TotalOrder totalOrder renaming
  (Carrier to A)

data T : Set c where
  lf : T
  nd : T → A → T → T

infix 4 _T≤_ _≤∀_

_T≤_ : T → A → Set ℓ≤
lf T≤ _ = ⊤
nd u m v T≤ a = u T≤ a × m ≤ a × v T≤ a

_≤T_ : A → T → Set ℓ≤
_ ≤T lf = ⊤
a ≤T nd u m v = a ≤T u × a ≤ m × a ≤T v

Sorted : T → Set ℓ≤
Sorted lf = ⊤
Sorted (nd u m v) = (Sorted u × u T≤ m) × (m ≤T v × Sorted v)

insert : A → T → T
insert a lf = nd lf a lf

insert a (nd u m v) with total a m
... | inj₁ _ = nd (insert a u) m v
... | inj₂ _ = nd u m (insert a v)

insertT≤ : ∀ {a n : A} {u : T} → a ≤ n → u T≤ n → insert a u T≤ n
insertT≤ {a} {n} {lf} a≤n _ = tt , a≤n , tt
insertT≤ {a} {n} {nd u m v} a≤n (u≤n , m≤n , v≤n) with total a m
... | inj₁ _ = insertT≤ a≤n u≤n , m≤n , v≤n
... | inj₂ _ = u≤n , m≤n , insertT≤ a≤n v≤n

insert≤T : ∀ {n a : A} {v : T} → n ≤ a → n ≤T v → n ≤T insert a v
insert≤T {n} {a} {lf} n≤a _ = tt , n≤a , tt
insert≤T {n} {a} {nd u m v} n≤a (n≤u , n≤m , n≤v) with total a m
... | inj₁ _ = insert≤T n≤a n≤u , n≤m , n≤v
... | inj₂ _ = n≤u , n≤m , insert≤T n≤a n≤v

sorted-insert : (a : A) → (t : T) → Sorted t → Sorted (insert a t)
sorted-insert a lf s = (tt , tt) , (tt , tt)
sorted-insert a (nd u m v) ((su , u≤m) , (v≤m , sv)) with total a m
... | inj₁ a≤m = (sorted-insert a u su , insertT≤ a≤m u≤m)  , (v≤m , sv)
... | inj₂ m≤a = (su , u≤m) , (insert≤T m≤a v≤m , sorted-insert a v sv)

record ST : Set (c ⊔ ℓ≤) where
  constructor st
  field
    tree : T
    sorted : Sorted tree

insertST : (a : A) → ST → ST
insertST a (st tree sorted) = st _ (sorted-insert a tree sorted)
