-- Section 6.1

open import Level
open import Relation.Binary

module SortedTrees {c ℓ≈ ℓ≤} (totalOrder : TotalOrder c ℓ≈ ℓ≤) where

open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum

open TotalOrder totalOrder renaming
  (Carrier to A)

data T : Set c where
  lf : T
  nd : T → A → T → T

infix 4 _∀≤_ _≤∀_

_∀≤_ : T → A → Set ℓ≤
lf ∀≤ _ = ⊤
nd u m v ∀≤ a = u ∀≤ a × m ≤ a × v ∀≤ a

_≤∀_ : A → T → Set ℓ≤
_ ≤∀ lf = ⊤
a ≤∀ nd u m v = a ≤∀ u × a ≤ m × a ≤∀ v

Sorted : T → Set ℓ≤
Sorted lf = ⊤
Sorted (nd u m v) = (Sorted u × u ∀≤ m) × (m ≤∀ v × Sorted v)

insert : A → T → T
insert a lf = nd lf a lf

insert a (nd u m v) with total a m
... | inj₁ _ = nd (insert a u) m v
... | inj₂ _ = nd u m (insert a v)

insert∀≤ : ∀ {a n : A} {u : T} → a ≤ n → u ∀≤ n → insert a u ∀≤ n
insert∀≤ {a} {n} {lf} a≤n _ = tt , a≤n , tt
insert∀≤ {a} {n} {nd u m v} a≤n (u≤n , m≤n , v≤n) with total a m
... | inj₁ _ = insert∀≤ a≤n u≤n , m≤n , v≤n
... | inj₂ _ = u≤n , m≤n , insert∀≤ a≤n v≤n

insert≤∀ : ∀ {n a : A} {v : T} → n ≤ a → n ≤∀ v → n ≤∀ insert a v
insert≤∀ {n} {a} {lf} n≤a _ = tt , n≤a , tt
insert≤∀ {n} {a} {nd u m v} n≤a (n≤u , n≤m , n≤v) with total a m
... | inj₁ _ = insert≤∀ n≤a n≤u , n≤m , n≤v
... | inj₂ _ = n≤u , n≤m , insert≤∀ n≤a n≤v

sorted-insert : (a : A) → (t : T) → Sorted t → Sorted (insert a t)
sorted-insert a lf s = (tt , tt) , (tt , tt)
sorted-insert a (nd u m v) ((su , u≤m) , (v≤m , sv)) with total a m
... | inj₁ a≤m = (sorted-insert a u su , insert∀≤ a≤m u≤m)  , (v≤m , sv)
... | inj₂ m≤a = (su , u≤m) , (insert≤∀ m≤a v≤m , sorted-insert a v sv)

record ST : Set (c ⊔ ℓ≤) where
  constructor st
  field
    tree : T
    sorted : Sorted tree

insertST : (a : A) → ST → ST
insertST a (st tree sorted) = st _ (sorted-insert a tree sorted)
