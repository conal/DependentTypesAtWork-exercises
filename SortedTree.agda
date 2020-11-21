-- Section 6.2

open import Level
open import Relation.Binary

module SortedTree {c ℓ≈ ℓ≤} (totalOrder : TotalOrder c ℓ≈ ℓ≤) where

open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum

open TotalOrder totalOrder renaming (Carrier to A)

open import SortingTrees totalOrder using (Sorted) renaming
  (T to UT; lf to ulf; nd to und; _*≤_ to _#≤_ ; _≤*_ to _≤#_)

mutual

  data T : Set (c ⊔ ℓ≤) where
    lf : T
    nd : (u : T) → (m : A) → (v : T)
       → u *≤ m → m ≤* v
       → T

  infix 4 _*≤_ _≤*_

  _*≤_ : T → A → Set ℓ≤
  lf *≤ _ = ⊤
  nd u m v _ _ *≤ n = m ≤ n × v *≤ n

  _≤*_ : A → T → Set ℓ≤
  _ ≤* lf = ⊤
  n ≤* nd u m v _ _ = n ≤* u × n ≤ m

private
  variable
    m n o : A
    u v t : T



*-trans : ∀ {u n o} → u *≤ n → n ≤ o → u *≤ o
*-trans {lf} _ _ = tt
*-trans {nd u m v _ _} (m≤n , v≤n) n≤o = trans m≤n n≤o , *-trans v≤n n≤o

trans-* : ∀ {v n o} → n ≤ o → o ≤* v → n ≤* v
trans-* {lf} _ _ = tt
trans-* {nd u m v _ _} n≤o (o≤u , o≤m) = trans-* n≤o o≤u , trans n≤o o≤m

t→ut : T -> UT
t→ut lf = ulf
t→ut (nd u m v _ _) = und (t→ut u) m (t→ut v)

t→ut#≤ : ∀ {u n} → u *≤ n → t→ut u #≤ n
t→ut#≤ {lf} u≤n = tt
t→ut#≤ {nd u m v u≤m m≤v} (m≤n , v≤n) =
  t→ut#≤ (*-trans u≤m m≤n) , m≤n , t→ut#≤ v≤n

≤#t→ut : ∀ {v n} → n ≤* v → n ≤# t→ut v
≤#t→ut {lf} _ = tt
≤#t→ut {nd u m v u≤m m≤v} (n≤u , n≤m) =
 ≤#t→ut n≤u , n≤m , ≤#t→ut (trans-* n≤m m≤v)

t→ut-sorted : (t : T) -> Sorted (t→ut t)
t→ut-sorted lf = tt
t→ut-sorted (nd u m v u≤m m≤v) =
    (t→ut-sorted u , t→ut#≤ u≤m)
  , (≤#t→ut m≤v , t→ut-sorted v )

mutual
  ut-sorted→t : {ut : UT} -> Sorted ut -> T
  ut-sorted→t {ulf} _ = lf
  ut-sorted→t {und u m v} ((su , u≤m) , (m≤v , sv)) =
    nd (ut-sorted→t su) m (ut-sorted→t sv)
       (#≤→*≤ u≤m su) (≤#→≤* m≤v sv)

  #≤→*≤ : ∀ {u : UT} {m} → u #≤ m → (su : Sorted u) → ut-sorted→t su *≤ m
  #≤→*≤ {ulf} tt tt = tt
  #≤→*≤ {und u n v} (u≤m , n≤m , v≤m) ((su , u≤n) , (n≤v , sv)) =
    n≤m , #≤→*≤ v≤m sv

  ≤#→≤* : ∀ {v : UT} {m} → m ≤# v → (sv : Sorted v) → m ≤* ut-sorted→t sv
  ≤#→≤* {ulf} tt tt = tt
  ≤#→≤* {und u n v} (m≤u , m≤n , m≤v) ((su , u≤n) , (n≤v , sv)) =
    ≤#→≤* m≤u su , m≤n
