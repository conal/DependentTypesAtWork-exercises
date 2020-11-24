-- From "Dependent Types at Work", section 3.3 

-- Exercise: Define lambda terms as an inductive family indexed by the maximal
-- number of free variables allowed in the term.

module Lambda where

open import Function
open import Data.List using (List ; [] ; _∷_)

data Ty : Set where
  unit : Ty
  _⟶_ : Ty → Ty → Ty

infix 3 _∈_
data _∈_ {ℓ} {A : Set ℓ} (x : A) : (xs : List A) → Set where
  zero : ∀ {xs} → x ∈ x ∷ xs
  suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

Context : Set
Context = List Ty

private
  variable
    σ τ : Ty
    Γ : Context

data L : Context → Ty → Set where
  Var : ∀ {τ} → τ ∈ Γ  → L Γ τ
  App : L Γ (σ ⟶ τ) → L Γ σ → L Γ τ
  Lam : L (σ ∷ Γ) τ → L Γ (σ ⟶ τ)

open import Data.Unit

⟦_⟧ₜ : Ty → Set
⟦ unit ⟧ₜ = ⊤
⟦ σ ⟶ τ ⟧ₜ = ⟦ σ ⟧ₜ → ⟦ τ ⟧ₜ

-- TODO: could we use Set in place of Ty?

data Env : Context → Set where
  nil : Env []
  push : ∀ {Γ} {τ : Ty} (x : ⟦ τ ⟧ₜ) → (ρ : Env Γ) → Env (τ ∷ Γ)

lookup : ∀ {Γ τ} → τ ∈ Γ → Env Γ → ⟦ τ ⟧ₜ
lookup zero (push x _) = x
lookup (suc z) (push _ ρ) = lookup z ρ

-- ⟦_⟧ : L Γ τ → Env Γ → ⟦ τ ⟧ₜ
-- ⟦ Var x ⟧   ρ = lookup x ρ
-- ⟦ App u v ⟧ ρ =  (⟦ u ⟧ ρ) (⟦ v ⟧ ρ)
-- ⟦ Lam u ⟧   ρ = λ x → ⟦ u ⟧ (push x ρ)

⟦_⟧ : L Γ τ → Env Γ → ⟦ τ ⟧ₜ
⟦  Var x  ⟧ = lookup x
⟦ App u v ⟧ = ⟦ u ⟧ ˢ ⟦ v ⟧
⟦  Lam u  ⟧ = (⟦ u ⟧ ∘_) ∘ flip push
              -- λ ρ → ⟦ u ⟧ ∘ flip push ρ

-- Closed terms
Closed : Ty → Set
Closed = L []

⟦_⟧₀ : Closed τ → ⟦ τ ⟧ₜ
⟦ e ⟧₀ = ⟦ e ⟧ nil

-- TODO: level polymorphism.
