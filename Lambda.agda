-- From "Dependent Types at Work", section 3.3 

-- Exercise: Define lambda terms as an inductive family indexed by the maximal
-- number of free variables allowed in the term.

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Function

private
  variable
    n : ℕ

data L₁ : ℕ → Set where
  Var₁ : Fin n → L₁ n
  App₁ : L₁ n → L₁ n → L₁ n
  Lam₁ : L₁ (suc n) → L₁ n

-- Try also to define typed lambda terms as an inductive family indexed by the
-- type of the term.

data Ty : Set where
  unit : Ty
  _⟶_ : Ty → Ty → Ty

Context : ℕ → Set
Context n = Vec Ty n

private
  variable
    σ τ : Ty
    Γ : Context n

data L : Context n → Ty → Set where
  Var : {Γ : Context n} → (i : Fin n) → L Γ (lookup Γ i)
  App : L Γ (σ ⟶ τ) → L Γ σ → L Γ τ
  Lam : L (σ ∷ Γ) τ → L Γ (σ ⟶ τ)

open import Data.Unit

⟦_⟧ₜ : Ty → Set
⟦ unit ⟧ₜ = ⊤
⟦ σ ⟶ τ ⟧ₜ = ⟦ σ ⟧ₜ → ⟦ τ ⟧ₜ

Env : ∀ {n} → Context n → Set
Env {n} Γ = (i : Fin n) → ⟦ lookup Γ i ⟧ₜ

nil : Env []
nil ()

push : {τ : Ty} → ⟦ τ ⟧ₜ → Env Γ → Env (τ ∷ Γ)
push x ρ zero    = x
push x ρ (suc i) = ρ i

-- ⟦_⟧ : L Γ τ → Env Γ → ⟦ τ ⟧ₜ
-- ⟦  Var i  ⟧ ρ = ρ i
-- ⟦ App u v ⟧ ρ = (⟦ u ⟧ ρ) (⟦ v ⟧ ρ)
-- ⟦  Lam u  ⟧ ρ = λ x → ⟦ u ⟧ (push x ρ)

-- Rework to avoid ⟦_⟧ under λ

⟦_⟧ : L Γ τ → Env Γ → ⟦ τ ⟧ₜ
⟦  Var i  ⟧ = (_$ i)
⟦ App u v ⟧ = ⟦ u ⟧ ˢ ⟦ v ⟧
⟦  Lam u  ⟧ = (⟦ u ⟧ ∘_) ∘ flip push
              -- λ ρ → ⟦ u ⟧ ∘ flip push ρ

-- Closed terms
Closed : Ty → Set
Closed = L []

⟦_⟧₀ : Closed τ → ⟦ τ ⟧ₜ
⟦ e ⟧₀ = ⟦ e ⟧ nil

-- TODO: level polymorphism.
