open import SystemT
open import Data.List using ([])

module Examples where

  -- λ x . x
  ex1 : [] ⊢ base ⟶ base
  ex1 = lam (var i0)

  -- λ x . λ y . y
  ex2 : [] ⊢ base ⟶ base ⟶ base
  ex2 = lam (lam (var i0))

  -- λ x . λ y . x
  ex3 : [] ⊢ base ⟶ base ⟶ base
  ex3 = lam (lam (var (iS i0)))
