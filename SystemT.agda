open import Data.List    using (List; _∷_; [])
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

module SystemT where

  data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
    i0 : {x : A} {xs : List A} → x ∈ (x ∷ xs)
    iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)


  data TType : Set where
    base  : TType
    _⟶_ : TType → TType → TType

  Context = List TType
  _,,_ : Context → TType → Context
  Γ ,, τ = τ ∷ Γ

  infixr 10 _⟶_
  infixr 9 _,,_
  infixr 8 _⊢_

  data _⊢_ (Γ : Context) : TType → Set where
    -- Some constant of the base type whose type is immediate.
    c : Γ ⊢ base
    -- Variable.
    var : {τ : TType} → τ ∈ Γ → Γ ⊢ τ
    -- Function introduction.
    lam : {τ₁ τ₂ : TType} → Γ ,, τ₁ ⊢ τ₂ → Γ ⊢ τ₁ ⟶ τ₂
    -- Function application.
    app : {τ₁ τ₂ : TType} → (Γ ⊢ τ₁ ⟶ τ₂) → Γ ⊢ τ₁ → Γ ⊢ τ₂

  module Semantics (B : Set) (elB : B) where

    -- Interpretation of System T types to Agda types.
    ⟦_⟧t : TType → Set
    ⟦ base ⟧t = B
    ⟦ τ₁ ⟶ τ₂ ⟧t = ⟦ τ₁ ⟧t → ⟦ τ₂ ⟧t

    -- Interpretation of System T contexts to Agda types.
    ⟦_⟧c : Context → Set
    ⟦ [] ⟧c = ⊤
    ⟦ τ ∷ Γ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t

    -- Interpretation of terms.
    ⟦_⟧ : {Γ : Context} {τ : TType} → (Γ ⊢ τ) → ⟦ Γ ⟧c → ⟦ τ ⟧t
    ⟦ c ⟧ γ = elB
    ⟦ var x ⟧ γ = {!  !}
    ⟦ lam e ⟧ γ x = {!   !}
    ⟦ app e₁ e₂ ⟧ γ = {!   !}
