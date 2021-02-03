module Dual.Values where

open import Dual.Syntax
open import Data.Product using (Σ ; proj₁ ; proj₂)

data Value : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A → Set 
data Covalue : ∀ {Γ Θ A} → A ∣ Γ ⟶ Θ → Set

data Value where

  V-var : ∀ {Γ Θ A} {x : Γ ∋ A}
      ---------
    → Value {Θ = Θ} (` x)

  V-prod : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B}
    → Value M
    → Value N
      ---------------
    → Value `⟨ M , N ⟩

  V-inl : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A}
    → Value M
      -------------
    → Value (inl⟨_⟩ {B = B} M)

  V-inr : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ B}
    → Value M
      -------------
    → Value (inr⟨_⟩ {A = A} M)

  V-not : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ}
      --------------
    → Value not[ K ]


data Covalue where
  
  CV-covar : ∀ {Γ Θ A} {α : Θ ∋ A}
      -------
    → Covalue {Γ = Γ} (` α)

  CV-sum : ∀ {Γ Θ A B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Covalue K
    → Covalue L
      ------------------
    → Covalue `[ K , L ]

  CV-fst : ∀ {Γ Θ A B} {K : A ∣ Γ ⟶ Θ}
    → Covalue K
      ----------------
    → Covalue (fst[_] {B = B} K)

  CV-snd : ∀ {Γ Θ A B} {K : B ∣ Γ ⟶ Θ}
    → Covalue K
      ----------------
    → Covalue (snd[_] {A = A} K)

  CV-not : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      --------------
    → Covalue not⟨ M ⟩

TermValue : Context → Context → Type → Set
TermValue Γ Θ A = Σ (Γ ⟶ Θ ∣ A) Value
