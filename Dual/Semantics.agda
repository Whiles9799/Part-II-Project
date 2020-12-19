module Dual.Semantics where

open import Dual.Syntax
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public

ext : ∀ {Γ Γ′} 
  → (∀ {A} →   Γ ∋ A →     Γ′ ∋ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Γ′ , B ∋ A)
ext ρ `Z     = `Z 
ext ρ (`S x) = `S (ρ x)

rename₁ : ∀ {Γ Γ′ Θ Θ′}
  → (∀ {A} → Γ ∋ A      → Γ′ ∋ A)
    ----------------------------------
  → (∀ {A} → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A)
rename₁ ρ (` x) = `(ρ x)
rename₁ ρ `⟨ M , N ⟩ = `⟨ rename₁ ρ M , rename₁ ρ N ⟩
rename₁ ρ inl⟨ M ⟩ = inl⟨ rename₁ ρ M ⟩
rename₁ ρ inr⟨ M ⟩ = inr⟨ rename₁ ρ M ⟩
rename₁ ρ not[ K ] = not[ {!   !} ]
rename₁ ρ (μθ S) = μθ {!   !}

rename₂ : ∀ {Γ Γ′ Θ Θ′}
  → (∀ {A} → Θ ∋ A → Θ′ ∋ A)
    -------------------------
  → (∀ {A} → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′)
rename₂ ρ (` α) = `(ρ α)
rename₂ ρ fst[ K ] = fst[ rename₂ ρ K ]
rename₂ ρ snd[ K ] = snd[ rename₂ ρ K ]
rename₂ ρ `[ K , L ] = `[ rename₂ ρ K , rename₂ ρ L ]
rename₂ ρ not⟨ M ⟩ = not⟨ rename₁ ?M ⟩
rename₂ ρ (μγ S) = ?

-- data Subst : Context → Context → Context → Context → Set where 
--   ⨀  : ∀ {Γ Θ} → Subst Γ Θ ∅ ∅
--   _,ᵗ_ : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → Γ ⟶ Θ ∣ A → Subst Γ Θ (Γ′ , A) Θ′
--   _,ᶜ_ : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → A ∣ Γ ⟶ Θ → Subst Γ Θ Γ′ (Θ′ , A)

-- exts-var : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → Subst (Γ , A) Θ Γ′ Θ′
-- exts-var ⨀ _ = ⨀
-- exts-var (s ,ⱽ t) 


-- sub-var : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → Γ′ ∋ A → Γ ⟶ Θ ∣ A 
-- sub-var (s ,ᵗ t) `Z = t
-- sub-var (s ,ᵗ t) (`S x) = sub-var s x 
-- sub-var (s ,ᶜ t) x = sub-var s x

-- sub-covar : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → Θ′ ∋ A → A ∣ Γ ⟶ Θ
-- sub-covar (s ,ᵗ t) α = sub-covar s α
-- sub-covar (s ,ᶜ t) `Z = t
-- sub-covar (s ,ᶜ t) (`S x) = sub-covar s x

-- sub-term : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → Γ′ ⟶ Θ′ ∣ A → Γ ⟶ Θ ∣ A
-- sub-coterm : ∀ {Γ Γ′ Θ Θ′ A} → Subst Γ Θ Γ′ Θ′ → A ∣ Γ′ ⟶ Θ′ → A ∣ Γ ⟶ Θ
-- sub-statement : ∀ {Γ Γ′ Θ Θ′} → Subst Γ Θ Γ′ Θ′ → Γ′ ↦ Θ′ → Γ ↦ Θ

-- sub-term s (` x) = sub-var s x
-- sub-term s `⟨ M , N ⟩ = `⟨ sub-term s M , sub-term s N ⟩  
-- sub-term s inl⟨ M ⟩ = inl⟨ sub-term s M ⟩
-- sub-term s inr⟨ M ⟩ = inr⟨ sub-term s M ⟩
-- sub-term s not[ K ] = not[ sub-coterm s K ]
-- sub-term s (μθ S) = μθ (sub-statement {!   !} {!   !})

-- sub-coterm s (` α) = sub-covar s α
-- sub-coterm s fst[ K ] = fst[ (sub-coterm s K) ]
-- sub-coterm s snd[ K ] = snd[ (sub-coterm s K) ]
-- sub-coterm s `[ K , L ] = `[ (sub-coterm s K) , (sub-coterm s L) ]
-- sub-coterm s not⟨ M ⟩ = not⟨ (sub-term s M) ⟩
-- sub-coterm s (μγ S) = {!   !}

-- sub-statement s (M ● K) = (sub-term s M) ● (sub-coterm s K)