module Dual.Semantics where

open import Dual.Syntax
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public

-- ext : ∀ {Γ Γ′} 
--   → (∀ {A} →   Γ ∋ A →     Γ′ ∋ A)
--     ----------------------------------
--   → (∀ {A B} → Γ , B ∋ A → Γ′ , B ∋ A)
-- ext ρ `Z     = `Z 
-- ext ρ (`S x) = `S (ρ x)

-- rename₁ : ∀ {Γ Γ′ Θ Θ′}
--   → (∀ {A} → Γ ∋ A → Γ′ ∋ A)
--   → (∀ {A} → Θ ∋ A → Θ′ ∋ A)
--     ----------------------------------
--   → (∀ {A} → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A)
-- rename₂ : ∀ {Γ Γ′ Θ Θ′}
--   → (∀ {A} → Γ ∋ A → Γ′ ∋ A)
--   → (∀ {A} → Θ ∋ A → Θ′ ∋ A)
--     -------------------------
--   → (∀ {A} → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′)
-- rename₃ : ∀ {Γ Γ′ Θ Θ′}
--   → (∀ {A} → Γ ∋ A → Γ′ ∋ A)
--   → (∀ {A} → Θ ∋ A → Θ′ ∋ A)
--     -----------------------------
--   → (Γ ↦ Θ → Γ′ ↦ Θ′)

-- rename₁ ρ σ (` x) = `(ρ x)
-- rename₁ ρ σ `⟨ M , N ⟩ = `⟨ rename₁ ρ σ M , rename₁ ρ σ N ⟩
-- rename₁ ρ σ inl⟨ M ⟩ = inl⟨ rename₁ ρ σ M ⟩
-- rename₁ ρ σ inr⟨ M ⟩ = inr⟨ rename₁ ρ σ M ⟩
-- rename₁ ρ σ not[ K ] = not[ rename₂ ρ σ K ]
-- rename₁ ρ σ (μθ S) = μθ (rename₃ ρ (ext σ) S)

-- rename₂ ρ σ (` α) = `(σ α)
-- rename₂ ρ σ fst[ K ] = fst[ rename₂ ρ σ K ]
-- rename₂ ρ σ snd[ K ] = snd[ rename₂ ρ σ K ]
-- rename₂ ρ σ `[ K , L ] = `[ rename₂ ρ σ K , rename₂ ρ σ L ]
-- rename₂ ρ σ not⟨ M ⟩ = not⟨ rename₁ ρ σ M ⟩
-- rename₂ ρ σ (μγ S) = μγ (rename₃ (ext ρ) σ S)

-- rename₃ ρ σ (M ● K) = (rename₁ ρ σ M) ● (rename₂ ρ σ K)

-- exts₁ : ∀ {Γ Γ′ Θ} 
--   → (∀ {A}   → Γ ∋ A → Γ′ ⟶ Θ ∣ A)
--     --------------------------------------
--   → (∀ {A B} → Γ , B ∋ A → Γ′ , B ⟶ Θ ∣ A)
-- exts₁ σ `Z = ` `Z
-- exts₁ σ (`S x) = rename₁ `S (λ x → x) (σ x)

-- exts₂ : ∀ {Γ Θ Θ′}
--   → (∀ {A}   → Θ ∋ A → A ∣ Γ ⟶ Θ′)
--     ---------------------------------------
--   → (∀ {A B} → Θ , B ∋ A → A ∣ Γ ⟶ Θ′ , B)
-- exts₂ σ `Z     = ` `Z
-- exts₂ σ (`S α) = rename₂ (λ x → x) `S (σ α)

-- subst₁ : ∀ {Γ Γ′ Θ Θ′}
--   → (∀ {A} → Γ ∋ A → (Context → Context → Type → Set))
--   → (∀ {A} → Θ ∋ A → (Context → Context → Type → Set))
--     ----------------------------------
--   → (∀ {A} → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A)
-- subst₂ : ∀ {Γ Γ′ Θ Θ′}
--   → (∀ {A} → Γ ∋ A → (Context → Context → Type → Set))
--   → (∀ {A} → Θ ∋ A → (Context → Context → Type → Set))
--     ----------------------------------
--   → (∀ {A} → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′)
-- subst₃ : ∀ {Γ Γ′ Θ Θ′}
--   → (∀ {A} → Γ ∋ A → (Context → Context → Set))
--   → (∀ {A} → Θ ∋ A → (Context → Context → Set))
--     --------------------------
--   → Γ ↦ Θ → Γ′ ↦ Θ′

-- subst₁ ρ σ (` x) = {!   !}
-- subst₁ ρ σ `⟨ M , N ⟩ = `⟨ subst₁ ρ σ M , subst₁ ρ σ N ⟩
-- subst₁ ρ σ inl⟨ M ⟩ = inl⟨ subst₁ ρ σ M ⟩
-- subst₁ ρ σ inr⟨ M ⟩ = inr⟨ subst₁ ρ σ M ⟩
-- subst₁ ρ σ not[ K ] = not[ (subst₂ ρ σ K) ]
-- subst₁ ρ σ (μθ S) = μθ (subst₃ {!  exts­ !} {!   !} {!   !})

-- subst₂ ρ σ (` α) = {!   !}
-- subst₂ ρ σ fst[ K ] = fst[ subst₂ ρ σ K ]
-- subst₂ ρ σ snd[ K ] = snd[ subst₂ ρ σ K ]
-- subst₂ ρ σ `[ K , L ] = `[ subst₂ ρ σ K , subst₂ ρ σ L ]
-- subst₂ ρ σ not⟨ M ⟩ = not⟨ {!   !} ⟩
-- subst₂ ρ σ (μγ S) = {!   !}

-- subst₃ ρ σ (M ● K) = (subst₁ {!   !} {!   !} {!   !}) ● {!   !}

data Subst (T : Context → Context → Type → Set): Context → Context → Context → Context → Set where 
  ⨀  : ∀ {Γ Θ} → Subst T Γ Θ ∅ ∅
  _,ᵗ_ : ∀ {Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → T Γ Θ A → Subst T Γ Θ (Γ′ , A) Θ′
  _,ᶜ_ : ∀ {Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → T Γ Θ A → Subst T Γ Θ Γ′ (Θ′ , A)

record SubstKit (T : Context → Context → Type → Set) : Set where
  field
    vr : ∀ {Γ Θ A}     → Γ ∋ A   → T Γ Θ A
    cvr : ∀ {Γ Θ A}    → Θ ∋ A   → T Γ Θ A
    tm-v : ∀ {Γ Θ A}   → T Γ Θ A → Γ ∋ A
    tm-c : ∀ {Γ Θ A}   → T Γ Θ A → Θ ∋ A
    wk-v : ∀ {Γ Θ A B} → T Γ Θ A → T (Γ , B) Θ A 
    wk-c : ∀ {Γ Θ A B} → T Γ Θ A → T Γ (Θ , B) A

record SubstKit+ (T : Context → Context → Type → Set) : Set where
  field
    kit : SubstKit T
    subst : ∀ {Γ Γ′ Θ Θ′ A} → T Γ′ Θ′ A → Subst T Γ Θ Γ′ Θ′ → T Γ Θ A 

weaken-var : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → SubstKit T → Subst T (Γ , A) Θ Γ′ Θ′
weaken-var ⨀ _ = ⨀
weaken-var (s ,ᵗ t) k = weaken-var s k ,ᵗ SubstKit.wk-v k t
weaken-var (s ,ᶜ t) k = weaken-var s k ,ᶜ SubstKit.wk-v k t

weaken-covar : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → SubstKit T → Subst T Γ (Θ , A) Γ′ Θ′
weaken-covar ⨀ _ = ⨀
weaken-covar (s ,ᵗ t) k = weaken-covar s k ,ᵗ SubstKit.wk-c k t
weaken-covar (s ,ᶜ t) k = weaken-covar s k ,ᶜ SubstKit.wk-c k t

ext-var : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → SubstKit T → Subst T (Γ , A) Θ (Γ′ , A) Θ′
ext-var s k = (weaken-var s k) ,ᵗ SubstKit.vr k `Z

ext-covar : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → SubstKit T → Subst T Γ (Θ , A) Γ′ (Θ′ , A)
ext-covar s k = (weaken-covar s k) ,ᶜ SubstKit.cvr k `Z

sub-var : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → Γ′ ∋ A → T Γ Θ A
sub-var (s ,ᵗ t) `Z = t
sub-var (s ,ᵗ t) (`S x) = sub-var s x 
sub-var (s ,ᶜ t) x = sub-var s x

sub-covar : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → Θ′ ∋ A → T Γ Θ A
sub-covar (s ,ᵗ t) α = sub-covar s α
sub-covar (s ,ᶜ t) `Z = t
sub-covar (s ,ᶜ t) (`S x) = sub-covar s x

sub-term : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → Γ′ ⟶ Θ′ ∣ A  → SubstKit T → Γ ⟶ Θ ∣ A
sub-coterm : ∀ {T Γ Γ′ Θ Θ′ A} → Subst T Γ Θ Γ′ Θ′ → A ∣ Γ′ ⟶ Θ′ → SubstKit T → A ∣ Γ ⟶ Θ
sub-statement : ∀ {T Γ Γ′ Θ Θ′} → Subst T Γ Θ Γ′ Θ′ → Γ′ ↦ Θ′ → SubstKit T → Γ ↦ Θ

sub-term s (` x) k = ` SubstKit.tm-v k (sub-var s x)
sub-term s `⟨ M , N ⟩ k = `⟨ sub-term s M k , sub-term s N k ⟩  
sub-term s inl⟨ M ⟩ k = inl⟨ sub-term s M k ⟩
sub-term s inr⟨ M ⟩ k = inr⟨ sub-term s M k ⟩
sub-term s not[ K ] k = not[ sub-coterm s K k ]
sub-term s (μθ S) k = μθ (sub-statement (ext-covar s k) S k)

sub-coterm s (` α) k = ` SubstKit.tm-c k (sub-covar s α)
sub-coterm s fst[ K ] k = fst[ sub-coterm s K k ]
sub-coterm s snd[ K ] k = snd[ sub-coterm s K k ]
sub-coterm s `[ K , L ] k = `[ sub-coterm s K k , sub-coterm s L k ]
sub-coterm s not⟨ M ⟩ k = not⟨ sub-term s M k ⟩
sub-coterm s (μγ S) k = μγ (sub-statement (ext-var s k) S k)

sub-statement s (M ● K) k = (sub-term s M k) ● (sub-coterm s K k)

