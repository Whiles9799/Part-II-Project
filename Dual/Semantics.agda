module Dual.Semantics where

open import Dual.Syntax
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public


postulate
  γexchange-statement : ∀ {Γ Θ A B} → Γ , B , A ↦ Θ → Γ , A , B ↦ Θ
  θexchange-statement : ∀ {Γ Θ A B} → Γ ↦ Θ , B , A → Γ ↦ Θ , A , B

γweaken-term : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ , B ⟶ Θ ∣ A
γweaken-coterm : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ , B ⟶ Θ
γweaken-statement : ∀ {Γ Θ B} → Γ ↦ Θ → Γ , B ↦ Θ

γweaken-term (` x) = ` `S x
γweaken-term `⟨ M , M₁ ⟩ = `⟨ γweaken-term M , γweaken-term M₁ ⟩
γweaken-term inl⟨ M ⟩ = inl⟨ γweaken-term M ⟩
γweaken-term inr⟨ M ⟩ = inr⟨ γweaken-term M ⟩
γweaken-term not[ K ] = not[ γweaken-coterm K ]
γweaken-term (μθ S) = μθ (γweaken-statement S)

γweaken-coterm (` α) = ` α
γweaken-coterm fst[ K ] = fst[ γweaken-coterm K ]
γweaken-coterm snd[ K ] = snd[ γweaken-coterm K ]
γweaken-coterm `[ K , L ] = `[ γweaken-coterm K , γweaken-coterm L ]
γweaken-coterm not⟨ M ⟩ = not⟨ (γweaken-term M) ⟩
γweaken-coterm (μγ S) = μγ (γexchange-statement (γweaken-statement S))

γweaken-statement (M ● K) = (γweaken-term M) ● (γweaken-coterm K)


θweaken-term : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ ⟶ Θ , B ∣ A
θweaken-coterm : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ ⟶ Θ , B
θweaken-statement : ∀ {Γ Θ B} → Γ ↦ Θ → Γ ↦ Θ , B

θweaken-term (` x) = ` x
θweaken-term `⟨ M , M₁ ⟩ = `⟨ θweaken-term M , θweaken-term M₁ ⟩
θweaken-term inl⟨ M ⟩ = inl⟨ θweaken-term M ⟩
θweaken-term inr⟨ M ⟩ = inr⟨ θweaken-term M ⟩
θweaken-term not[ K ] = not[ θweaken-coterm K ]
θweaken-term (μθ S) = μθ (θexchange-statement (θweaken-statement S))

θweaken-coterm (` α) = ` (`S α)
θweaken-coterm fst[ K ] = fst[ θweaken-coterm K ]
θweaken-coterm snd[ K ] = snd[ θweaken-coterm K ]
θweaken-coterm `[ K , L ] = `[ θweaken-coterm K , θweaken-coterm L ]
θweaken-coterm not⟨ M ⟩ = not⟨ (θweaken-term M) ⟩
θweaken-coterm (μγ S) = μγ (θweaken-statement S)

θweaken-statement (M ● K) = (θweaken-term M) ● (θweaken-coterm K)

infix 2 _⟶ⱽ_

data Value : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A → Set 
data Covalue : ∀ {Γ Θ A} → A ∣ Γ ⟶ Θ → Set

data Value where

  V-var : ∀ {Γ A} {x : Γ ∋ A}
      ---------
    → Value (` x)

  V-prod : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B}
    → Value M
    → Value N
      ---------------
    → Value `⟨ M , N ⟩

  V-inl : ∀ {Γ Θ A B} {M ∶ Γ ⟶ Θ ∣ A `× B}
    → Value M
      -------------
    → Value inl⟨ M ⟩

  V-inr : ∀ {Γ Θ A B} {M ∶ Γ ⟶ Θ ∣ A `× B}
    → Value M
      -------------
    → Value inr⟨ M ⟩

  V-not : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ}
      --------------
    → Value not[ K ]


data Covalue where
  
  CV-covar : ∀ {Θ A} {α : Θ ∋ A}
      -------
    → Covalue(` α)

  CV-sum : ∀ {Γ Θ A B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Covalue K
    → Covalue L
      ------------------
    → Covalue `[ K , L ]

  CV-fst : ∀ {Γ Θ A B} {K ∶ A `+ B ∣ Γ ⟶ Θ}
    → Covalue K
      ----------------
    → Covalue fst[ K ]

  CV-snd : ∀ {Γ Θ A B} {K ∶ A `+ B ∣ Γ ⟶ Θ}
    → Covalue K
      ----------------
    → Covalue snd[ K ]

  CV-not : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      --------------
    → Covalue not⟨ M ⟩

data Subst (T : Context → Type → Set): Context → Context → Set where
  ⨀  : ∀ {Γ} → Subst T Γ ∅
  _,_ : ∀ {Γ Γ′ A} → Subst T Γ Γ′ → T Γ A → Subst T Γ (Γ′ , A)

record VarSubstKit (T : Context → Type → Set) : Set where
  field 
    vr : ∀ {Γ A} → Γ ∋ A → T Γ A
    wk : ∀ {Γ A B} → T Γ A → T (Γ , B) A

record TermSubstKit (T : Context → Context → Type → Set) : Set where
  field 
    tm : ∀ {Γ Θ A}     → T Γ Θ A → Γ ⟶ Θ ∣ A
    kit : ∀ {Θ}        → VarSubstKit (λ Γ → T Γ Θ)
    wk : ∀ {Γ Θ A B}   → T Γ Θ A → T Γ (Θ , B) A

record CotermSubstKit (C : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → C Γ Θ A → A ∣ Γ ⟶ Θ
    wk : ∀ {Γ Θ A B}   → C Γ Θ A → C (Γ , B) Θ A
    kit : ∀ {Γ}        → VarSubstKit (C Γ)


weaken : ∀ {T Γ Γ′ A} → VarSubstKit T → Subst T Γ Γ′ → Subst T (Γ , A) Γ′
weaken k ⨀ = ⨀
weaken k (s , t) = (weaken k s) , VarSubstKit.wk k t

ext : ∀ {T Γ Γ′ A} → VarSubstKit T → Subst T Γ Γ′ → Subst T (Γ , A) (Γ′ , A)
ext k s = (weaken k s) , (VarSubstKit.vr k `Z)

sub-var : ∀ {T Γ Γ′ A} → Subst T Γ Γ′ → Γ′ ∋ A → T Γ A
sub-var ⨀ ()
sub-var (s , t) `Z = t
sub-var (s , t) (`S x) = sub-var s x

VarKit : VarSubstKit _∋_ 
VarKit = record 
  {  vr = λ a → a
  ;  wk = `S
  } 

id-var : ∀ {Γ} → Subst _∋_ Γ Γ
id-var {∅} = ⨀
id-var {Γ , A} = ext VarKit id-var

id-term : ∀ {Γ Θ} → Subst (λ - → _⟶_∣_ - Θ) Γ Γ
id-term {∅} = ⨀
id-term {Γ , A} = ext (record { vr = `_ ; wk = γweaken-term }) id-term 

id-coterm : ∀ {Γ Θ} → Subst (λ - A → A ∣ Γ ⟶ -) Θ Θ
id-coterm {_}{∅} = ⨀
id-coterm {_}{Θ , B} = ext (record { vr = `_ ; wk = θweaken-coterm }) id-coterm

lift : ∀ {T T′ Γ Γ′} (f : ∀ {Γ A} → T Γ A → T′ Γ A) → Subst T Γ Γ′ → Subst T′ Γ Γ′
lift f ⨀ = ⨀
lift f (s , x) = lift f s , f x

sub-term : ∀ {A T C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C → Subst (λ - → T - Θ) Γ Γ′ → Subst (C Γ) Θ Θ′ → Γ′ ⟶ Θ′ ∣ A → Γ ⟶ Θ ∣ A
sub-coterm : ∀ {A T C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C → Subst (λ - → T - Θ) Γ Γ′ → Subst (C Γ) Θ Θ′ → A ∣ Γ′ ⟶ Θ′ → A ∣ Γ ⟶ Θ
sub-statement : ∀ {T C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C → Subst (λ - → T - Θ) Γ Γ′ → Subst (C Γ) Θ Θ′ → Γ′ ↦ Θ′ → Γ ↦ Θ

sub-term k₁ k₂ s t (` x) = TermSubstKit.tm k₁ (sub-var s x)
sub-term k₁ k₂ s t `⟨ M , N ⟩ = `⟨ sub-term k₁ k₂ s t M , sub-term k₁ k₂ s t N ⟩
sub-term k₁ k₂ s t inl⟨ M ⟩ = inl⟨ sub-term k₁ k₂ s t M ⟩
sub-term k₁ k₂ s t inr⟨ M ⟩ = inr⟨ sub-term k₁ k₂ s t M ⟩
sub-term k₁ k₂ s t not[ K ] = not[ sub-coterm k₁ k₂ s t K ]
sub-term k₁ k₂ s t (μθ S) = μθ (sub-statement k₁ k₂ (lift (λ x → TermSubstKit.wk k₁ x) s) (ext (CotermSubstKit.kit k₂) t) S)

sub-coterm k₁ k₂ s t (` α) = CotermSubstKit.tm k₂ (sub-var t α)
sub-coterm k₁ k₂ s t fst[ K ] = fst[ sub-coterm k₁ k₂ s t K ]
sub-coterm k₁ k₂ s t snd[ K ] = snd[ sub-coterm k₁ k₂ s t K ]
sub-coterm k₁ k₂ s t `[ K , L ] = `[ sub-coterm k₁ k₂ s t K , sub-coterm k₁ k₂ s t L ]
sub-coterm k₁ k₂ s t not⟨ M ⟩ = not⟨ (sub-term k₁ k₂ s t M) ⟩
sub-coterm k₁ k₂ s t (μγ S) = μγ (sub-statement k₁ k₂ (ext (TermSubstKit.kit k₁) s) (lift (λ x → CotermSubstKit.wk k₂ x) t) S)

sub-statement k₁ k₂ s t (M ● K) = (sub-term k₁ k₂ s t M) ● (sub-coterm k₁ k₂ s t K)


TermKit : TermSubstKit _⟶_∣_ 
TermKit = record 
  {  tm = λ a → a
  ;  wk = θweaken-term
  ;  kit = record { vr = `_ ; wk = γweaken-term }
  }

CotermKit : CotermSubstKit λ Γ Θ A → A ∣ Γ ⟶ Θ
CotermKit = record
  {  tm = λ a → a 
  ;  wk = γweaken-coterm
  ;  kit = record { vr = `_ ; wk = θweaken-coterm }
  }


_⟨_/⟩ᵗ : ∀ {Γ Θ A B} 
  → Γ , A ⟶ Θ ∣ B
  → Γ ⟶ Θ ∣ A
    --------------
  → Γ ⟶ Θ ∣ B   

_⟨_/⟩ᶜ : ∀ {Γ Θ A B}
  → B ∣ Γ , A ⟶ Θ
  → Γ ⟶ Θ ∣ A
    --------------
  → B ∣ Γ ⟶ Θ

_⟨_/⟩ˢ : ∀ {Γ Θ A}
  → Γ , A ↦ Θ
  → Γ ⟶ Θ ∣ A
    ----------
  → Γ ↦ Θ

_[_/]ᵗ : ∀ {Γ Θ A B}
  → Γ ⟶ Θ , A ∣ B
  → A ∣ Γ ⟶ Θ
    --------------
  → Γ ⟶ Θ ∣ B

_[_/]ᶜ : ∀ {Γ Θ A B}
  → B ∣ Γ ⟶ Θ , A
  → A ∣ Γ ⟶ Θ
    --------------
  → B ∣ Γ ⟶ Θ

_[_/]ˢ : ∀ {Γ Θ A}
  → Γ ↦ Θ , A
  → A ∣ Γ ⟶ Θ
    ----------
  → Γ ↦ Θ

N ⟨ M /⟩ᵗ = sub-term TermKit CotermKit (id-term , M) id-coterm N

L ⟨ M /⟩ᶜ = sub-coterm TermKit CotermKit (id-term , M) id-coterm L

S ⟨ M /⟩ˢ = sub-statement TermKit CotermKit (id-term , M) id-coterm S

N [ K /]ᵗ = sub-term TermKit CotermKit id-term (id-coterm , K) N

L [ K /]ᶜ = sub-coterm TermKit CotermKit id-term (id-coterm , K) L

S [ K /]ˢ = sub-statement TermKit CotermKit id-term (id-coterm , K) S


data _⟶ⱽ_ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ) → Set where

  β×₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ}
    → Value V → Value W
      ------------------------------
    → `⟨ V , W ⟩ ● fst[ K ] ⟶ⱽ V ● K

  β×₂ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {L : B ∣ Γ ⟶ Θ}
    → Value V → Value W
      ------------------------------
    → `⟨ V , W ⟩ ● snd[ L ] ⟶ⱽ W ● L

  β+₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Value V
      ------------------------------
    → inl⟨ V ⟩ ● `[ K , L ] ⟶ⱽ V ● K

  β+₂ : ∀ {Γ Θ A B} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Value W
      ------------------------------
    → inr⟨ W ⟩ ● `[ K , L ] ⟶ⱽ W ● L

  β¬ : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ}
      -----------------------------
    → not[ K ] ● not⟨ M ⟩ ⟶ⱽ M ● K

  -- βL : ∀ {Γ Θ A} {V : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ} {s : Subst _↦_+_ Γ Θ Γ Θ}
  --   → Value V
  --     ------------------------------
  --   → V ● (μγ S) ⟶ⱽ ((sub-statement+ {!   !} ((S +)) {!   !}) -)
