module Dual.Semantics where

open import Dual.Syntax
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public

infix 2 _ˢ⟶ⱽ_
infix 2 _ᶜ⟶ⱽ_
infix 2 _ᵗ⟶ⱽ_

infix 2 _ˢ⟶ᴺ_
infix 2 _ᶜ⟶ᴺ_
infix 2 _ᵗ⟶ᴺ_

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

rename-var : ∀ {Γ Γ′ A} → Subst _∋_ Γ Γ′ → Γ′ ∋ A → Γ ∋ A
rename-var (s , t) `Z = t
rename-var (s , t) (`S x) = rename-var s x

rename-term : ∀ {Γ Γ′ Θ Θ′ A} → VarSubstKit _∋_ → Subst _∋_ Γ Γ′ → Subst _∋_ Θ Θ′ → Γ′ ⟶ Θ′ ∣ A → Γ ⟶ Θ ∣ A
rename-coterm : ∀ {Γ Γ′ Θ Θ′ A} → VarSubstKit _∋_ → Subst _∋_ Γ Γ′ → Subst _∋_ Θ Θ′ → A ∣ Γ′ ⟶ Θ′ → A ∣ Γ ⟶ Θ
rename-statement : ∀ {Γ Γ′ Θ Θ′} → VarSubstKit _∋_ → Subst _∋_ Γ Γ′ → Subst _∋_ Θ Θ′ → Γ′ ↦ Θ′ → Γ ↦ Θ

rename-term k s t (` x) = ` (rename-var s x)
rename-term k s t `⟨ M , N ⟩ = `⟨ (rename-term k s t M) , (rename-term k s t N) ⟩
rename-term k s t inl⟨ M ⟩ = inl⟨ rename-term k s t M ⟩
rename-term k s t inr⟨ M ⟩ = inr⟨ rename-term k s t M ⟩
rename-term k s t not[ K ] = not[ rename-coterm k s t K ]
rename-term k s t (μθ S) = μθ (rename-statement k s (ext k t) S)

rename-coterm k s t (` α) = ` (rename-var t α)
rename-coterm k s t fst[ K ] = fst[ rename-coterm k s t K ]
rename-coterm k s t snd[ K ] = snd[ rename-coterm k s t K ]
rename-coterm k s t `[ K , L ] = `[ rename-coterm k s t K , rename-coterm k s t L ]
rename-coterm k s t not⟨ M ⟩ = not⟨ (rename-term k s t M) ⟩
rename-coterm k s t (μγ S) = μγ (rename-statement k (ext k s) t S)

rename-statement k s t (M ● K) = (rename-term k s t M) ● (rename-coterm k s t K)  

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
id-term {Γ , A} = ext (record { vr = `_ ; wk = rename-term VarKit (weaken VarKit id-var) id-var }) id-term 

id-coterm : ∀ {Γ Θ} → Subst (λ - A → A ∣ Γ ⟶ -) Θ Θ
id-coterm {_}{∅} = ⨀
id-coterm {_}{Θ , B} = ext (record { vr = `_ ; wk = rename-coterm VarKit id-var (weaken VarKit id-var) }) id-coterm

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
  ;  wk = rename-term VarKit id-var (weaken VarKit id-var)
  ;  kit = record { vr = `_ ; wk = rename-term VarKit (weaken VarKit id-var) id-var }
  }

CotermKit : CotermSubstKit λ Γ Θ A → A ∣ Γ ⟶ Θ
CotermKit = record
  {  tm = λ a → a 
  ;  wk = rename-coterm VarKit (weaken VarKit id-var) id-var
  ;  kit = record { vr = `_ ; wk = rename-coterm VarKit id-var (weaken VarKit id-var) }
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


data _ˢ⟶ⱽ_ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ) → Set where

  β×₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ}
    → Value V → Value W
      ------------------------------
    → `⟨ V , W ⟩ ● fst[ K ] ˢ⟶ⱽ V ● K

  β×₂ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {L : B ∣ Γ ⟶ Θ}
    → Value V → Value W
      ------------------------------
    → `⟨ V , W ⟩ ● snd[ L ] ˢ⟶ⱽ W ● L

  β+₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Value V
      ------------------------------
    → inl⟨ V ⟩ ● `[ K , L ] ˢ⟶ⱽ V ● K

  β+₂ : ∀ {Γ Θ A B} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Value W
      ------------------------------
    → inr⟨ W ⟩ ● `[ K , L ] ˢ⟶ⱽ W ● L

  β¬ : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ}
      -----------------------------
    → not[ K ] ● not⟨ M ⟩ ˢ⟶ⱽ M ● K

  βL : ∀ {Γ Θ A} {V : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ}
    → Value V
      ------------------------------
    → V ● (μγ S) ˢ⟶ⱽ S ⟨ V /⟩ˢ

  βR : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} {S : Γ ↦ Θ , A}
      ------------------------
    → (μθ S) ● K ˢ⟶ⱽ S [ K /]ˢ

data _ᶜ⟶ⱽ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ⱽ μγ ((γ 0) ● rename-coterm VarKit (weaken VarKit id-var) id-var K)

data _ᵗ⟶ⱽ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ⱽ μθ (rename-term VarKit id-var (weaken VarKit id-var) M ● (θ 0))


data _ˢ⟶ᴺ_ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ) → Set where
  
  β×₁ : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B} {P : A ∣ Γ ⟶ Θ}
    → Covalue P
      -------------------------------
    → `⟨ M , N ⟩ ● fst[ P ] ˢ⟶ᴺ M ● P

  β×₂ : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B} {Q : B ∣ Γ ⟶ Θ}
    → Covalue Q
      --------------------------------
    → `⟨ M , N ⟩ ● snd[ Q ] ˢ⟶ᴺ N ● Q

  β+₁ : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {P : A ∣ Γ ⟶ Θ} {Q : B ∣ Γ ⟶ Θ}
    → Covalue P → Covalue Q
      --------------------------------
    → inl⟨ M ⟩ ● `[ P , Q ] ˢ⟶ᴺ M ● P

  β+₂ : ∀ {Γ Θ A B} {N : Γ ⟶ Θ ∣ B} {P : A ∣ Γ ⟶ Θ} {Q : B ∣ Γ ⟶ Θ}
    → Covalue P → Covalue Q
      --------------------------------
    → inr⟨ N ⟩ ● `[ P , Q ] ˢ⟶ᴺ N ● Q

  β¬ : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ}
      -----------------------------
    → not[ K ] ● not⟨ M ⟩ ˢ⟶ᴺ M ● K 
  
  βL : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ}
      ------------------------
    → M ● (μγ S) ˢ⟶ᴺ S ⟨ M /⟩ˢ 

  βR : ∀ {Γ Θ A} {S : Γ ↦ Θ , A} {P : A ∣ Γ ⟶ Θ}
    → Covalue P
      -------------------------
    → (μθ S) ● P ˢ⟶ᴺ S [ P /]ˢ

data _ᶜ⟶ᴺ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ᴺ μγ ((γ 0) ● rename-coterm VarKit (weaken VarKit id-var) id-var K)

data _ᵗ⟶ᴺ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ᴺ μθ (rename-term VarKit id-var (weaken VarKit id-var) M ● (θ 0))

  