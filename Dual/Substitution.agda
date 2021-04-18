module Dual.Substitution where

open import Dual.Syntax
open import Dual.Values
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ ; proj₁ ; proj₂) renaming ( _,_ to ⟨_,_⟩ )

infix  5 ƛⱽ_
infix  5 ƛᴺ_
infixl 7 _·ⱽ_
infixl 7 _·ᴺ_

--Families: context-indexed sets--
Family : Set₁
Family = Context → Set

--Sorted families: sort-indexed families--
Sorted-Family : Set₁
Sorted-Family = Context → Type → Set

--Context map--
_–[_]→_ : Context → Sorted-Family → Context → Set
Γ –[ X ]→ Δ = {A : Type} → Γ ∋ A → X Δ A

--Renaming map--
_↝_ : Context → Context → Set
Γ ↝ Δ = Γ –[ _∋_ ]→ Δ

--Adding a term to a context map--
add : ∀{Γ Δ A}(T : Context → Type → Set) → T Δ A → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ Δ
add T t σ `Z = t
add T t σ (`S v) = σ v

--Removing a term from a renaming map--
ren-skip : ∀ {Γ Γ′ A} → (Γ , A) ↝ Γ′ → Γ ↝ Γ′
ren-skip ρ x = ρ (`S x)

--Removing a term from a context map
sub-skip : ∀ {Γ Γ′ A} T → ((Γ , A) –[ T ]→ Γ′) → ( Γ –[ T ]→ Γ′)
sub-skip T σ x = σ (`S x)

record VarSubstKit (T : Context → Type → Set) : Set where
  field
    vr : ∀ {Γ A} → Γ ∋ A → T Γ A
    wk : ∀ {Γ A B} → T Γ A → T (Γ , B) A

record TermSubstKit (T : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → T Γ Θ A → Γ ⟶ Θ ∣ A
    kit : ∀ {Θ}        → VarSubstKit (λ Γ → T Γ Θ)
    wkΘ : ∀ {Γ Θ A B}   → T Γ Θ A → T Γ (Θ , B) A
  open module K {Θ} = VarSubstKit (kit {Θ}) renaming (wk to wkΓ) public

record CotermSubstKit (C : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → C Γ Θ A → A ∣ Γ ⟶ Θ
    wkΓ : ∀ {Γ Θ A B}   → C Γ Θ A → C (Γ , B) Θ A
    kit : ∀ {Γ}        → VarSubstKit (C Γ)
  open module K {Γ} = VarSubstKit (kit {Γ}) renaming (wk to wkΘ) public


rename-weaken : ∀ {Γ Δ A} → Γ ↝ Δ → Γ ↝ (Δ , A)
rename-weaken ρ x = `S (ρ x)

rename-lift : ∀ {Γ Δ A} → Γ ↝ Δ → (Γ , A) ↝ (Δ , A)
rename-lift ρ `Z = `Z
rename-lift ρ (`S x) = `S (ρ x)


rename-term : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
rename-coterm : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
rename-statement : ∀ {Γ Γ′ Θ Θ′} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′

rename-term ρ ϱ (` x) = ` (ρ x)
rename-term ρ ϱ `⟨ M , N ⟩ = `⟨ (rename-term ρ ϱ M) , rename-term ρ ϱ N ⟩
rename-term ρ ϱ inr⟨ M ⟩ = inr⟨ rename-term ρ ϱ M ⟩
rename-term ρ ϱ inl⟨ M ⟩ = inl⟨ rename-term ρ ϱ M ⟩
rename-term ρ ϱ not[ K ] = not[ rename-coterm ρ ϱ K ]
rename-term ρ ϱ (μθ S) = μθ (rename-statement ρ (rename-lift ϱ) S)

rename-coterm ρ ϱ (` α) = ` (ϱ α)
rename-coterm ρ ϱ fst[ K ] = fst[ rename-coterm ρ ϱ K ]
rename-coterm ρ ϱ snd[ K ] = snd[ rename-coterm ρ ϱ K ]
rename-coterm ρ ϱ `[ K , L ] = `[ rename-coterm ρ ϱ K , rename-coterm ρ ϱ L ]
rename-coterm ρ ϱ not⟨ M ⟩ = not⟨ (rename-term ρ ϱ M) ⟩
rename-coterm ρ ϱ (μγ S) = μγ (rename-statement (rename-lift ρ) ϱ S)

rename-statement ρ ϱ (M ● K) = (rename-term ρ ϱ M) ● (rename-coterm ρ ϱ K) 

-- rename : ∀ {Γ Γ′ Θ Θ′ A} T → Γ ↝ Γ′ → Θ ↝ Θ′ → (T Γ Θ A) → (T Γ Θ A)
-- rename Term ρ ϱ M = ?
-- rename 

VarKit : VarSubstKit _∋_ 
VarKit = record 
  {  vr = λ a → a
  ;  wk = `S
  } 

sub-weaken : ∀ {Γ Δ A T} → VarSubstKit T → Γ –[ T ]→ Δ → Γ –[ T ]→ (Δ , A)
sub-weaken k σ x = VarSubstKit.wk k (σ x)

sub-lift : ∀ {Γ Δ A T} → VarSubstKit T → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ (Δ , A)
sub-lift k σ `Z = VarSubstKit.vr k `Z
sub-lift k σ (`S x) = sub-weaken k σ x

id-var : ∀ {Γ} → Γ ↝ Γ
id-var = λ x → x

id-term : ∀ {Γ Θ} → Γ –[ (λ - → _⟶_∣_ - Θ) ]→  Γ
id-term x = ` x

id-termvalue : ∀ {Γ Θ} → Γ –[ (λ Γ A → TermValue Γ Θ A) ]→ Γ
id-termvalue x = ⟨ (` x) , V-var ⟩

id-coterm : ∀ {Γ Θ} →  Θ –[ (λ - A → A ∣ Γ ⟶ -) ]→ Θ
id-coterm x = ` x

id-cotermvalue : ∀ {Γ Θ} → Θ –[ (λ Θ A → CotermValue Γ Θ A) ]→ Θ
id-cotermvalue x = ⟨ (` x) , CV-covar ⟩

fmap : ∀ {T T′ Γ Γ′} (f : ∀ {Γ A} → T Γ A → T′ Γ A) → Γ –[ T ]→ Γ′ → Γ –[ T′ ]→ Γ′
fmap f σ x = f (σ x)


sub-term : ∀ {T A C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C → Γ –[ (λ - → T - Θ′) ]→ Γ′ → Θ –[ (C Γ′) ]→ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-coterm : ∀ {T A C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C → Γ –[ (λ - → T - Θ′) ]→ Γ′ → Θ –[ (C Γ′) ]→ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-statement : ∀ {T C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C → Γ –[ (λ - → T - Θ′) ]→ Γ′ → Θ –[ (C Γ′) ]→ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′

sub-term k₁ k₂ s t (` x) = TermSubstKit.tm k₁ (s x)
sub-term k₁ k₂ s t `⟨ M , N ⟩ = `⟨ sub-term k₁ k₂ s t M , sub-term k₁ k₂ s t N ⟩
sub-term k₁ k₂ s t inl⟨ M ⟩ = inl⟨ sub-term k₁ k₂ s t M ⟩
sub-term k₁ k₂ s t inr⟨ M ⟩ = inr⟨ sub-term k₁ k₂ s t M ⟩
sub-term k₁ k₂ s t not[ K ] = not[ sub-coterm k₁ k₂ s t K ]
sub-term {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μθ S) = μθ (sub-statement k₁ k₂ (fmap {λ - → T - Θ′} {λ - → T - (Θ′ , A)} (λ x → TermSubstKit.wkΘ k₁ x) s) (sub-lift (CotermSubstKit.kit k₂) t) S)

sub-coterm k₁ k₂ s t (` α) = CotermSubstKit.tm k₂ (t α)
sub-coterm k₁ k₂ s t fst[ K ] = fst[ sub-coterm k₁ k₂ s t K ]
sub-coterm k₁ k₂ s t snd[ K ] = snd[ sub-coterm k₁ k₂ s t K ]
sub-coterm k₁ k₂ s t `[ K , L ] = `[ sub-coterm k₁ k₂ s t K , sub-coterm k₁ k₂ s t L ]
sub-coterm k₁ k₂ s t not⟨ M ⟩ = not⟨ (sub-term k₁ k₂ s t M) ⟩
sub-coterm {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μγ S) = μγ (sub-statement k₁ k₂ (sub-lift (TermSubstKit.kit k₁) s) (fmap {C Γ′} {C (Γ′ , A)} (λ x → CotermSubstKit.wkΓ k₂ x) t) S)

sub-statement k₁ k₂ s t (M ● K) = (sub-term k₁ k₂ s t M) ● (sub-coterm k₁ k₂ s t K)

TK : TermSubstKit _⟶_∣_ 
TK = record 
  {  tm = λ a → a
  ;  wkΘ = rename-term id-var (rename-weaken id-var)
  ;  kit = record { vr = `_ ; wk = rename-term (rename-weaken id-var) id-var }
  }

CK : CotermSubstKit λ Γ Θ A → A ∣ Γ ⟶ Θ
CK = record
  {  tm = λ a → a 
  ;  wkΓ = rename-coterm (rename-weaken id-var) id-var
  ;  kit = record { vr = `_ ; wk = rename-coterm id-var (rename-weaken id-var) }
  }

value-rename : ∀ {Γ Γ′ Θ Θ′ A} {V : Γ ⟶ Θ ∣ A} (ρ : Γ ↝ Γ′) (ϱ : Θ ↝ Θ′) →
  Value V → Value (rename-term ρ ϱ V)
value-rename ρ ϱ V-var = V-var
value-rename ρ ϱ (V-prod v w) = V-prod (value-rename ρ ϱ v) (value-rename ρ ϱ w)
value-rename ρ ϱ (V-inl v) = V-inl (value-rename ρ ϱ v)
value-rename ρ ϱ (V-inr v) = V-inr (value-rename ρ ϱ v)
value-rename ρ ϱ V-not = V-not  

covalue-rename : ∀ {Γ Γ′ Θ Θ′ A} {P : A ∣ Γ ⟶ Θ} (ρ : Γ ↝ Γ′) (ϱ : Θ ↝ Θ′) →
  Covalue P → Covalue (rename-coterm ρ ϱ P)
covalue-rename ρ ϱ CV-covar = CV-covar
covalue-rename ρ ϱ (CV-sum p q) = CV-sum (covalue-rename ρ ϱ p) (covalue-rename ρ ϱ q)
covalue-rename ρ ϱ (CV-fst p) = CV-fst (covalue-rename ρ ϱ p)
covalue-rename ρ ϱ (CV-snd p) = CV-snd (covalue-rename ρ ϱ p)
covalue-rename ρ ϱ CV-not = CV-not

TVK : TermSubstKit TermValue
TVK = record
  { tm = λ x → proj₁ x
  ; wkΘ = λ x → ⟨ (TermSubstKit.wkΘ TK (proj₁ x)) , value-rename id-var (rename-weaken id-var) (proj₂ x) ⟩
  ; kit = record { vr = λ x → ⟨ ` x , V-var ⟩ ; wk = λ x → ⟨ (VarSubstKit.wk (TermSubstKit.kit TK) (proj₁ x)) , value-rename (rename-weaken id-var) id-var (proj₂ x) ⟩ }
  }

CVK : CotermSubstKit CotermValue
CVK = record 
  { tm = λ x → proj₁ x 
  ; wkΓ = λ x → ⟨ (CotermSubstKit.wkΓ CK (proj₁ x)) , covalue-rename (rename-weaken id-var) id-var (proj₂ x) ⟩ 
  ; kit = record { vr = λ x → ⟨ (` x) , CV-covar ⟩ ; wk = λ x → ⟨ (VarSubstKit.wk (CotermSubstKit.kit CK) (proj₁ x)) , (covalue-rename id-var (rename-weaken id-var) (proj₂ x)) ⟩ } 
  }

sub-t-tv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ TermValue Θ′ ]→ Γ′ → Θ –[ Fix₁ Coterm Γ′ ]→ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-t-tv = sub-term TVK CK

sub-t-cv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ Term Θ′ ]→ Γ′ → Θ –[ Fix₁ CotermValue Γ′ ]→ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-t-cv = sub-term TK CVK

sub-c-tv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ TermValue Θ′ ]→ Γ′ → Θ –[ Fix₁ Coterm Γ′ ]→ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-c-tv = sub-coterm TVK CK

sub-c-cv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ Term Θ′ ]→ Γ′ → Θ –[ Fix₁ CotermValue Γ′ ]→ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-c-cv = sub-coterm TK CVK

sub-s-tv : ∀ {Γ Θ Γ′ Θ′} → Γ –[ Fix₂ TermValue Θ′ ]→ Γ′ → Θ –[ Fix₁ Coterm Γ′ ]→ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′
sub-s-tv = sub-statement TVK CK

sub-s-cv : ∀ {Γ Θ Γ′ Θ′} → Γ –[ Fix₂ Term Θ′ ]→ Γ′ → Θ –[ Fix₁ CotermValue Γ′ ]→ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′
sub-s-cv = sub-statement TK CVK

wkΓᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ , B ⟶ Θ ∣ A
wkΓᵗ = TermSubstKit.wkΓ TK

wkΘᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ ⟶ Θ , B ∣ A
wkΘᵗ = TermSubstKit.wkΘ TK

wkΓᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ , B ⟶ Θ
wkΓᶜ = CotermSubstKit.wkΓ CK

wkΘᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ ⟶ Θ , B
wkΘᶜ = CotermSubstKit.wkΘ CK

wkΓⱽ : ∀ {Γ Θ A B} → TermValue Γ Θ A → TermValue (Γ , B) Θ A
wkΓⱽ = TermSubstKit.wkΓ TVK

wkΘⱽ : ∀ {Γ Θ A B} → TermValue Γ Θ A → TermValue Γ (Θ , B) A
wkΘⱽ = TermSubstKit.wkΘ TVK

wkΓᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue (Γ , B) Θ A
wkΓᶜⱽ = CotermSubstKit.wkΓ CVK

wkΘᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue Γ (Θ , B) A
wkΘᶜⱽ = CotermSubstKit.wkΘ CVK

intΓᵗ : ∀ {Γ Θ A B C} → Γ , A , B ⟶ Θ ∣ C → Γ , B , A ⟶ Θ ∣ C
intΓᵗ M = rename-term (add _∋_ (`S `Z) (rename-lift (rename-weaken id-var))) id-var M


ƛⱽ_ : ∀ {Γ Θ A B}
  → Γ , A ⟶ Θ ∣ B
    --------------------------
  → Γ ⟶ Θ ∣ A ⇒ⱽ B 

ƛᴺ_ : ∀ {Γ Θ A B}
  → Γ , A ⟶ Θ ∣ B
    --------------------------
  → Γ ⟶ Θ ∣ A ⇒ᴺ B

_·ⱽ_ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → B ∣ Γ ⟶ Θ
      ---------------
    → A ⇒ⱽ B ∣ Γ ⟶ Θ 

_·ᴺ_ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → B ∣ Γ ⟶ Θ
      ---------------
    → A ⇒ᴺ B ∣ Γ ⟶ Θ 

ƛⱽ N = not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ intΓᵗ (wkΓᵗ N) ⟩ ]) ]) ]

ƛᴺ N = μθ (inl⟨ not[ μγ(inr⟨ wkΘᵗ N ⟩ ● θ 0) ] ⟩ ● θ 0) 

M ·ⱽ N = not⟨ `⟨ M , not[ N ] ⟩ ⟩

M ·ᴺ N = `[ not⟨ M ⟩ , N ]

-- _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
-- (g ∘ f) x  = g (f x)

-- RCS-T : ∀ {Γ Γ′ Γ″ Θ} → (σ : Γ –[ Fix₂ Term Θ ]→ Γ′) (ρ : Γ′ ↝ Γ″) → Γ –[ Fix₂ Term Θ ]→ Γ″
-- RCS-T σ ρ x = rename-term ρ id-var (σ x)

-- RCS-C : ∀ {Θ Θ′ Θ″ Γ} → (σ : Θ –[ Fix₁ Coterm Γ ]→ Θ′) (ρ : Θ′ ↝ Θ″) → Θ –[ Fix₁ Coterm Γ ]→ Θ″
-- RCS-C σ ρ x = rename-coterm id-var ρ (σ x)

-- sub-ren-term : ∀ {T C Γ Γ′ Γ″ Θ Θ′ Θ″ A} (tk : TermSubstKit T) (ck : CotermSubstKit C) (M : Γ ⟶ Θ ∣ A) (s : Γ′ –[ Fix₂ T Θ″ ]→ Γ″) (t : Θ′ –[ Fix₁ C Γ″ ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-term tk ck s t (rename-term u v M) ≡ sub-term tk ck (s ∘ u) (t ∘ v) M

-- sub-ren-coterm : ∀ {T C Γ Γ′ Γ″ Θ Θ′ Θ″ A} (tk : TermSubstKit T) (ck : CotermSubstKit C) (K : A ∣ Γ ⟶ Θ) (s : Γ′ –[ Fix₂ T Θ″ ]→ Γ″) (t : Θ′ –[ Fix₁ C Γ″ ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-coterm tk ck s t (rename-coterm u v K) ≡ sub-coterm tk ck (s ∘ u) (t ∘ v) K

-- sub-ren-statement : ∀ {T C Γ Γ′ Γ″ Θ Θ′ Θ″} (tk : TermSubstKit T) (ck : CotermSubstKit C) (S : Γ ↦ Θ) (s : Γ′ –[ Fix₂ T Θ″ ]→ Γ″) (t : Θ′ –[ Fix₁ C Γ″ ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-statement tk ck s t (rename-statement u v S) ≡ sub-statement tk ck (s ∘ u) (t ∘ v) S

-- sub-ren-term tk ck (` x) s t u v = refl
-- sub-ren-term tk ck `⟨ M , N ⟩ s t u v = cong₂ `⟨_,_⟩ (sub-ren-term tk ck M s t u v) (sub-ren-term tk ck N s t u v)
-- sub-ren-term tk ck inl⟨ M ⟩ s t u v = cong inl⟨_⟩ (sub-ren-term tk ck M s t u v)
-- sub-ren-term tk ck inr⟨ M ⟩ s t u v = cong inr⟨_⟩ (sub-ren-term tk ck M s t u v)
-- sub-ren-term tk ck not[ K ] s t u v = cong not[_](sub-ren-coterm tk ck K s t u v)
-- sub-ren-term {T} {C} {Γ} {Γ′} {Γ″} {Θ} {Θ′} {Θ″} {A} tk ck (μθ S) s t u v = cong μθ 
--   (begin 
--     sub-statement tk ck 
--       (fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)}(TermSubstKit.wkΘ tk) s)
--       (sub-lift (CotermSubstKit.kit ck) t)
--       (rename-statement u (rename-lift v) S)
--   ≡⟨ sub-ren-statement tk ck S (fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)}(TermSubstKit.wkΘ tk) s) (sub-lift (CotermSubstKit.kit ck) t) u (rename-lift v) ⟩
--     sub-statement tk ck ((fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)} (TermSubstKit.wkΘ tk) s) ∘ u)
--       ((sub-lift (CotermSubstKit.kit ck) t) ∘ rename-lift v) S
--   ≡⟨ {!   !} ⟩
--     (sub-statement tk ck (fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)} (TermSubstKit.wkΘ tk) (s ∘ u))
--       (sub-lift (CotermSubstKit.kit ck) (t ∘ v)) S) 
--   ∎)

-- sub-ren-coterm tk ck (` α) s t u v = refl
-- sub-ren-coterm tk ck fst[ K ] s t u v = cong fst[_] (sub-ren-coterm tk ck K s t u v)
-- sub-ren-coterm tk ck snd[ K ] s t u v = cong snd[_] (sub-ren-coterm tk ck K s t u v)
-- sub-ren-coterm tk ck `[ K , L ] s t u v = cong₂ `[_,_] (sub-ren-coterm tk ck K s t u v) (sub-ren-coterm tk ck L s t u v)
-- sub-ren-coterm tk ck not⟨ M ⟩ s t u v = cong not⟨_⟩ (sub-ren-term tk ck M s t u v)
-- sub-ren-coterm {T} {C} {Γ} {Γ′} {Γ″} {Θ} {Θ′} {Θ″} {A} tk ck (μγ S) s t u v = cong μγ 
--   (trans 
--     (sub-ren-statement tk ck S (sub-lift (TermSubstKit.kit tk) s) (fmap {Fix₁ C Γ″} {Fix₁ C (Γ″ , A)} (CotermSubstKit.wkΓ ck) t) (rename-lift u) v) 
--     {!   !})

-- sub-ren-statement tk ck (M ● K) s t u v = cong₂ _●_ (sub-ren-term tk ck M s t u v) (sub-ren-coterm tk ck K s t u v)

-- ren-sub-term : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (M : Γ ⟶ Θ ∣ A) (s : Γ –[ Fix₂ Term Θ′ ]→ Γ′) (t : Θ –[ Fix₁ Coterm Γ′ ]→ Θ′) (u : Γ′ ↝ Γ″) (v : Θ′ ↝ Θ″)
--   → rename-term u v (sub-term TK CK s t M) ≡ sub-term TK CK (RCS-T (fmap (rename-term id-var v) s) u) (RCS-C (fmap (rename-coterm u id-var) t) v) M

-- ren-sub-coterm : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (K : A ∣ Γ ⟶ Θ) (s : Γ –[ Fix₂ Term Θ′ ]→ Γ′) (t : Θ –[ Fix₁ Coterm Γ′ ]→ Θ′) (u : Γ′ ↝ Γ″) (v : Θ′ ↝ Θ″)
--   → rename-coterm u v (sub-coterm TK CK s t K) ≡ sub-coterm TK CK (RCS-T (fmap (rename-term id-var v) s) u) (RCS-C (fmap (rename-coterm u id-var) t) v) K

-- ren-sub-statement : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″} (S : Γ ↦ Θ) (s : Γ –[ Fix₂ Term Θ′ ]→ Γ′) (t : Θ –[ Fix₁ Coterm Γ′ ]→ Θ′) (u : Γ′ ↝ Γ″) (v : Θ′ ↝ Θ″)
--   → rename-statement u v (sub-statement TK CK s t S) ≡ sub-statement TK CK (RCS-T (fmap (rename-term id-var v) s) u) (RCS-C (fmap (rename-coterm u id-var) t) v) S

-- ren-sub-term (` x) s t u v = {!   !}
-- ren-sub-term `⟨ M , N ⟩ s t u v = cong₂ `⟨_,_⟩ (ren-sub-term M s t u v) (ren-sub-term N s t u v)
-- ren-sub-term inl⟨ M ⟩ s t u v = {!   !}
-- ren-sub-term inr⟨ M ⟩ s t u v = {!   !}
-- ren-sub-term not[ K ] s t u v = {!   !}
-- ren-sub-term (μθ S) s t u v = cong μθ (
--   begin 
--     rename-statement u (rename-lift v)
--       (sub-statement TK CK
--        (λ x → rename-term (λ x₁ → x₁) (λ x₁ → `S x₁) (s x))
--        (sub-lift
--         (record { vr = `_ ; wk = rename-coterm (λ x → x) (λ x → `S x) }) t)
--        S)
--   ≡⟨ ren-sub-statement S (fmap (rename-term id-var (rename-weaken id-var)) s) (sub-lift (CotermSubstKit.kit CK) t) u (rename-lift v) ⟩
--     {!   !})