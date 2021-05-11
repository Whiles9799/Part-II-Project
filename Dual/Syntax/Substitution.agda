module Dual.Syntax.Substitution where

open import Dual.Syntax.Core
open import Dual.Syntax.Values
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ ; proj₁ ; proj₂) renaming ( _,_ to ⟨_,_⟩ )

--Families: context-indexed sets--
Family : Set₁
Family = Context → Set

--Sorted families: sort-indexed families--
Sorted-Family : Set₁
Sorted-Family = Context → Type → Set

--Context map--
_–[_]→_ : Context → Sorted-Family → Context → Set
Γ –[ T ]→ Δ = {A : Type} → Γ ∋ A → T Δ A

--Renaming map--
_↝_ : Context → Context → Set
Γ ↝ Δ = Γ –[ _∋_ ]→ Δ

--Adding a T to a context map--
add : ∀{Γ Δ A}(T : Context → Type → Set) → T Δ A → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ Δ
add T t σ `Z = t
add T t σ (`S v) = σ v

--Removing a T from a renaming map--
ren-skip : ∀ {Γ Γ′ A} → (Γ , A) ↝ Γ′ → Γ ↝ Γ′
ren-skip ρ x = ρ (`S x)

--Removing a T from a context map
sub-skip : ∀ {Γ Γ′ A} T → ((Γ , A) –[ T ]→ Γ′) → ( Γ –[ T ]→ Γ′)
sub-skip T σ x = σ (`S x)

record VarKit (T : Context → Type → Set) : Set where
  field
    vr : ∀ {Γ A} → Γ ∋ A → T Γ A
    wk : ∀ {Γ A B} → T Γ A → T (Γ , B) A

record TermKit (T : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → T Γ Θ A → Γ ⟶ Θ ∣ A
    kit : ∀ {Θ}        → VarKit (λ Γ → T Γ Θ)
    wkΘ : ∀ {Γ Θ A B}   → T Γ Θ A → T Γ (Θ , B) A
  open module K {Θ} = VarKit (kit {Θ}) renaming (wk to wkΓ) public

record CotermKit (C : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → C Γ Θ A → A ∣ Γ ⟶ Θ
    wkΓ : ∀ {Γ Θ A B}   → C Γ Θ A → C (Γ , B) Θ A
    kit : ∀ {Γ}        → VarKit (C Γ)
  open module K {Γ} = VarKit (kit {Γ}) renaming (wk to wkΘ) public


ren-weaken : ∀ {Γ Δ A} → Γ ↝ Δ → Γ ↝ (Δ , A)
ren-weaken ρ x = `S (ρ x)

ren-lift : ∀ {Γ Δ A} → Γ ↝ Δ → (Γ , A) ↝ (Δ , A)
ren-lift ρ `Z = `Z
ren-lift ρ (`S x) = `S (ρ x)


ren-T : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
ren-C : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
ren-S : ∀ {Γ Γ′ Θ Θ′} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′

ren-T ρ ϱ (` x) = ` (ρ x)
ren-T ρ ϱ `⟨ M , N ⟩ = `⟨ (ren-T ρ ϱ M) , ren-T ρ ϱ N ⟩
ren-T ρ ϱ inr⟨ M ⟩ = inr⟨ ren-T ρ ϱ M ⟩
ren-T ρ ϱ inl⟨ M ⟩ = inl⟨ ren-T ρ ϱ M ⟩
ren-T ρ ϱ not[ K ] = not[ ren-C ρ ϱ K ]
ren-T ρ ϱ (μθ S) = μθ (ren-S ρ (ren-lift ϱ) S)

ren-C ρ ϱ (` α) = ` (ϱ α)
ren-C ρ ϱ fst[ K ] = fst[ ren-C ρ ϱ K ]
ren-C ρ ϱ snd[ K ] = snd[ ren-C ρ ϱ K ]
ren-C ρ ϱ `[ K , L ] = `[ ren-C ρ ϱ K , ren-C ρ ϱ L ]
ren-C ρ ϱ not⟨ M ⟩ = not⟨ (ren-T ρ ϱ M) ⟩
ren-C ρ ϱ (μγ S) = μγ (ren-S (ren-lift ρ) ϱ S)

ren-S ρ ϱ (M ● K) = (ren-T ρ ϱ M) ● (ren-C ρ ϱ K) 

VK : VarKit _∋_ 
VK = record 
  {  vr = λ a → a
  ;  wk = `S
  } 

sub-weaken : ∀ {Γ Δ A T} → VarKit T → Γ –[ T ]→ Δ → Γ –[ T ]→ (Δ , A)
sub-weaken k σ x = VarKit.wk k (σ x)

sub-lift : ∀ {Γ Δ A T} → VarKit T → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ (Δ , A)
sub-lift k σ `Z = VarKit.vr k `Z
sub-lift k σ (`S x) = sub-weaken k σ x

id-var : ∀ {Γ} → Γ ↝ Γ
id-var = λ x → x

id-T : ∀ {Γ Θ} → Γ –[ (λ - → _⟶_∣_ - Θ) ]→  Γ
id-T x = ` x

id-TV : ∀ {Γ Θ} → Γ –[ (Fix₂ TermValue Θ) ]→ Γ
id-TV x = ⟨ (` x) , V-var ⟩

id-C : ∀ {Γ Θ} →  Θ –[ (λ - A → A ∣ Γ ⟶ -) ]→ Θ
id-C x = ` x

id-CV : ∀ {Γ Θ} → Θ –[ (Fix₁ CotermValue Γ) ]→ Θ
id-CV x = ⟨ (` x) , CV-covar ⟩

fmap : ∀ {T T′ Γ Γ′} (f : ∀ {Γ A} → T Γ A → T′ Γ A) → Γ –[ T ]→ Γ′ → Γ –[ T′ ]→ Γ′
fmap f σ x = f (σ x)

sub-T : ∀ {T A C Γ Θ Γ′ Θ′} → TermKit T → CotermKit C → Γ –[ (λ - → T - Θ′) ]→ Γ′ → Θ –[ (C Γ′) ]→ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-C : ∀ {T A C Γ Θ Γ′ Θ′} → TermKit T → CotermKit C → Γ –[ (λ - → T - Θ′) ]→ Γ′ → Θ –[ (C Γ′) ]→ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-S : ∀ {T C Γ Θ Γ′ Θ′} → TermKit T → CotermKit C → Γ –[ (λ - → T - Θ′) ]→ Γ′ → Θ –[ (C Γ′) ]→ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′

sub-T k₁ k₂ s t (` x) = TermKit.tm k₁ (s x)
sub-T k₁ k₂ s t `⟨ M , N ⟩ = `⟨ sub-T k₁ k₂ s t M , sub-T k₁ k₂ s t N ⟩
sub-T k₁ k₂ s t inl⟨ M ⟩ = inl⟨ sub-T k₁ k₂ s t M ⟩
sub-T k₁ k₂ s t inr⟨ M ⟩ = inr⟨ sub-T k₁ k₂ s t M ⟩
sub-T k₁ k₂ s t not[ K ] = not[ sub-C k₁ k₂ s t K ]
sub-T {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μθ S) = μθ (sub-S k₁ k₂ (fmap {λ - → T - Θ′} {λ - → T - (Θ′ , A)} (λ x → TermKit.wkΘ k₁ x) s) (sub-lift (CotermKit.kit k₂) t) S)

sub-C k₁ k₂ s t (` α) = CotermKit.tm k₂ (t α)
sub-C k₁ k₂ s t fst[ K ] = fst[ sub-C k₁ k₂ s t K ]
sub-C k₁ k₂ s t snd[ K ] = snd[ sub-C k₁ k₂ s t K ]
sub-C k₁ k₂ s t `[ K , L ] = `[ sub-C k₁ k₂ s t K , sub-C k₁ k₂ s t L ]
sub-C k₁ k₂ s t not⟨ M ⟩ = not⟨ (sub-T k₁ k₂ s t M) ⟩
sub-C {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μγ S) = μγ (sub-S k₁ k₂ (sub-lift (TermKit.kit k₁) s) (fmap {C Γ′} {C (Γ′ , A)} (λ x → CotermKit.wkΓ k₂ x) t) S)

sub-S k₁ k₂ s t (M ● K) = (sub-T k₁ k₂ s t M) ● (sub-C k₁ k₂ s t K)

TK : TermKit _⟶_∣_ 
TK = record 
  {  tm = λ a → a
  ;  wkΘ = ren-T id-var (ren-weaken id-var)
  ;  kit = record { vr = `_ ; wk = ren-T (ren-weaken id-var) id-var }
  }

module TK = TermKit TK

CK : CotermKit λ Γ Θ A → A ∣ Γ ⟶ Θ
CK = record
  {  tm = λ a → a 
  ;  wkΓ = ren-C (ren-weaken id-var) id-var
  ;  kit = record { vr = `_ ; wk = ren-C id-var (ren-weaken id-var) }
  }

module CK = CotermKit CK

V-ren : ∀ {Γ Γ′ Θ Θ′ A} {V : Γ ⟶ Θ ∣ A} (ρ : Γ ↝ Γ′) (ϱ : Θ ↝ Θ′) →
  Value V → Value (ren-T ρ ϱ V)
V-ren ρ ϱ V-var = V-var
V-ren ρ ϱ (V-prod v w) = V-prod (V-ren ρ ϱ v) (V-ren ρ ϱ w)
V-ren ρ ϱ (V-inl v) = V-inl (V-ren ρ ϱ v)
V-ren ρ ϱ (V-inr v) = V-inr (V-ren ρ ϱ v)
V-ren ρ ϱ V-not = V-not  

CV-ren : ∀ {Γ Γ′ Θ Θ′ A} {P : A ∣ Γ ⟶ Θ} (ρ : Γ ↝ Γ′) (ϱ : Θ ↝ Θ′) →
  Covalue P → Covalue (ren-C ρ ϱ P)
CV-ren ρ ϱ CV-covar = CV-covar
CV-ren ρ ϱ (CV-sum p q) = CV-sum (CV-ren ρ ϱ p) (CV-ren ρ ϱ q)
CV-ren ρ ϱ (CV-fst p) = CV-fst (CV-ren ρ ϱ p)
CV-ren ρ ϱ (CV-snd p) = CV-snd (CV-ren ρ ϱ p)
CV-ren ρ ϱ CV-not = CV-not

TVK : TermKit TermValue
TVK = record
  { tm = λ x → proj₁ x
  ; wkΘ = λ x → ⟨ (TK.wkΘ (proj₁ x)) , V-ren id-var (ren-weaken id-var) (proj₂ x) ⟩
  ; kit = record { vr = λ x → ⟨ ` x , V-var ⟩ ; wk = λ x → ⟨ (VarKit.wk (TK.kit) (proj₁ x)) , V-ren (ren-weaken id-var) id-var (proj₂ x) ⟩ }
  }

module TVK = TermKit TVK

CVK : CotermKit CotermValue
CVK = record 
  { tm = λ x → proj₁ x 
  ; wkΓ = λ x → ⟨ (CK.wkΓ (proj₁ x)) , CV-ren (ren-weaken id-var) id-var (proj₂ x) ⟩ 
  ; kit = record { vr = λ x → ⟨ (` x) , CV-covar ⟩ ; wk = λ x → ⟨ (VarKit.wk (CK.kit) (proj₁ x)) , (CV-ren id-var (ren-weaken id-var) (proj₂ x)) ⟩ } 
  }

module CVK = CotermKit CVK

sub-t-tv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ TermValue Θ′ ]→ Γ′ → Θ –[ Fix₁ Coterm Γ′ ]→ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-t-tv = sub-T TVK CK

sub-t-cv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ Term Θ′ ]→ Γ′ → Θ –[ Fix₁ CotermValue Γ′ ]→ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-t-cv = sub-T TK CVK

sub-c-tv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ TermValue Θ′ ]→ Γ′ → Θ –[ Fix₁ Coterm Γ′ ]→ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-c-tv = sub-C TVK CK

sub-c-cv : ∀ {Γ Θ Γ′ Θ′ A} → Γ –[ Fix₂ Term Θ′ ]→ Γ′ → Θ –[ Fix₁ CotermValue Γ′ ]→ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-c-cv = sub-C TK CVK

sub-s-tv : ∀ {Γ Θ Γ′ Θ′} → Γ –[ Fix₂ TermValue Θ′ ]→ Γ′ → Θ –[ Fix₁ Coterm Γ′ ]→ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′
sub-s-tv = sub-S TVK CK

sub-s-cv : ∀ {Γ Θ Γ′ Θ′} → Γ –[ Fix₂ Term Θ′ ]→ Γ′ → Θ –[ Fix₁ CotermValue Γ′ ]→ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′
sub-s-cv = sub-S TK CVK

wkΓᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ , B ⟶ Θ ∣ A
wkΓᵗ = TermKit.wkΓ TK

wkΘᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ ⟶ Θ , B ∣ A
wkΘᵗ = TermKit.wkΘ TK

wkΓᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ , B ⟶ Θ
wkΓᶜ = CotermKit.wkΓ CK

wkΘᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ ⟶ Θ , B
wkΘᶜ = CotermKit.wkΘ CK

wkΓⱽ : ∀ {Γ Θ A B} → TermValue Γ Θ A → TermValue (Γ , B) Θ A
wkΓⱽ = TermKit.wkΓ TVK

wkΘⱽ : ∀ {Γ Θ A B} → TermValue Γ Θ A → TermValue Γ (Θ , B) A
wkΘⱽ = TermKit.wkΘ TVK

wkΓᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue (Γ , B) Θ A
wkΓᶜⱽ = CotermKit.wkΓ CVK

wkΘᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue Γ (Θ , B) A
wkΘᶜⱽ = CotermKit.wkΘ CVK

intΓᵗ : ∀ {Γ Θ A B C} → Γ , A , B ⟶ Θ ∣ C → Γ , B , A ⟶ Θ ∣ C
intΓᵗ M = ren-T (add _∋_ (`S `Z) (ren-lift (ren-weaken id-var))) id-var M

fmap-wkΘᵗ : ∀ {Γ Γ′} Θ A → Γ –[ Fix₂ Term Θ ]→ Γ′ → Γ –[ Fix₂ Term (Θ , A) ]→ Γ′
fmap-wkΘᵗ Θ A = fmap {Fix₂ Term Θ} {Fix₂ Term (Θ , A)} wkΘᵗ

fmap-wkΓᶜ : ∀ {Θ Θ′} Γ A → Θ –[ Fix₁ Coterm Γ ]→ Θ′ → Θ –[ Fix₁ Coterm (Γ , A) ]→ Θ′
fmap-wkΓᶜ Γ A = fmap {Fix₁ Coterm Γ}{Fix₁ Coterm (Γ , A)} wkΓᶜ

fmap-wkΘᵗⱽ : ∀ {Γ Γ′} Θ A → Γ –[ Fix₂ TermValue Θ ]→ Γ′ → Γ –[ Fix₂ TermValue (Θ , A) ]→ Γ′
fmap-wkΘᵗⱽ Θ A = fmap {Fix₂ TermValue Θ} {Fix₂ TermValue (Θ , A)} wkΘⱽ

fmap-wkΓᶜⱽ : ∀ {Θ Θ′} Γ A → Θ –[ Fix₁ CotermValue Γ ]→ Θ′ → Θ –[ Fix₁ CotermValue (Γ , A) ]→ Θ′
fmap-wkΓᶜⱽ Γ A = fmap {Fix₁ CotermValue Γ}{Fix₁ CotermValue (Γ , A)} wkΓᶜⱽ


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

_ⱽ⟨_/⟩ˢ : ∀ {Γ Θ A}
  → Γ , A ↦ Θ
  → TermValue Γ Θ A
    ---------------
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

_ⱽ[_/]ˢ : ∀ {Γ Θ A}
  → Γ ↦ Θ , A
  → CotermValue Γ Θ A
    -----------------
  → Γ ↦ Θ

_⟨_/⟩ᵗ {Γ}{Θ} N M = sub-T TK CVK (add (Fix₂ Term Θ) M id-T) id-CV N

_⟨_/⟩ᶜ {Γ}{Θ} L M = sub-C TK CVK (add (Fix₂ Term Θ) M id-T) id-CV L

_⟨_/⟩ˢ {Γ}{Θ} S M = sub-S TK CVK (add (Fix₂ Term Θ) M id-T) id-CV S

_ⱽ⟨_/⟩ˢ {Γ}{Θ} S V = sub-S TVK CK (add (Fix₂ TermValue Θ) V id-TV) id-C S

_[_/]ᵗ {Γ}{Θ} N K = sub-T TVK CK id-TV (add (Fix₁ Coterm Γ) K id-C) N

_[_/]ᶜ {Γ}{Θ} L K = sub-C TVK CK id-TV (add (Fix₁ Coterm Γ) K id-C) L

_[_/]ˢ {Γ}{Θ} S K = sub-S TVK CK id-TV (add (Fix₁ Coterm Γ) K id-C) S

_ⱽ[_/]ˢ {Γ}{Θ} S P = sub-S TK CVK id-T (add (Fix₁ CotermValue Γ) P id-CV) S


_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

-- RCS-T : ∀ {Γ Γ′ Γ″ Θ} → (σ : Γ –[ Fix₂ Term Θ ]→ Γ′) (ρ : Γ′ ↝ Γ″) → Γ –[ Fix₂ Term Θ ]→ Γ″
-- RCS-T σ ρ x = ren-T ρ id-var (σ x)

-- RCS-C : ∀ {Θ Θ′ Θ″ Γ} → (σ : Θ –[ Fix₁ Coterm Γ ]→ Θ′) (ρ : Θ′ ↝ Θ″) → Θ –[ Fix₁ Coterm Γ ]→ Θ″
-- RCS-C σ ρ x = ren-C id-var ρ (σ x)

postulate
  sub-ren-T : ∀ {T C Γ Γ′ Γ″ Θ Θ′ Θ″ A} (tk : TermKit T) (ck : CotermKit C) (M : Γ ⟶ Θ ∣ A) (s : Γ′ –[ Fix₂ T Θ″ ]→ Γ″) (t : Θ′ –[ Fix₁ C Γ″ ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
    → sub-T tk ck s t (ren-T u v M) ≡ sub-T tk ck (s ∘ u) (t ∘ v) M

  sub-ren-C : ∀ {T C Γ Γ′ Γ″ Θ Θ′ Θ″ A} (tk : TermKit T) (ck : CotermKit C) (K : A ∣ Γ ⟶ Θ) (s : Γ′ –[ Fix₂ T Θ″ ]→ Γ″) (t : Θ′ –[ Fix₁ C Γ″ ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
    → sub-C tk ck s t (ren-C u v K) ≡ sub-C tk ck (s ∘ u) (t ∘ v) K

  sub-ren-S : ∀ {T C Γ Γ′ Γ″ Θ Θ′ Θ″} (tk : TermKit T) (ck : CotermKit C) (S : Γ ↦ Θ) (s : Γ′ –[ Fix₂ T Θ″ ]→ Γ″) (t : Θ′ –[ Fix₁ C Γ″ ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
    → sub-S tk ck s t (ren-S u v S) ≡ sub-S tk ck (s ∘ u) (t ∘ v) S

-- sub-ren-T tk ck (` x) s t u v = refl
-- sub-ren-T tk ck `⟨ M , N ⟩ s t u v = cong₂ `⟨_,_⟩ (sub-ren-T tk ck M s t u v) (sub-ren-T tk ck N s t u v)
-- sub-ren-T tk ck inl⟨ M ⟩ s t u v = cong inl⟨_⟩ (sub-ren-T tk ck M s t u v)
-- sub-ren-T tk ck inr⟨ M ⟩ s t u v = cong inr⟨_⟩ (sub-ren-T tk ck M s t u v)
-- sub-ren-T tk ck not[ K ] s t u v = cong not[_](sub-ren-C tk ck K s t u v)
-- sub-ren-T {T} {C} {Γ} {Γ′} {Γ″} {Θ} {Θ′} {Θ″} {A} tk ck (μθ S) s t u v = cong μθ 
--   (begin 
--     sub-S tk ck 
--       (fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)}(TermKit.wkΘ tk) s)
--       (sub-lift (CotermKit.kit ck) t)
--       (ren-S u (ren-lift v) S)
--   ≡⟨ sub-ren-S tk ck S (fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)}(TermKit.wkΘ tk) s) (sub-lift (CotermKit.kit ck) t) u (ren-lift v) ⟩
--     sub-S tk ck ((fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)} (TermKit.wkΘ tk) s) ∘ u)
--       ((sub-lift (CotermKit.kit ck) t) ∘ ren-lift v) S
--   ≡⟨ {!   !} ⟩
--     (sub-S tk ck (fmap {Fix₂ T Θ″}{Fix₂ T (Θ″ , A)} (TermKit.wkΘ tk) (s ∘ u))
--       (sub-lift (CotermKit.kit ck) (t ∘ v)) S) 
--   ∎)

-- sub-ren-C tk ck (` α) s t u v = refl
-- sub-ren-C tk ck fst[ K ] s t u v = cong fst[_] (sub-ren-C tk ck K s t u v)
-- sub-ren-C tk ck snd[ K ] s t u v = cong snd[_] (sub-ren-C tk ck K s t u v)
-- sub-ren-C tk ck `[ K , L ] s t u v = cong₂ `[_,_] (sub-ren-C tk ck K s t u v) (sub-ren-C tk ck L s t u v)
-- sub-ren-C tk ck not⟨ M ⟩ s t u v = cong not⟨_⟩ (sub-ren-T tk ck M s t u v)
-- sub-ren-C {T} {C} {Γ} {Γ′} {Γ″} {Θ} {Θ′} {Θ″} {A} tk ck (μγ S) s t u v = cong μγ 
--   (trans 
--     (sub-ren-S tk ck S (sub-lift (TermKit.kit tk) s) (fmap {Fix₁ C Γ″} {Fix₁ C (Γ″ , A)} (CotermKit.wkΓ ck) t) (ren-lift u) v) 
--     {!   !})

-- sub-ren-S tk ck (M ● K) s t u v = cong₂ _●_ (sub-ren-T tk ck M s t u v) (sub-ren-C tk ck K s t u v)

-- ren-sub-T : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (M : Γ ⟶ Θ ∣ A) (s : Γ –[ Fix₂ Term Θ′ ]→ Γ′) (t : Θ –[ Fix₁ Coterm Γ′ ]→ Θ′) (u : Γ′ ↝ Γ″) (v : Θ′ ↝ Θ″)
--   → ren-T u v (sub-T TK CK s t M) ≡ sub-T TK CK (RCS-T (fmap (ren-T id-var v) s) u) (RCS-C (fmap (ren-C u id-var) t) v) M

-- ren-sub-C : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (K : A ∣ Γ ⟶ Θ) (s : Γ –[ Fix₂ Term Θ′ ]→ Γ′) (t : Θ –[ Fix₁ Coterm Γ′ ]→ Θ′) (u : Γ′ ↝ Γ″) (v : Θ′ ↝ Θ″)
--   → ren-C u v (sub-C TK CK s t K) ≡ sub-C TK CK (RCS-T (fmap (ren-T id-var v) s) u) (RCS-C (fmap (ren-C u id-var) t) v) K

-- ren-sub-S : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″} (S : Γ ↦ Θ) (s : Γ –[ Fix₂ Term Θ′ ]→ Γ′) (t : Θ –[ Fix₁ Coterm Γ′ ]→ Θ′) (u : Γ′ ↝ Γ″) (v : Θ′ ↝ Θ″)
--   → ren-S u v (sub-S TK CK s t S) ≡ sub-S TK CK (RCS-T (fmap (ren-T id-var v) s) u) (RCS-C (fmap (ren-C u id-var) t) v) S

-- ren-sub-T (` x) s t u v = {!   !}
-- ren-sub-T `⟨ M , N ⟩ s t u v = cong₂ `⟨_,_⟩ (ren-sub-T M s t u v) (ren-sub-T N s t u v)
-- ren-sub-T inl⟨ M ⟩ s t u v = {!   !}
-- ren-sub-T inr⟨ M ⟩ s t u v = {!   !}
-- ren-sub-T not[ K ] s t u v = {!   !}
-- ren-sub-T (μθ S) s t u v = cong μθ (
--   begin 
--     ren-S u (ren-lift v)
--       (sub-S TK CK
--        (λ x → ren-T (λ x₁ → x₁) (λ x₁ → `S x₁) (s x))
--        (sub-lift
--         (record { vr = `_ ; wk = ren-C (λ x → x) (λ x → `S x) }) t)
--        S)
--   ≡⟨ ren-sub-S S (fmap (ren-T id-var (ren-weaken id-var)) s) (sub-lift (CK.kit) t) u (ren-lift v) ⟩
--     {!   !})