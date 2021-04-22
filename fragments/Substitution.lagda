\begin{code}
module fragments.Substitution where

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

\end{code}

%<*maps>
\begin{code}
_–[_]→_ : Context → Sorted-Family → Context → Set
Γ –[ X ]→ Δ = {A : Type} → Γ ∋ A → X Δ A

_↝_ : Context → Context → Set
Γ ↝ Δ = Γ –[ _∋_ ]→ Δ
\end{code}
%</maps>

%<*add>
\begin{code}
add : ∀{Γ Δ A}(T : Context → Type → Set) → T Δ A → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ Δ
add T t σ `Z = t
add T t σ (`S v) = σ v
\end{code}
%</add>
\begin{code}

--Removing a T from a renaming map--
ren-skip : ∀ {Γ Γ′ A} → (Γ , A) ↝ Γ′ → Γ ↝ Γ′
ren-skip ρ x = ρ (`S x)

--Removing a T from a context map
sub-skip : ∀ {Γ Γ′ A} T → ((Γ , A) –[ T ]→ Γ′) → ( Γ –[ T ]→ Γ′)
sub-skip T σ x = σ (`S x)
\end{code}
%<*kits>
\begin{code}
record VarKit (T : Context → Type → Set) : Set where
  field
    vr : ∀ {Γ A} → Γ ∋ A → T Γ A
    wk : ∀ {Γ A B} → T Γ A → T (Γ , B) A

record TermKit (T : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → T Γ Θ A → Γ ⟶ Θ ∣ A
    kit : ∀ {Θ}        → VarKit (Fix₂ T Θ)
    wkΘ : ∀ {Γ Θ A B}   → T Γ Θ A → T Γ (Θ , B) A
  open module K {Θ} = VarKit (kit {Θ}) renaming (wk to wkΓ) public

record CotermKit (C : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → C Γ Θ A → A ∣ Γ ⟶ Θ
    wkΓ : ∀ {Γ Θ A B}   → C Γ Θ A → C (Γ , B) Θ A
    kit : ∀ {Γ}        → VarKit (Fix₁ C Γ)
  open module K {Γ} = VarKit (kit {Γ}) renaming (wk to wkΘ) public
\end{code}
%</kits>

%<*ren-weaken>
\begin{code}
ren-weaken : ∀ {Γ Δ A} → Γ ↝ Δ → Γ ↝ (Δ , A)
\end{code}
%</ren-weaken>
\begin{code}
ren-weaken ρ x = `S (ρ x)
\end{code}

%<*ren-lift>
\begin{code}
ren-lift : ∀ {Γ Δ A} → Γ ↝ Δ → (Γ , A) ↝ (Δ , A)
ren-lift ρ `Z = `Z
ren-lift ρ (`S x) = `S (ρ x)
\end{code}
%</ren-lift>

%<*renty>
\begin{code}
ren-T : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
ren-C : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
ren-S : ∀ {Γ Γ′ Θ Θ′} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′
\end{code}
%</renty>

%<*renvar>
\begin{code}
ren-T ρ ϱ (` x) = ` (ρ x)
\end{code}
%</renvar>
\begin{code}
ren-T ρ ϱ `⟨ M , N ⟩ = `⟨ (ren-T ρ ϱ M) , ren-T ρ ϱ N ⟩
ren-T ρ ϱ inr⟨ M ⟩ = inr⟨ ren-T ρ ϱ M ⟩
ren-T ρ ϱ inl⟨ M ⟩ = inl⟨ ren-T ρ ϱ M ⟩
ren-T ρ ϱ not[ K ] = not[ ren-C ρ ϱ K ]
\end{code}
%<*rencovarabs>
\begin{code}
ren-T ρ ϱ (μθ S) = μθ (ren-S ρ (ren-lift ϱ) S)
\end{code}
%</rencovarabs>

%<*rencovar>
\begin{code}
ren-C ρ ϱ (` α) = ` (ϱ α)
\end{code}
%</rencovar>
\begin{code}
ren-C ρ ϱ fst[ K ] = fst[ ren-C ρ ϱ K ]
ren-C ρ ϱ snd[ K ] = snd[ ren-C ρ ϱ K ]
ren-C ρ ϱ `[ K , L ] = `[ ren-C ρ ϱ K , ren-C ρ ϱ L ]
ren-C ρ ϱ not⟨ M ⟩ = not⟨ (ren-T ρ ϱ M) ⟩
\end{code}
%<*renvarabs>
\begin{code}
ren-C ρ ϱ (μγ S) = μγ (ren-S (ren-lift ρ) ϱ S)
\end{code}
%</renvarabs>

\begin{code}
ren-S ρ ϱ (M ● K) = (ren-T ρ ϱ M) ● (ren-C ρ ϱ K) 


VK : VarKit _∋_ 
VK = record 
  {  vr = λ a → a
  ;  wk = `S
  } 

\end{code}
%<*subweaken>
\begin{code}
sub-weaken : ∀ {Γ Δ A T} → VarKit T → Γ –[ T ]→ Δ → Γ –[ T ]→ (Δ , A)
sub-weaken k σ x = VarKit.wk k (σ x)
\end{code}
%</subweaken>
%<*sublift>
\begin{code}
sub-lift : ∀ {Γ Δ A T} → VarKit T → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ (Δ , A)
sub-lift k σ `Z = VarKit.vr k `Z
sub-lift k σ (`S x) = sub-weaken k σ x
\end{code}
%</sublift>
\begin{code}
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
\end{code}

%<*fmap>
\begin{code}
fmap : ∀ {T T′ Γ Γ′} (f : ∀ {Γ A} → T Γ A → T′ Γ A) → Γ –[ T ]→ Γ′ → Γ –[ T′ ]→ Γ′
fmap f σ `x = f (σ `x)
\end{code}
%</fmap>

%<*subty>
\begin{code}
sub-T : ∀ {T A C Γ Θ Γ′ Θ′} → TermKit T → CotermKit C 
  → Γ –[ (Fix₂ T Θ′) ]→ Γ′ → Θ –[ (Fix₁ C Γ′) ]→ Θ′ 
  → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-C : ∀ {T A C Γ Θ Γ′ Θ′} → TermKit T → CotermKit C 
  → Γ –[ (Fix₂ T Θ′) ]→ Γ′ → Θ –[ (Fix₁ C Γ′) ]→ Θ′ 
  → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-S : ∀ {T C Γ Θ Γ′ Θ′} → TermKit T → CotermKit C 
  → Γ –[ (Fix₂ T Θ′) ]→ Γ′ → Θ –[ (Fix₁ C Γ′) ]→ Θ′ 
  → Γ ↦ Θ → Γ′ ↦ Θ′
\end{code}
%</subty>
%<*subvar>
\begin{code}
sub-T k₁ k₂ s t (` x) = TermKit.tm k₁ (s x)
\end{code}
%</subvar>
\begin{code}
sub-T k₁ k₂ s t `⟨ M , N ⟩ = `⟨ sub-T k₁ k₂ s t M , sub-T k₁ k₂ s t N ⟩
sub-T k₁ k₂ s t inl⟨ M ⟩ = inl⟨ sub-T k₁ k₂ s t M ⟩
sub-T k₁ k₂ s t inr⟨ M ⟩ = inr⟨ sub-T k₁ k₂ s t M ⟩
sub-T k₁ k₂ s t not[ K ] = not[ sub-C k₁ k₂ s t K ]
\end{code}
%<*subcovarabs>
\begin{code}
sub-T {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μθ S) = μθ (sub-S k₁ k₂ 
  (fmap {λ - → T - Θ′} {λ - → T - (Θ′ , A)} (λ x → TermKit.wkΘ k₁ x) s) 
  (sub-lift (CotermKit.kit k₂) t) S)
\end{code}
%</subcovarabs>

%<*subcovar>
\begin{code}
sub-C k₁ k₂ s t (` α) = CotermKit.tm k₂ (t α)
\end{code}
%</subcovar>
\begin{code}
sub-C k₁ k₂ s t fst[ K ] = fst[ sub-C k₁ k₂ s t K ]
sub-C k₁ k₂ s t snd[ K ] = snd[ sub-C k₁ k₂ s t K ]
sub-C k₁ k₂ s t `[ K , L ] = `[ sub-C k₁ k₂ s t K , sub-C k₁ k₂ s t L ]
sub-C k₁ k₂ s t not⟨ M ⟩ = not⟨ (sub-T k₁ k₂ s t M) ⟩
\end{code}
%<*subvarabs>
\begin{code}
sub-C {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μγ S) = μγ (sub-S k₁ k₂ 
  (sub-lift (TermKit.kit k₁) s) 
  (fmap {C Γ′} {C (Γ′ , A)} (λ x → CotermKit.wkΓ k₂ x) t) S)
\end{code}
%</subvarabs>

\begin{code}
sub-S k₁ k₂ s t (M ● K) = (sub-T k₁ k₂ s t M) ● (sub-C k₁ k₂ s t K)


TK : TermKit _⟶_∣_ 
TK = record 
  {  tm = λ a → a
  ;  wkΘ = ren-T id-var (ren-weaken id-var)
  ;  kit = record { vr = `_ ; wk = ren-T (ren-weaken id-var) id-var }
  }
\end{code}

%<*cotermkit>
\begin{code}
CK : CotermKit λ Γ Θ A → A ∣ Γ ⟶ Θ
CK = record
  {  tm = λ a → a 
  ;  wkΓ = ren-C (ren-weaken id-var) id-var
  ;  kit = record { vr = `_ ; wk = ren-C id-var (ren-weaken id-var) }
  }
\end{code}
%</cotermkit>

%<*valren>
\begin{code}
V-ren : ∀ {Γ Γ′ Θ Θ′ A} {V : Γ ⟶ Θ ∣ A} {ρ : Γ ↝ Γ′} {ϱ : Θ ↝ Θ′} →
  Value V → Value (ren-T ρ ϱ V)
\end{code}
%</valren>
\begin{code}
V-ren V-var = V-var
V-ren (V-prod v w) = V-prod (V-ren v) (V-ren w)
V-ren (V-inl v) = V-inl (V-ren v)
V-ren (V-inr v) = V-inr (V-ren v)
V-ren V-not = V-not  
\end{code}

%<*covalren>
\begin{code}
covalue-ren : ∀ {Γ Γ′ Θ Θ′ A} {P : A ∣ Γ ⟶ Θ} (ρ : Γ ↝ Γ′) (ϱ : Θ ↝ Θ′) →
  Covalue P → Covalue (ren-C ρ ϱ P)
\end{code}
%</covalren>
\begin{code}
covalue-ren ρ ϱ CV-covar = CV-covar
covalue-ren ρ ϱ (CV-sum p q) = CV-sum (covalue-ren ρ ϱ p) (covalue-ren ρ ϱ q)
covalue-ren ρ ϱ (CV-fst p) = CV-fst (covalue-ren ρ ϱ p)
covalue-ren ρ ϱ (CV-snd p) = CV-snd (covalue-ren ρ ϱ p)
covalue-ren ρ ϱ CV-not = CV-not
\end{code}

%<*termvalkit>
\begin{code}
TVK : TermKit TermValue
TVK = record
  { tm = λ x → proj₁ x
  ; wkΘ = λ x → ⟨ (TermKit.wkΘ TK (proj₁ x)) 
                , V-ren (proj₂ x) ⟩
  ; kit = record 
    { vr = λ x → ⟨ ` x , V-var ⟩ 
    ; wk = λ x → ⟨ (VarKit.wk (TermKit.kit TK) (proj₁ x)) 
                 , V-ren (proj₂ x) ⟩ }
  }
\end{code}
%</termvalkit>
\begin{code}
CVK : CotermKit CotermValue
CVK = record 
  { tm = λ x → proj₁ x 
  ; wkΓ = λ x → ⟨ (CotermKit.wkΓ CK (proj₁ x)) 
                , covalue-ren (ren-weaken id-var) id-var (proj₂ x) ⟩ 
  ; kit = record 
    { vr = λ x → ⟨ (` x) , CV-covar ⟩ 
    ; wk = λ x → ⟨ (VarKit.wk (CotermKit.kit CK) (proj₁ x)) 
                , (covalue-ren id-var (ren-weaken id-var) (proj₂ x)) ⟩ } 
  }
\end{code}

\begin{code}
wkΓᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ , B ⟶ Θ ∣ A
wkΓᵗ = TermKit.wkΓ TK

wkΘᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ ⟶ Θ , B ∣ A
wkΘᵗ = TermKit.wkΘ TK

wkΓᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ , B ⟶ Θ
wkΓᶜ = CotermKit.wkΓ CK

wkΘᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ ⟶ Θ , B
wkΘᶜ = CotermKit.wkΘ CK

wkΓᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue (Γ , B) Θ A
wkΓᶜⱽ = CotermKit.wkΓ CVK

wkΘᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue Γ (Θ , B) A
wkΘᶜⱽ = CotermKit.wkΘ CVK

intΓᵗ : ∀ {Γ Θ A B C} → Γ , A , B ⟶ Θ ∣ C → Γ , B , A ⟶ Θ ∣ C
intΓᵗ M = ren-T (add _∋_ (`S `Z) (ren-lift (ren-weaken id-var))) id-var M
\end{code}

%<*fundef>
\begin{code}
ƛⱽ_ : ∀ {Γ Θ A B}  → Γ , A ⟶ Θ ∣ B            → Γ ⟶ Θ ∣ A ⇒ⱽ B 
ƛᴺ_ : ∀ {Γ Θ A B}  → Γ , A ⟶ Θ ∣ B            → Γ ⟶ Θ ∣ A ⇒ᴺ B
_·ⱽ_ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → B ∣ Γ ⟶ Θ   → A ⇒ⱽ B ∣ Γ ⟶ Θ 
_·ᴺ_ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → B ∣ Γ ⟶ Θ   → A ⇒ᴺ B ∣ Γ ⟶ Θ 
\end{code}
%</fundef>

%<*fun>
\begin{code}
ƛⱽ N = not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ intΓᵗ (wkΓᵗ N) ⟩ ]) ]) ]
ƛᴺ N = μθ (inl⟨ not[ μγ(inr⟨ wkΘᵗ N ⟩ ● θ 0) ] ⟩ ● θ 0) 
M ·ⱽ N = not⟨ `⟨ M , not[ N ] ⟩ ⟩
M ·ᴺ N = `[ not⟨ M ⟩ , N ]
\end{code}
%</fun>

_++_ : ∀ {T Γ Γ′ Γ″} → Γ ↝ Γ′ → Γ′ –[ T ]→ Γ″ → Γ –[ T ]→ Γ″
(s ++ t) x = t (s x)

-- sub-fmap : ∀ {Γ Θ Θ′ A} (s : Subst (λ -₁ -₂ → -₂ ∣ Γ ⟶ -₁) Θ Θ′) (x : Θ′ ∋ A) 
--   → sub-var (fmap (ren-C VK ((weaken) VK id-var) id-var) s) x ≡ ren-C VK (weaken VK id-var) id-var (sub-var s x)
-- sub-fmap (s , s′) `Z = refl
-- sub-fmap (s , s′) (`S x) = sub-fmap s x

-- fmap++ : ∀ {Γ Θ Θ′ Θ″} (s : Subst (λ -₁ -₂ → -₂ ∣ Γ ⟶ -₁) Θ Θ′) (t : Subst _∋_ Θ′ Θ″) 
--   → (fmap (ren-C VK ((weaken) VK id-var) id-var) s ++ t) ≡ fmap (ren-C VK (weaken VK id-var) id-var) (s ++ t)
-- fmap++ s ⨀ = refl
-- fmap++ s (_,_ t t′) = cong₂ _,_ (fmap++ s t) (sub-fmap s t′)

-- lemma : ∀ {Γ Γ′ Γ″ Θ} (s : Subst (λ -₁ -₂ → -₁ ⟶ Θ ∣ -₂) Γ Γ′) (t : Subst _∋_ Γ′ Γ″)
--   → ((exts (TermKit.kit TK) s ++ weaken VK t) , (` `Z)) ≡ exts (TermKit.kit TK) (s ++ t)

-- lemma s ⨀ = refl
-- lemma s (t , x) = cong₂ _,_ ({!   !}) refl

-- lemma : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (s : Subst (λ -₁ → _⟶_∣_ -₁ Θ) Γ Γ′) (t : Subst (λ -₁ -₂ → -₂ ∣ Γ ⟶ -₁) Θ Θ′) (u : Subst _∋_ Γ′ Γ″) (v : Subst _∋_ Θ′ Θ″) (S : Γ″ ↦ Θ″ , A)
--     → sub-S TK CK
--       ((exts (CotermKit.kit CK) s ++ weaken VK u) , (` `Z))
--       (fmap (ren-C VK (weaken VK id-var) id-var) t ++ v)
--       S
--       ≡
--       sub-S TK CK
--       (fmap (ren-T VK id-var (weaken VK id-var)) (s ++ u))
--       (exts (CotermKit.kit CK) (t ++ v))
--       S
-- lemma s t u v S = trans {! sub-ren-S  !} {!   !}
    

-- sub-ren-T : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (M : Γ ⟶ Θ ∣ A) (s : Γ′ –[ (λ -₁ -₂ → -₁ ⟶ Θ″ ∣ -₂) ]→ Γ″) (t : Θ′ –[ (λ -₁ -₂ → -₂ ∣ Γ″ ⟶ -₁) ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-T TK CK s t (ren-T u v M) ≡ sub-T TK CK (u ++ s) (v ++ t) M

-- sub-ren-C : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (K : A ∣ Γ ⟶ Θ) (s : Γ′ –[ (λ -₁ -₂ → -₁ ⟶ Θ″ ∣ -₂) ]→ Γ″) (t : Θ′ –[ (λ -₁ -₂ → -₂ ∣ Γ″ ⟶ -₁) ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-C TK CK s t (ren-C u v K) ≡ sub-C TK CK (u ++ s) (v ++ t) K

-- sub-ren-S : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″} (S : Γ ↦ Θ) (s : Γ′ –[ (λ -₁ -₂ → -₁ ⟶ Θ″ ∣ -₂) ]→ Γ″) (t : Θ′ –[ (λ -₁ -₂ → -₂ ∣ Γ″ ⟶ -₁) ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-S TK CK s t (ren-S u v S) ≡ sub-S TK CK (u ++ s) (v ++ t) S

-- sub-ren-T (` x) s t u v = refl
-- sub-ren-T `⟨ M , N ⟩ s t u v = cong₂ `⟨_,_⟩ (sub-ren-T M s t u v) (sub-ren-T N s t u v)
-- sub-ren-T inl⟨ M ⟩ s t u v = cong inl⟨_⟩ (sub-ren-T M s t u v)
-- sub-ren-T inr⟨ M ⟩ s t u v = cong inr⟨_⟩ (sub-ren-T M s t u v)
-- sub-ren-T not[ K ] s t u v = cong not[_](sub-ren-C K s t u v)
-- sub-ren-T (μθ S) s t u v = cong μθ 
--   (begin 
--     sub-S TK CK
--       (fmap (ren-T (id-var) (ren-weaken id-var)) s)
--       (sub-lift (CotermKit.kit CK) t)
--       (ren-S u (ren-lift v) S)
--   ≡⟨ sub-ren-S S (fmap (ren-T id-var (ren-weaken id-var)) s) (sub-lift (CotermKit.kit CK) t) u (ren-lift v) ⟩
--     sub-S TK CK
--       (u ++ fmap (TermKit.wkΘ TK) s)
--       (ren-lift v ++ sub-lift (CotermKit.kit CK) t) S
--   ≡⟨ cong (λ x → sub-S TK CK (u ++ fmap (TermKit.wkΘ TK) s) x S) {!   !} ⟩
--     {!  !})

-- sub-ren-C (` α) s t u v = refl
-- sub-ren-C fst[ K ] s t u v = cong fst[_] (sub-ren-C K s t u v)
-- sub-ren-C snd[ K ] s t u v = cong snd[_] (sub-ren-C K s t u v)
-- sub-ren-C `[ K , L ] s t u v = cong₂ `[_,_] (sub-ren-C K s t u v) (sub-ren-C L s t u v)
-- sub-ren-C not⟨ M ⟩ s t u v = cong not⟨_⟩ (sub-ren-T M s t u v)
-- sub-ren-C (μγ S) s t u v = cong μγ ({!   !})
-- --   (begin
-- --     sub-S TK CK
-- --       (exts (TermKit.kit TK) s)
-- --       (fmap (ren-C VK (weaken VK id-var) id-var) t)
-- --       (ren-S VK (exts VK u) v S)
-- --   ≡⟨ sub-ren-S S (exts (TermKit.kit TK) s) (fmap (ren-C VK (weaken VK id-var) id-var) t) (exts VK u) v ⟩
-- --     sub-S TK CK
-- --       ((exts (TermKit.kit TK) s ++ weaken VK u) , (` `Z))
-- --       (fmap (ren-C VK (weaken VK id-var) id-var) t ++ v)
-- --       S
-- --   ≡⟨ cong (λ x → sub-S TK CK ((exts (TermKit.kit TK) s ++ weaken VK u) , ` `Z) x S)  (fmap++ t v) ⟩ 
-- --     sub-S TK CK
-- --       ((exts (TermKit.kit TK) s ++ weaken VK u) , (` `Z))
-- --       (fmap (ren-C VK (weaken VK id-var) id-var) (t ++ v))
-- --       S
-- --   ≡⟨ cong (λ x → sub-S TK CK x (fmap (ren-C VK (weaken VK id-var) id-var) (t ++ v)) S) {!    !} ⟩
-- --     sub-S TK CK
-- --       (exts (TermKit.kit TK) (s ++ u))
-- --       (fmap (ren-C VK (weaken VK id-var) id-var) (t ++ v))
-- --       S
-- --   ∎)

-- sub-ren-S (M ● K) s t u v = cong₂ _●_ (sub-ren-T M s t u v) (sub-ren-C K s t u v)