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

--Removing a term from a renaming map--
ren-skip : ∀ {Γ Γ′ A} → (Γ , A) ↝ Γ′ → Γ ↝ Γ′
ren-skip ρ x = ρ (`S x)

--Removing a term from a context map
sub-skip : ∀ {Γ Γ′ A} T → ((Γ , A) –[ T ]→ Γ′) → ( Γ –[ T ]→ Γ′)
sub-skip T σ x = σ (`S x)
\end{code}
%<*kits>
\begin{code}
record VarSubstKit (T : Context → Type → Set) : Set where
  field
    vr : ∀ {Γ A} → Γ ∋ A → T Γ A
    wk : ∀ {Γ A B} → T Γ A → T (Γ , B) A

record TermSubstKit (T : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → T Γ Θ A → Γ ⟶ Θ ∣ A
    kit : ∀ {Θ}        → VarSubstKit (λ Γ A → T Γ Θ A)
    wkΘ : ∀ {Γ Θ A B}   → T Γ Θ A → T Γ (Θ , B) A
  open module K {Θ} = VarSubstKit (kit {Θ}) renaming (wk to wkΓ) public

record CotermSubstKit (C : Context → Context → Type → Set) : Set where
  field
    tm : ∀ {Γ Θ A}     → C Γ Θ A → A ∣ Γ ⟶ Θ
    wkΓ : ∀ {Γ Θ A B}   → C Γ Θ A → C (Γ , B) Θ A
    kit : ∀ {Γ}        → VarSubstKit (λ Θ A → C Γ Θ A)
  open module K {Γ} = VarSubstKit (kit {Γ}) renaming (wk to wkΘ) public
\end{code}
%</kits>

%<*ren-weaken>
\begin{code}
rename-weaken : ∀ {Γ Δ A} → Γ ↝ Δ → Γ ↝ (Δ , A)
\end{code}
%</ren-weaken>
\begin{code}
rename-weaken ρ x = `S (ρ x)
\end{code}

%<*ren-lift>
\begin{code}
rename-lift : ∀ {Γ Δ A} → Γ ↝ Δ → (Γ , A) ↝ (Δ , A)
rename-lift ρ `Z = `Z
rename-lift ρ (`S x) = `S (ρ x)
\end{code}
%</ren-lift>

%<*renty>
\begin{code}
rename-term : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
rename-coterm : ∀ {Γ Γ′ Θ Θ′ A} → Γ ↝ Γ′ → Θ ↝ Θ′ → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
rename-statement : ∀ {Γ Γ′ Θ Θ′} → Γ ↝ Γ′ → Θ ↝ Θ′ → Γ ↦ Θ → Γ′ ↦ Θ′
\end{code}
%</renty>

%<*renvar>
\begin{code}
rename-term ρ ϱ (` x) = ` (ρ x)
\end{code}
%</renvar>
\begin{code}
rename-term ρ ϱ `⟨ M , N ⟩ = `⟨ (rename-term ρ ϱ M) , rename-term ρ ϱ N ⟩
rename-term ρ ϱ inr⟨ M ⟩ = inr⟨ rename-term ρ ϱ M ⟩
rename-term ρ ϱ inl⟨ M ⟩ = inl⟨ rename-term ρ ϱ M ⟩
rename-term ρ ϱ not[ K ] = not[ rename-coterm ρ ϱ K ]
\end{code}
%<*rencovarabs>
\begin{code}
rename-term ρ ϱ (μθ S) = μθ (rename-statement ρ (rename-lift ϱ) S)
\end{code}
%</rencovarabs>

%<*rencovar>
\begin{code}
rename-coterm ρ ϱ (` α) = ` (ϱ α)
\end{code}
%</rencovar>
\begin{code}
rename-coterm ρ ϱ fst[ K ] = fst[ rename-coterm ρ ϱ K ]
rename-coterm ρ ϱ snd[ K ] = snd[ rename-coterm ρ ϱ K ]
rename-coterm ρ ϱ `[ K , L ] = `[ rename-coterm ρ ϱ K , rename-coterm ρ ϱ L ]
rename-coterm ρ ϱ not⟨ M ⟩ = not⟨ (rename-term ρ ϱ M) ⟩
\end{code}
%<*renvarabs>
\begin{code}
rename-coterm ρ ϱ (μγ S) = μγ (rename-statement (rename-lift ρ) ϱ S)
\end{code}
%</renvarabs>

\begin{code}
rename-statement ρ ϱ (M ● K) = (rename-term ρ ϱ M) ● (rename-coterm ρ ϱ K) 


VarKit : VarSubstKit _∋_ 
VarKit = record 
  {  vr = λ a → a
  ;  wk = `S
  } 

\end{code}
%<*subweaken>
\begin{code}
sub-weaken : ∀ {Γ Δ A T} → VarSubstKit T → Γ –[ T ]→ Δ → Γ –[ T ]→ (Δ , A)
sub-weaken k σ x = VarSubstKit.wk k (σ x)
\end{code}
%</subweaken>
%<*sublift>
\begin{code}
sub-lift : ∀ {Γ Δ A T} → VarSubstKit T → Γ –[ T ]→ Δ → (Γ , A) –[ T ]→ (Δ , A)
sub-lift k σ `Z = VarSubstKit.vr k `Z
sub-lift k σ (`S x) = sub-weaken k σ x
\end{code}
%</sublift>
\begin{code}
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
\end{code}

%<*fmap>
\begin{code}
fmap : ∀ {T T′ Γ Γ′} (f : ∀ {Γ A} → T Γ A → T′ Γ A) → Γ –[ T ]→ Γ′ → Γ –[ T′ ]→ Γ′
fmap f σ `x = f (σ `x)
\end{code}
%</fmap>

%<*subty>
\begin{code}
sub-term : ∀ {T A C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C 
  → Γ –[ (λ Γ A → T Γ Θ′ A) ]→ Γ′ → Θ –[ (λ Θ A → C Γ′ Θ A) ]→ Θ′ 
  → Γ ⟶ Θ ∣ A → Γ′ ⟶ Θ′ ∣ A
sub-coterm : ∀ {T A C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C 
  → Γ –[ (λ Γ A → T Γ Θ′ A) ]→ Γ′ → Θ –[ (λ Θ A → C Γ′ Θ A) ]→ Θ′ 
  → A ∣ Γ ⟶ Θ → A ∣ Γ′ ⟶ Θ′
sub-statement : ∀ {T C Γ Θ Γ′ Θ′} → TermSubstKit T → CotermSubstKit C 
  → Γ –[ (λ Γ A → T Γ Θ′ A) ]→ Γ′ → Θ –[ (λ Θ A → C Γ′ Θ A) ]→ Θ′ 
  → Γ ↦ Θ → Γ′ ↦ Θ′
\end{code}
%</subty>
%<*subvar>
\begin{code}
sub-term k₁ k₂ s t (` x) = TermSubstKit.tm k₁ (s x)
\end{code}
%</subvar>
\begin{code}
sub-term k₁ k₂ s t `⟨ M , N ⟩ = `⟨ sub-term k₁ k₂ s t M , sub-term k₁ k₂ s t N ⟩
sub-term k₁ k₂ s t inl⟨ M ⟩ = inl⟨ sub-term k₁ k₂ s t M ⟩
sub-term k₁ k₂ s t inr⟨ M ⟩ = inr⟨ sub-term k₁ k₂ s t M ⟩
sub-term k₁ k₂ s t not[ K ] = not[ sub-coterm k₁ k₂ s t K ]
\end{code}
%<*subcovarabs>
\begin{code}
sub-term {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μθ S) = μθ (sub-statement k₁ k₂ 
  (fmap {λ - → T - Θ′} {λ - → T - (Θ′ , A)} (λ x → TermSubstKit.wkΘ k₁ x) s) 
  (sub-lift (CotermSubstKit.kit k₂) t) S)
\end{code}
%</subcovarabs>

%<*subcovar>
\begin{code}
sub-coterm k₁ k₂ s t (` α) = CotermSubstKit.tm k₂ (t α)
\end{code}
%</subcovar>
\begin{code}
sub-coterm k₁ k₂ s t fst[ K ] = fst[ sub-coterm k₁ k₂ s t K ]
sub-coterm k₁ k₂ s t snd[ K ] = snd[ sub-coterm k₁ k₂ s t K ]
sub-coterm k₁ k₂ s t `[ K , L ] = `[ sub-coterm k₁ k₂ s t K , sub-coterm k₁ k₂ s t L ]
sub-coterm k₁ k₂ s t not⟨ M ⟩ = not⟨ (sub-term k₁ k₂ s t M) ⟩
\end{code}
%<*subvarabs>
\begin{code}
sub-coterm {T}{A}{C}{Γ}{Θ}{Γ′}{Θ′} k₁ k₂ s t (μγ S) = μγ (sub-statement k₁ k₂ 
  (sub-lift (TermSubstKit.kit k₁) s) 
  (fmap {C Γ′} {C (Γ′ , A)} (λ x → CotermSubstKit.wkΓ k₂ x) t) S)
\end{code}
%</subvarabs>

\begin{code}
sub-statement k₁ k₂ s t (M ● K) = (sub-term k₁ k₂ s t M) ● (sub-coterm k₁ k₂ s t K)


TermKit : TermSubstKit _⟶_∣_ 
TermKit = record 
  {  tm = λ a → a
  ;  wkΘ = rename-term id-var (rename-weaken id-var)
  ;  kit = record { vr = `_ ; wk = rename-term (rename-weaken id-var) id-var }
  }
\end{code}

%<*cotermkit>
\begin{code}
CotermKit : CotermSubstKit λ Γ Θ A → A ∣ Γ ⟶ Θ
CotermKit = record
  {  tm = λ a → a 
  ;  wkΓ = rename-coterm (rename-weaken id-var) id-var
  ;  kit = record { vr = `_ ; wk = rename-coterm id-var (rename-weaken id-var) }
  }
\end{code}
%</cotermkit>

%<*valren>
\begin{code}
value-rename : ∀ {Γ Γ′ Θ Θ′ A} {V : Γ ⟶ Θ ∣ A} {ρ : Γ ↝ Γ′} {ϱ : Θ ↝ Θ′} →
  Value V → Value (rename-term ρ ϱ V)
\end{code}
%</valren>
\begin{code}
value-rename V-var = V-var
value-rename (V-prod v w) = V-prod (value-rename v) (value-rename w)
value-rename (V-inl v) = V-inl (value-rename v)
value-rename (V-inr v) = V-inr (value-rename v)
value-rename V-not = V-not  
\end{code}

%<*covalren>
\begin{code}
covalue-rename : ∀ {Γ Γ′ Θ Θ′ A} {P : A ∣ Γ ⟶ Θ} (ρ : Γ ↝ Γ′) (ϱ : Θ ↝ Θ′) →
  Covalue P → Covalue (rename-coterm ρ ϱ P)
\end{code}
%</covalren>
\begin{code}
covalue-rename ρ ϱ CV-covar = CV-covar
covalue-rename ρ ϱ (CV-sum p q) = CV-sum (covalue-rename ρ ϱ p) (covalue-rename ρ ϱ q)
covalue-rename ρ ϱ (CV-fst p) = CV-fst (covalue-rename ρ ϱ p)
covalue-rename ρ ϱ (CV-snd p) = CV-snd (covalue-rename ρ ϱ p)
covalue-rename ρ ϱ CV-not = CV-not
\end{code}

%<*termvalkit>
\begin{code}
TermValueKit : TermSubstKit TermValue
TermValueKit = record
  { tm = λ x → proj₁ x
  ; wkΘ = λ x → ⟨ (TermSubstKit.wkΘ TermKit (proj₁ x)) 
                , value-rename (proj₂ x) ⟩
  ; kit = record 
    { vr = λ x → ⟨ ` x , V-var ⟩ 
    ; wk = λ x → ⟨ (VarSubstKit.wk (TermSubstKit.kit TermKit) (proj₁ x)) 
                 , value-rename (proj₂ x) ⟩ }
  }
\end{code}
%</termvalkit>
\begin{code}
CotermValueKit : CotermSubstKit CotermValue
CotermValueKit = record 
  { tm = λ x → proj₁ x 
  ; wkΓ = λ x → ⟨ (CotermSubstKit.wkΓ CotermKit (proj₁ x)) 
                , covalue-rename (rename-weaken id-var) id-var (proj₂ x) ⟩ 
  ; kit = record 
    { vr = λ x → ⟨ (` x) , CV-covar ⟩ 
    ; wk = λ x → ⟨ (VarSubstKit.wk (CotermSubstKit.kit CotermKit) (proj₁ x)) 
                , (covalue-rename id-var (rename-weaken id-var) (proj₂ x)) ⟩ } 
  }
\end{code}

\begin{code}
wkΓᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ , B ⟶ Θ ∣ A
wkΓᵗ = TermSubstKit.wkΓ TermKit

wkΘᵗ : ∀ {Γ Θ A B} → Γ ⟶ Θ ∣ A → Γ ⟶ Θ , B ∣ A
wkΘᵗ = TermSubstKit.wkΘ TermKit

wkΓᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ , B ⟶ Θ
wkΓᶜ = CotermSubstKit.wkΓ CotermKit

wkΘᶜ : ∀ {Γ Θ A B} → A ∣ Γ ⟶ Θ → A ∣ Γ ⟶ Θ , B
wkΘᶜ = CotermSubstKit.wkΘ CotermKit

wkΓᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue (Γ , B) Θ A
wkΓᶜⱽ = CotermSubstKit.wkΓ CotermValueKit

wkΘᶜⱽ : ∀ {Γ Θ A B} → CotermValue Γ Θ A → CotermValue Γ (Θ , B) A
wkΘᶜⱽ = CotermSubstKit.wkΘ CotermValueKit

intΓᵗ : ∀ {Γ Θ A B C} → Γ , A , B ⟶ Θ ∣ C → Γ , B , A ⟶ Θ ∣ C
intΓᵗ M = rename-term (add _∋_ (`S `Z) (rename-lift (rename-weaken id-var))) id-var M
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
--   → sub-var (fmap (rename-coterm VarKit ((weaken) VarKit id-var) id-var) s) x ≡ rename-coterm VarKit (weaken VarKit id-var) id-var (sub-var s x)
-- sub-fmap (s , s′) `Z = refl
-- sub-fmap (s , s′) (`S x) = sub-fmap s x

-- fmap++ : ∀ {Γ Θ Θ′ Θ″} (s : Subst (λ -₁ -₂ → -₂ ∣ Γ ⟶ -₁) Θ Θ′) (t : Subst _∋_ Θ′ Θ″) 
--   → (fmap (rename-coterm VarKit ((weaken) VarKit id-var) id-var) s ++ t) ≡ fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) (s ++ t)
-- fmap++ s ⨀ = refl
-- fmap++ s (_,_ t t′) = cong₂ _,_ (fmap++ s t) (sub-fmap s t′)

-- lemma : ∀ {Γ Γ′ Γ″ Θ} (s : Subst (λ -₁ -₂ → -₁ ⟶ Θ ∣ -₂) Γ Γ′) (t : Subst _∋_ Γ′ Γ″)
--   → ((exts (TermSubstKit.kit TermKit) s ++ weaken VarKit t) , (` `Z)) ≡ exts (TermSubstKit.kit TermKit) (s ++ t)

-- lemma s ⨀ = refl
-- lemma s (t , x) = cong₂ _,_ ({!   !}) refl

-- lemma : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (s : Subst (λ -₁ → _⟶_∣_ -₁ Θ) Γ Γ′) (t : Subst (λ -₁ -₂ → -₂ ∣ Γ ⟶ -₁) Θ Θ′) (u : Subst _∋_ Γ′ Γ″) (v : Subst _∋_ Θ′ Θ″) (S : Γ″ ↦ Θ″ , A)
--     → sub-statement TermKit CotermKit
--       ((exts (CotermSubstKit.kit CotermKit) s ++ weaken VarKit u) , (` `Z))
--       (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) t ++ v)
--       S
--       ≡
--       sub-statement TermKit CotermKit
--       (fmap (rename-term VarKit id-var (weaken VarKit id-var)) (s ++ u))
--       (exts (CotermSubstKit.kit CotermKit) (t ++ v))
--       S
-- lemma s t u v S = trans {! sub-ren-statement  !} {!   !}
    

-- sub-ren-term : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (M : Γ ⟶ Θ ∣ A) (s : Γ′ –[ (λ -₁ -₂ → -₁ ⟶ Θ″ ∣ -₂) ]→ Γ″) (t : Θ′ –[ (λ -₁ -₂ → -₂ ∣ Γ″ ⟶ -₁) ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-term TermKit CotermKit s t (rename-term u v M) ≡ sub-term TermKit CotermKit (u ++ s) (v ++ t) M

-- sub-ren-coterm : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″ A} (K : A ∣ Γ ⟶ Θ) (s : Γ′ –[ (λ -₁ -₂ → -₁ ⟶ Θ″ ∣ -₂) ]→ Γ″) (t : Θ′ –[ (λ -₁ -₂ → -₂ ∣ Γ″ ⟶ -₁) ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-coterm TermKit CotermKit s t (rename-coterm u v K) ≡ sub-coterm TermKit CotermKit (u ++ s) (v ++ t) K

-- sub-ren-statement : ∀ {Γ Γ′ Γ″ Θ Θ′ Θ″} (S : Γ ↦ Θ) (s : Γ′ –[ (λ -₁ -₂ → -₁ ⟶ Θ″ ∣ -₂) ]→ Γ″) (t : Θ′ –[ (λ -₁ -₂ → -₂ ∣ Γ″ ⟶ -₁) ]→ Θ″) (u : Γ ↝ Γ′) (v : Θ ↝ Θ′)
--   → sub-statement TermKit CotermKit s t (rename-statement u v S) ≡ sub-statement TermKit CotermKit (u ++ s) (v ++ t) S

-- sub-ren-term (` x) s t u v = refl
-- sub-ren-term `⟨ M , N ⟩ s t u v = cong₂ `⟨_,_⟩ (sub-ren-term M s t u v) (sub-ren-term N s t u v)
-- sub-ren-term inl⟨ M ⟩ s t u v = cong inl⟨_⟩ (sub-ren-term M s t u v)
-- sub-ren-term inr⟨ M ⟩ s t u v = cong inr⟨_⟩ (sub-ren-term M s t u v)
-- sub-ren-term not[ K ] s t u v = cong not[_](sub-ren-coterm K s t u v)
-- sub-ren-term (μθ S) s t u v = cong μθ 
--   (begin 
--     sub-statement TermKit CotermKit
--       (fmap (rename-term (id-var) (rename-weaken id-var)) s)
--       (sub-lift (CotermSubstKit.kit CotermKit) t)
--       (rename-statement u (rename-lift v) S)
--   ≡⟨ sub-ren-statement S (fmap (rename-term id-var (rename-weaken id-var)) s) (sub-lift (CotermSubstKit.kit CotermKit) t) u (rename-lift v) ⟩
--     sub-statement TermKit CotermKit
--       (u ++ fmap (TermSubstKit.wkΘ TermKit) s)
--       (rename-lift v ++ sub-lift (CotermSubstKit.kit CotermKit) t) S
--   ≡⟨ cong (λ x → sub-statement TermKit CotermKit (u ++ fmap (TermSubstKit.wkΘ TermKit) s) x S) {!   !} ⟩
--     {!  !})

-- sub-ren-coterm (` α) s t u v = refl
-- sub-ren-coterm fst[ K ] s t u v = cong fst[_] (sub-ren-coterm K s t u v)
-- sub-ren-coterm snd[ K ] s t u v = cong snd[_] (sub-ren-coterm K s t u v)
-- sub-ren-coterm `[ K , L ] s t u v = cong₂ `[_,_] (sub-ren-coterm K s t u v) (sub-ren-coterm L s t u v)
-- sub-ren-coterm not⟨ M ⟩ s t u v = cong not⟨_⟩ (sub-ren-term M s t u v)
-- sub-ren-coterm (μγ S) s t u v = cong μγ ({!   !})
-- --   (begin
-- --     sub-statement TermKit CotermKit
-- --       (exts (TermSubstKit.kit TermKit) s)
-- --       (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) t)
-- --       (rename-statement VarKit (exts VarKit u) v S)
-- --   ≡⟨ sub-ren-statement S (exts (TermSubstKit.kit TermKit) s) (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) t) (exts VarKit u) v ⟩
-- --     sub-statement TermKit CotermKit
-- --       ((exts (TermSubstKit.kit TermKit) s ++ weaken VarKit u) , (` `Z))
-- --       (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) t ++ v)
-- --       S
-- --   ≡⟨ cong (λ x → sub-statement TermKit CotermKit ((exts (TermSubstKit.kit TermKit) s ++ weaken VarKit u) , ` `Z) x S)  (fmap++ t v) ⟩ 
-- --     sub-statement TermKit CotermKit
-- --       ((exts (TermSubstKit.kit TermKit) s ++ weaken VarKit u) , (` `Z))
-- --       (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) (t ++ v))
-- --       S
-- --   ≡⟨ cong (λ x → sub-statement TermKit CotermKit x (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) (t ++ v)) S) {!    !} ⟩
-- --     sub-statement TermKit CotermKit
-- --       (exts (TermSubstKit.kit TermKit) (s ++ u))
-- --       (fmap (rename-coterm VarKit (weaken VarKit id-var) id-var) (t ++ v))
-- --       S
-- --   ∎)

-- sub-ren-statement (M ● K) s t u v = cong₂ _●_ (sub-ren-term M s t u v) (sub-ren-coterm K s t u v)