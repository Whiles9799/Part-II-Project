\begin{code}
{-# OPTIONS --rewriting #-}

module fragments.Duality where

open import Dual.Syntax.Core
open import Dual.Syntax.Values
open import Dual.Syntax.Substitution
open import Dual.Syntax.Duality
open import Dual.OperationalSemantics.CBVReduction
open import Dual.OperationalSemantics.CBNReduction
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎) 
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Function.Bundles using (Inverse)

variable
  Γ Γ′ Θ Θ′ : Context
  A : Type

dual-ren-weaken-lemma : ∀ {A B} Γ Γ′ (ρ : Γ ↝ Γ′) (x : Γ ᵒˣ ∋ A) →  dual-ren Γ (Γ′ , B) (ren-weaken ρ) x ≡ (ren-weaken (dual-ren Γ Γ′ ρ)) x
dual-ren-weaken-lemma (Γ , C) Γ′ ρ `Z = refl
dual-ren-weaken-lemma (Γ , C) Γ′ ρ (`S x) = dual-ren-weaken-lemma Γ Γ′ (λ z → ρ (`S z)) x

dual-ren-id-lemma : ∀ Γ {A} (x : Γ ᵒˣ ∋ A) → (dual-ren Γ Γ id-var) x ≡ id-var x
dual-ren-id-lemma (Γ , B) `Z = refl
dual-ren-id-lemma (Γ , B) (`S x) =  trans (dual-ren-weaken-lemma Γ Γ id-var x) (cong `S (dual-ren-id-lemma Γ  x))

dual-ren-lift-lemma : ∀ {A B} Γ Γ′ (ρ : Γ ↝ Γ′) (x : Γ ᵒˣ , B ᵒᵀ ∋ A) → dual-ren (Γ , B) (Γ′ , B) (ren-lift ρ) x ≡ (ren-lift (dual-ren Γ Γ′ ρ)) x
dual-ren-lift-lemma Γ Γ′ ρ `Z = refl
dual-ren-lift-lemma {A}{B} Γ Γ′ ρ (`S x) = dual-ren-weaken-lemma Γ Γ′ ρ x
  
dual-ren-lemma-var : ∀ {Γ Γ′ A} (x : Γ ∋ A) (ρ : Γ ↝ Γ′) → ρ x ᵒⱽ ≡ dual-ren Γ Γ′ ρ (x ᵒⱽ)
dual-ren-lemma-var `Z ρ = refl
dual-ren-lemma-var (`S x) ρ = dual-ren-lemma-var x (λ z → ρ (`S z))

dual-ren-lemma-T : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) → (ren-T s t M ᵒᴸ) ≡ ren-C (dual-ren Θ Θ′ t) (dual-ren Γ Γ′ s) (M ᵒᴸ)
dual-ren-lemma-C : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) → (ren-C s t K ᵒᴿ) ≡ ren-T (dual-ren Θ Θ′ t) (dual-ren Γ Γ′ s) (K ᵒᴿ)
dual-ren-lemma-S : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) → (ren-S s t S ᵒˢ) ≡ ren-S (dual-ren Θ Θ′ t) (dual-ren Γ Γ′ s) (S ᵒˢ)

dual-ren-lemma-T (` x) s t = cong `_ (dual-ren-lemma-var x s)
dual-ren-lemma-T `⟨ M , N ⟩ s t = cong₂ `[_,_] (dual-ren-lemma-T M s t) (dual-ren-lemma-T N s t)
dual-ren-lemma-T inl⟨ M ⟩ s t = cong fst[_] (dual-ren-lemma-T M s t)
dual-ren-lemma-T inr⟨ M ⟩ s t = cong snd[_] (dual-ren-lemma-T M s t)
dual-ren-lemma-T not[ K ] s t = cong not⟨_⟩ (dual-ren-lemma-C K s t)
dual-ren-lemma-T {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t = cong μγ 
  (trans (dual-ren-lemma-S S s (ren-lift t)) (cong (λ - → - (dual-ren Γ Γ′ s) (S ᵒˢ)) (cong ren-S (iext (ext λ x → dual-ren-lift-lemma Θ Θ′ t x)))))

dual-ren-lemma-C (` α) s t = cong `_ (dual-ren-lemma-var α t)
dual-ren-lemma-C fst[ K ] s t = cong inl⟨_⟩ (dual-ren-lemma-C K s t)
dual-ren-lemma-C snd[ K ] s t = cong inr⟨_⟩ (dual-ren-lemma-C K s t)
dual-ren-lemma-C `[ K , L ] s t = cong₂ `⟨_,_⟩ (dual-ren-lemma-C K s t) (dual-ren-lemma-C L s t)
dual-ren-lemma-C not⟨ M ⟩ s t = cong not[_] (dual-ren-lemma-T M s t)
dual-ren-lemma-C {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t = cong μθ 
  (trans (dual-ren-lemma-S S (ren-lift s) t) (cong (λ - → - (S ᵒˢ)) (cong (ren-S (dual-ren Θ Θ′ t)) (iext (ext (λ x → dual-ren-lift-lemma Γ Γ′ s x))))))

dual-ren-lemma-S (M ● K) s t = cong₂ _●_ (dual-ren-lemma-C K s t) (dual-ren-lemma-T M s t)
\end{code}
%<*cv-eq>
\begin{code}
CV-eq : ∀ {Γ Θ A} {K L : Coterm Γ Θ A} (K-V : Covalue K) (L-V : Covalue L) 
  → (e : K ≡ L) → subst Covalue e K-V ≡ L-V
\end{code}
%</cv-eq>
\begin{code}
CV-eq CV-covar CV-covar refl = refl
CV-eq (CV-fst K-V) (CV-fst L-V) refl = cong CV-fst (CV-eq K-V L-V refl)
CV-eq (CV-snd K-V) (CV-snd L-V) refl = cong CV-snd (CV-eq K-V L-V refl)
CV-eq (CV-sum K₁-V K₂-V) (CV-sum L₁-V L₂-V) refl = cong₂ CV-sum (CV-eq K₁-V L₁-V refl) (CV-eq K₂-V L₂-V refl)
CV-eq CV-not CV-not refl = refl
\end{code}
%<*ctv-eq>
\begin{code}
CTV-eq : ∀{Γ Θ A}{K L : Coterm Γ Θ A}(K-V : Covalue K)(L-V : Covalue L)
  → (e : K ≡ L) → ⟨ K , K-V ⟩ ≡ ⟨ L , L-V ⟩
CTV-eq K-V L-V e = Inverse.f Σ-≡,≡↔≡ ⟨ e , CV-eq K-V L-V e ⟩
\end{code}
%</ctv-eq>
%<*weaken>
\begin{code}
dual-sub-TV-weaken-lemma : ∀ Γ Γ′ Θ′ A {B} (σ : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (x : Γ ᵒˣ ∋ B) 
  → dual-sub-TV Γ (Γ′ , A) Θ′ (sub-weaken (TVK.kit) σ) x
    ≡ sub-weaken (CVK.kit) (dual-sub-TV Γ Γ′ Θ′ σ) x
\end{code}
%</weaken>
\begin{code}
dual-sub-TV-weaken-lemma (Γ , C) Γ′ Θ′ A σ `Z = CTV-eq 
  (Vᵒ≡P (ren-T (ren-weaken id-var) id-var (proj₁ (σ `Z))) (V-ren (ren-weaken id-var) id-var (proj₂ (σ `Z)))) 
  (CV-ren id-var (ren-weaken id-var) (Vᵒ≡P (proj₁ (σ `Z)) (proj₂ (σ `Z)))) 
  ((trans 
    (dual-ren-lemma-T (proj₁ (σ `Z)) (ren-weaken (λ z → z)) (λ x → x)) 
    (cong₂ (λ -₁ -₂ → ren-C (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (proj₁ (σ `Z) ᵒᴸ)) 
      (iext (ext (λ x → dual-ren-id-lemma Θ′ x)))
      (iext (ext (λ x → trans (dual-ren-weaken-lemma Γ′ Γ′ (λ z → z) x) (cong `S (dual-ren-id-lemma Γ′ x))))))))
dual-sub-TV-weaken-lemma (Γ , C) Γ′ Θ′ A σ (`S x) = dual-sub-TV-weaken-lemma Γ Γ′ Θ′ A (sub-skip (Fix₂ TermValue Θ′) σ) x

\end{code}
%<*lift>
\begin{code}
dual-sub-TV-lift-lemma : ∀ Γ Γ′ Θ′ A {B} (σ : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (x : (Γ , A) ᵒˣ ∋ B)
  → dual-sub-TV (Γ , A) (Γ′ , A) Θ′ (sub-lift (TVK.kit) σ) x
    ≡ sub-lift (CVK.kit) (dual-sub-TV Γ Γ′ Θ′ σ) x
\end{code}
%</lift>
\begin{code}
dual-sub-TV-lift-lemma Γ Γ′ Θ′ A σ `Z = refl
dual-sub-TV-lift-lemma Γ Γ′ Θ′ A σ (`S x) = dual-sub-TV-weaken-lemma Γ Γ′ Θ′ A σ x

\end{code}
%<*fmap>
\begin{code}
dual-sub-TV-fmap-lemma : ∀ Γ Γ′ Θ′ A {B} (σ : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (x : Γ ᵒˣ ∋ B)
  → dual-sub-TV Γ Γ′ (Θ′ , A) (fmap-wkΘᵗⱽ Θ′ A σ) x 
    ≡ fmap-wkΓᶜⱽ (Θ′ ᵒˣ) (A ᵒᵀ) (dual-sub-TV Γ Γ′ Θ′ σ) x
\end{code}
%</fmap>
\begin{code}
dual-sub-TV-fmap-lemma (Γ , C) Γ′ Θ′ A σ `Z = CTV-eq 
  (Vᵒ≡P (ren-T id-var (ren-weaken id-var) (proj₁ (σ `Z))) (V-ren id-var (ren-weaken id-var) (proj₂ (σ `Z)))) 
  (CV-ren (ren-weaken id-var) id-var (Vᵒ≡P (proj₁ (σ `Z)) (proj₂ (σ `Z)))) 
  ((trans 
    (dual-ren-lemma-T (proj₁ (σ `Z)) (λ z → z) (ren-weaken (λ z → z))) 
    (cong₂ (λ -₁ -₂ → ren-C (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (proj₁ (σ `Z) ᵒᴸ))
      (iext (λ {A} → ext (λ x → trans (dual-ren-weaken-lemma Θ′ Θ′ (λ z → z) x) (cong `S (dual-ren-id-lemma Θ′ x))))) 
      (iext (ext (λ x → dual-ren-id-lemma Γ′ x))))))
dual-sub-TV-fmap-lemma (Γ , C) Γ′ Θ′ A σ (`S x) = dual-sub-TV-fmap-lemma Γ Γ′ Θ′ A (sub-skip (Fix₂ TermValue Θ′) σ) x
\end{code}

%<*id>
\begin{code}
dual-sub-TV-id-lemma : ∀ Γ Θ A (x : Γ ᵒˣ ∋ A)
  → dual-sub-TV Γ Γ Θ id-TV x ≡ id-CV x
\end{code}
%</id>
\begin{code}
dual-sub-TV-id-lemma (Γ , B) Θ A `Z = refl 
dual-sub-TV-id-lemma (Γ , B) Θ A (`S x) = 
  trans 
    (dual-sub-TV-weaken-lemma Γ Γ Θ B id-TV x)
    (CTV-eq 
      (CV-ren (λ z → z) (ren-weaken (λ z → z)) (proj₂ (dual-sub-TV Γ Γ Θ id-TV x)))
      CV-covar 
      (cong (ren-C (λ x → x) (ren-weaken (λ x → x))) (cong proj₁ (dual-sub-TV-id-lemma Γ Θ A x)))) 
\end{code}

%<*add>
\begin{code}
dual-sub-TV-add-lemma : ∀ Γ Θ A {B} (V : Term Γ Θ A) (v : Value V) (x : (Γ , A) ᵒˣ ∋ B)
  → dual-sub-TV (Γ , A) Γ Θ (add (Fix₂ TermValue Θ) ⟨ V , v ⟩ id-TV) x
    ≡ add (Fix₁ CotermValue (Θ ᵒˣ)) ⟨ V ᵒᴸ , Vᵒ≡P V v ⟩ id-CV x
\end{code}
%</add>
\begin{code}
dual-sub-TV-add-lemma Γ Θ A V v `Z = refl
dual-sub-TV-add-lemma Γ Θ A {B} V v (`S x) = dual-sub-TV-id-lemma Γ Θ B x

dual-sub-C-weaken-lemma : ∀ Γ′ Θ Θ′ A {B} (σ : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) (x : Θ ᵒˣ ∋ B) 
  → dual-sub-C Γ′ Θ (Θ′ , A) (sub-weaken (CK.kit) σ) x
    ≡ sub-weaken (TK.kit) (dual-sub-C Γ′ Θ Θ′ σ) x
dual-sub-C-weaken-lemma Γ′ (Θ , C) Θ′ A σ `Z = 
  trans 
    (dual-ren-lemma-C (σ `Z) (λ z → z) (ren-weaken (λ z → z))) 
    (cong₂ (λ -₁ -₂ → ren-T (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (σ `Z ᵒᴿ))
      (iext (ext (λ x → trans (dual-ren-weaken-lemma Θ′ Θ′ id-var x) (cong `S (dual-ren-id-lemma Θ′ x))))) 
      (iext (ext (λ x → dual-ren-id-lemma Γ′ x))))
dual-sub-C-weaken-lemma Γ′ (Θ , C) Θ′ A σ (`S x) = dual-sub-C-weaken-lemma Γ′ Θ Θ′ A (sub-skip (Fix₁ Coterm Γ′) σ) x

dual-sub-C-lift-lemma : ∀ Γ′ Θ Θ′ A {B} (σ : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) (x : (Θ , A) ᵒˣ ∋ B)
  → dual-sub-C Γ′ (Θ , A) (Θ′ , A) (sub-lift (CK.kit) σ) x
      ≡ sub-lift (TK.kit) (dual-sub-C Γ′ Θ Θ′ σ) x
dual-sub-C-lift-lemma Γ′ Θ Θ′ A σ `Z = refl
dual-sub-C-lift-lemma Γ′ Θ Θ′ A σ (`S x) = dual-sub-C-weaken-lemma Γ′ Θ Θ′ A σ x

dual-sub-C-fmap-lemma : ∀ Γ′ Θ Θ′ A {B} (σ : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) (x : Θ ᵒˣ ∋ B)
  → dual-sub-C (Γ′ , A) Θ Θ′ (fmap-wkΓᶜ Γ′ A σ) x
    ≡ fmap-wkΘᵗ (Γ′ ᵒˣ) (A ᵒᵀ) (dual-sub-C Γ′ Θ Θ′ σ) x
dual-sub-C-fmap-lemma Γ′ (Θ , C) Θ′ A {B} σ `Z = 
  trans 
    (dual-ren-lemma-C (σ `Z) (ren-weaken (λ z → z)) (λ z → z))
    (cong₂ (λ -₁ -₂ → ren-T (λ { {A} → -₁ {A} }) (λ { {A} → -₂ {A} }) (σ `Z ᵒᴿ))
      (iext (ext (λ x → dual-ren-id-lemma Θ′ x))) 
      (iext (ext (λ x → trans (dual-ren-weaken-lemma Γ′ Γ′ id-var x) (cong `S (dual-ren-id-lemma Γ′ x))))))
dual-sub-C-fmap-lemma Γ′ (Θ , C) Θ′ A σ (`S x) = dual-sub-C-fmap-lemma Γ′ Θ Θ′ A (sub-skip (Fix₁ Coterm Γ′) σ) x

dual-sub-C-id-lemma : ∀ Γ Θ A (x : Θ ᵒˣ ∋ A)
  → dual-sub-C Γ Θ Θ id-C x ≡ id-T x 
dual-sub-C-id-lemma Γ (Θ , B) .(B ᵒᵀ) `Z = refl
dual-sub-C-id-lemma Γ (Θ , B) A (`S x) = 
  trans 
    (dual-sub-C-weaken-lemma Γ Θ Θ B `_ x) 
    (cong (ren-T (λ x₁ → `S x₁) (λ x₁ → x₁)) (dual-sub-C-id-lemma Γ Θ A x))


dual-sub-C-add-lemma : ∀ Γ Θ A B (K : Coterm Γ Θ A) (x : (Θ , A) ᵒˣ ∋ B)
  → dual-sub-C Γ (Θ , A) Θ (add (Fix₁ Coterm Γ) K id-C) x
    ≡ add (Fix₂ Term (Γ ᵒˣ)) (K ᵒᴿ) id-T x
dual-sub-C-add-lemma Γ Θ A B K `Z = refl
dual-sub-C-add-lemma Γ Θ A B K (`S x) = dual-sub-C-id-lemma Γ Θ B x


dual-sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (x : Γ ∋ A) (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) →
  proj₁ (s x) ᵒᴸ ≡ proj₁ (dual-sub-TV Γ Γ′ Θ′ s (x ᵒⱽ))
dual-sub-lemma-var `Z s = refl
dual-sub-lemma-var {Γ}{Γ′}{Θ′} (`S x) s = dual-sub-lemma-var x (sub-skip (Fix₂ TermValue Θ′) s)

dual-sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (α : Θ ∋ A) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) →
  t α ᵒᴿ ≡ dual-sub-C Γ′ Θ Θ′ t (α ᵒⱽ)
dual-sub-lemma-covar `Z t = refl
dual-sub-lemma-covar {Γ′} (`S α) t = dual-sub-lemma-covar α (sub-skip (Fix₁ Coterm Γ′) t)

\end{code}

%<*dual-sub-lemma>
\begin{code}
dual-sub-lemma-T : ∀ (M : Γ ⟶ Θ ∣ A) (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  → (sub-T TVK CK s t M) ᵒᴸ ≡ sub-C TK CVK (dual-sub-C Γ′ Θ Θ′ t) (dual-sub-TV Γ Γ′ Θ′ s) (M ᵒᴸ)
dual-sub-lemma-C : ∀ (K : A ∣ Γ ⟶ Θ) (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  → (sub-C TVK CK s t K) ᵒᴿ ≡ sub-T TK CVK (dual-sub-C Γ′ Θ Θ′ t) (dual-sub-TV Γ Γ′ Θ′ s) (K ᵒᴿ)
dual-sub-lemma-S : ∀ (S : Γ ↦ Θ) (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  → (sub-S TVK CK s t S) ᵒˢ ≡ sub-S TK CVK (dual-sub-C Γ′ Θ Θ′ t) (dual-sub-TV Γ Γ′ Θ′ s) (S ᵒˢ)
\end{code}
%</dual-sub-lemma>

\begin{code}

dual-sub-lemma-T (` x) s t = dual-sub-lemma-var x s
dual-sub-lemma-T `⟨ M , N ⟩ s t = cong₂ `[_,_] (dual-sub-lemma-T M s t) (dual-sub-lemma-T N s t)
dual-sub-lemma-T inl⟨ M ⟩ s t = cong fst[_] (dual-sub-lemma-T M s t)
dual-sub-lemma-T inr⟨ M ⟩ s t = cong snd[_] (dual-sub-lemma-T M s t)
dual-sub-lemma-T not[ K ] s t = cong not⟨_⟩ (dual-sub-lemma-C K s t)
dual-sub-lemma-T {Γ}{Θ}{A}{Θ′}{Γ′} (μθ S) s t = cong μγ (
  begin 
    sub-S TVK CK 
      (fmap-wkΘᵗⱽ Θ′ A s) 
      (sub-lift (CK.kit) t) 
      S ᵒˢ
  ≡⟨ dual-sub-lemma-S S (fmap-wkΘᵗⱽ Θ′ A s) (sub-lift (CK.kit) t) ⟩
    sub-S TK CVK
      (dual-sub-C Γ′ (Θ , A) (Θ′ , A) (sub-lift (CK.kit) t))
      (dual-sub-TV Γ Γ′ (Θ′ , A) (fmap-wkΘᵗⱽ Θ′ A s))
      (S ᵒˢ)
  ≡⟨ cong₂(λ -₁ -₂ → sub-S TK CVK (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (S ᵒˢ))
      (iext (ext (λ x → dual-sub-C-lift-lemma Γ′ Θ Θ′ A t x))) 
      (iext (ext (λ x → dual-sub-TV-fmap-lemma Γ Γ′ Θ′ A s x))) ⟩
    (sub-S TK CVK 
      (sub-lift (TK.kit) (dual-sub-C Γ′ Θ Θ′ t)) 
      (fmap-wkΓᶜⱽ (Θ′ ᵒˣ) (A ᵒᵀ) (dual-sub-TV Γ Γ′ Θ′ s)) 
      (S ᵒˢ)) 
  ∎)

dual-sub-lemma-C (` α) s t = dual-sub-lemma-covar α t
dual-sub-lemma-C fst[ K ] s t = cong inl⟨_⟩ (dual-sub-lemma-C K s t)
dual-sub-lemma-C snd[ K ] s t = cong inr⟨_⟩ (dual-sub-lemma-C K s t)
dual-sub-lemma-C `[ K , L ] s t = cong₂ `⟨_,_⟩ (dual-sub-lemma-C K s t) (dual-sub-lemma-C L s t)
dual-sub-lemma-C not⟨ M ⟩ s t = cong not[_] (dual-sub-lemma-T M s t)
dual-sub-lemma-C {A}{Γ}{Θ}{Θ′}{Γ′} (μγ S) s t = cong μθ (
  begin 
    sub-S TVK CK (sub-lift (TVK.kit) s) (fmap-wkΓᶜ Γ′ A t) S ᵒˢ
  ≡⟨ dual-sub-lemma-S S (sub-lift (TVK.kit) s) (fmap-wkΓᶜ Γ′ A t) ⟩ 
    sub-S TK CVK 
      (dual-sub-C (Γ′ , A) Θ Θ′ (fmap-wkΓᶜ Γ′ A t)) 
      (dual-sub-TV (Γ , A) (Γ′ , A) Θ′ (sub-lift (TVK.kit) s))
      (S ᵒˢ)
  ≡⟨ cong₂ (λ -₁ -₂ → sub-S TK CVK (λ{ {A} → -₁ {A} }) (λ{ {A} → -₂ {A} }) (S ᵒˢ) )
      (iext (ext (λ x → dual-sub-C-fmap-lemma Γ′ Θ Θ′ A t x))) 
      (iext (ext (λ x → dual-sub-TV-lift-lemma Γ Γ′ Θ′ A s x))) ⟩ 
    sub-S TK CVK
      (fmap-wkΘᵗ (Γ′ ᵒˣ) (A ᵒᵀ) (dual-sub-C Γ′ Θ Θ′ t))
      (sub-lift (CVK.kit) (dual-sub-TV Γ Γ′ Θ′ s))
      (S ᵒˢ)
  ∎)

dual-sub-lemma-S (M ● K) s t = cong₂ _●_ (dual-sub-lemma-C K s t) (dual-sub-lemma-T M s t)

\end{code}

%<*dual>
\begin{code}
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ : ∀ {Γ Θ} (S T : Γ ↦ Θ) → S ˢ⟶ⱽ T → (S ᵒˢ) ˢ⟶ᴺ (T ᵒˢ)
\end{code}
%</dual>

\begin{code}
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) (β×₁ v w) = β+₁ (Vᵒ≡P V v) (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) (β×₂ v w) = β+₂ (Vᵒ≡P V v) (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) (β+₁ v) = β×₁ (Vᵒ≡P V v)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) (β+₂ w) = β×₂ (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (not[ K ] ● not⟨ M ⟩) (M ● K) β¬ = β¬
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ {Γ}{Θ} (V ● μγ {Γ}{Θ}{A} S) .(sub-S TVK CK (add (λ Γ A → Σ (Γ ⟶ _ ∣ A) Value) ⟨ V , v ⟩ id-TV) id-C S) (βL v) = 
  subst (λ - → μθ (S ᵒˢ) ● V ᵒᴸ ˢ⟶ᴺ -) 
    (sym (trans 
      (dual-sub-lemma-S S (add (λ Γ A → Σ (Γ ⟶ Θ ∣ A) Value) ⟨ V , v ⟩ id-TV) id-C) 
      (cong₂ (λ -₁ -₂ → sub-S TK CVK (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (S ᵒˢ))
        (iext (λ {C} → ext (λ x → dual-sub-C-id-lemma Γ Θ C x))) 
        (iext λ {C} → ext (λ x → dual-sub-TV-add-lemma Γ Θ A V v x))))) 
    (βR (Vᵒ≡P V v))
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ {Γ}{Θ} (μθ {Γ}{Θ}{A} S ● K) .(sub-S TVK CK id-TV (add (λ Θ A → A ∣ _ ⟶ Θ) K id-C) S) βR = 
  subst (λ - → K ᵒᴿ ● μγ (S ᵒˢ) ˢ⟶ᴺ -) 
    (sym (trans 
      (dual-sub-lemma-S S id-TV (add (Fix₁ Coterm Γ) K id-C)) 
      (cong₂ (λ -₁ -₂ → sub-S TK CVK (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (S ᵒˢ))
        (iext (λ {C} → ext (λ x → dual-sub-C-add-lemma Γ Θ A C K x))) 
        (iext λ {C} → ext (λ x → dual-sub-TV-id-lemma Γ Θ C x))))) 
    βL


\end{code}