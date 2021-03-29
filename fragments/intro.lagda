\begin{code}
module intro where
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
infixl 40 _+_

\end{code}

%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>

%<*plus>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero   + n = n
suc m  + n = suc (m + n)
\end{code}
%</plus>

%<*list>
\begin{code}
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
\end{code}
%</list>


%<*map>
\begin{code}
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs
\end{code}
%</map>

%<*vec>
\begin{code}
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
%</vec>

%<*head>
\begin{code}
head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x :: xs) = x
\end{code}
%</head>

%<*equality>
\begin{code}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
\end{code}
%</equality>

\begin{code}
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl
\end{code}


%<*assoc>
\begin{code}
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)
\end{code}
%</assoc>


