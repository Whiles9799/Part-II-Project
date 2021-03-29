\begin{code}
module comm where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_)
\end{code}


%<*id1>
\begin{code}
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
\end{code}
%</id1>

%<*id2>
\begin{code}
+-identityʳ zero = refl
\end{code}
%</id2>

%<*id3>
\begin{code}
+-identityʳ (suc m) = cong suc (+-identityʳ m)
\end{code}
%</id3>

%<*suc1>
\begin{code}
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
\end{code}
%</suc1>

%<*suc2>
\begin{code}
+-suc zero n = refl
\end{code}
%</suc2>

%<*suc3>
\begin{code}
+-suc (suc m) n = cong suc (+-suc m n)
\end{code}
%</suc3>

%<*comm1>
\begin{code}
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
\end{code}
%</comm1>

%<*comm2>
\begin{code}
+-comm m zero = +-identityʳ m
\end{code}
%</comm2>

%<*comm3>
\begin{code}
+-comm m (suc n) =
  begin
    m + (suc n) 
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    (suc(n + m)) 
  ∎
\end{code}
%</comm3>
