---
title: PRF
author: Ayberk Tosun
---

Originally written as an assignment in Nils Anders Danielsson's Models of
Computation course.

```agda
module PRF where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality hiding ([_])

Type₀ = Set₀
```

## Recursion principle of ℕ

```agda
natrec : ∀ {A : Type₀} → A → (ℕ → A → A) → ℕ → A
natrec z s zero     = z
natrec z s (suc n)  = s n (natrec z s n)
```

```agda
data Vec (A : Type₀) : ℕ → Type₀ where
  nil : Vec A 0
  _,_ : ∀ {n} → Vec A n → A → Vec A (suc n)
```

## Definition of the PRF syntax

```agda
data PRF : ℕ → Type₀ where
  zero : PRF 0
  suc  : PRF 1
  proj : {n   : ℕ} → Fin n → PRF n
  comp : {m n : ℕ} → PRF m → Vec (PRF n) m → PRF n
  rec  : {n   : ℕ} → PRF n → PRF (suc (suc n)) → PRF (suc n)
```

```agda
_[_] : {A : Type₀} {n : ℕ} → Vec A n → Fin n → A
_[_] (_  , x) zero    = x
_[_] (xs , x) (suc i) = xs [ i ]
```

```agda
mutual
  ⟦_⟧ : {n : ℕ} → PRF n → Vec ℕ n → ℕ
  ⟦ zero       ⟧ nil        = 0
  ⟦ suc        ⟧ (nil , n)  = 1 + n
  ⟦ proj i     ⟧ ρ          = ρ [ i ]
  ⟦ comp f gs  ⟧ ρ          = ⟦ f ⟧ (⟦ gs ⟧⋆ ρ)
  ⟦ rec  f g   ⟧ (ρ , n)    = natrec (⟦ f ⟧ ρ) (λ n r → ⟦ g ⟧ ((ρ , r) , n)) n

  ⟦_⟧⋆ : ∀ {m n} → Vec (PRF m) n → Vec ℕ m → Vec ℕ n
  ⟦ nil     ⟧⋆ ρ = nil
  ⟦ fs , f  ⟧⋆ ρ = ⟦ fs ⟧⋆ ρ , ⟦ f ⟧ ρ
```

## Implementation of addition

```agda
prf-add : PRF 2
prf-add = rec (proj zero) (comp suc (nil , proj (suc zero)))
```

```
open ≡-Reasoning

PRF-add-correct : ∀ m n → ⟦ prf-add ⟧ ((nil , m) , n) ≡ m + n
PRF-add-correct m zero = sym (+-identityʳ m)
PRF-add-correct m (suc n) =
  ⟦ prf-add ⟧ ((nil , m) , suc n)       ≡⟨ refl                           ⟩
  suc (⟦ prf-add ⟧ ((nil , m) , n))     ≡⟨ cong suc (PRF-add-correct m n) ⟩
  suc (m + n)                           ≡⟨ sym (+-suc m n)                ⟩
  m + suc n ∎
```
