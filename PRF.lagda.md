---
title: PRF
author: Ayberk Tosun
---

## Preamble and Some Bureaucratic Things

Originally written as an assignment in Nils Anders Danielsson's Models of
Computation course.

```agda
module PRF where

open import Data.Nat
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Relation.Nullary

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

```agda
private
  variable
    n : ℕ

isPrimitive : (Vec ℕ n → ℕ) → Type₀
isPrimitive {n = n} f = Σ[ p ∈ PRF n  ] ⟦ p ⟧ ≡ f
```

## Peter-Ackermann

```agda
iter : {A : Set} → ℕ → (A → A) → A → A
iter zero    f x = x
iter (suc n) f x = f (iter n f x)

succ : ℕ → ℕ
succ = suc

peter-ackermann : ℕ → ℕ → ℕ
peter-ackermann zero    = λ n → suc n
peter-ackermann (suc m) = λ n → iter (suc n) (peter-ackermann m) 1

pa-eq₀ : (n : ℕ) → peter-ackermann 0 n ≡ 1 + n
pa-eq₀ _ = refl

open ≡-Reasoning

pa-eq₁ : (m : ℕ) → peter-ackermann (suc m) 0 ≡ peter-ackermann m 1
pa-eq₁ _ = refl

pa-eq₂ : (m n : ℕ) → peter-ackermann (suc m) (suc n) ≡ peter-ackermann m (peter-ackermann (suc m) n)
pa-eq₂ _ _ = refl
```

```agda
ack : Vec ℕ 2 → ℕ
ack ((nil , m) , n) = peter-ackermann m n
```
