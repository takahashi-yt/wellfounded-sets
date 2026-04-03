{-# OPTIONS --cubical --guardedness --safe #-}

module FiniteSet where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat
open import Cubical.Relation.Binary.Base
open BinaryRelation
open import Cubical.Induction.WellFounded

open import Base

private
  variable
    ℓ ℓ' : Level
    n : ℕ

Fin : (n : ℕ) → Type
Fin zero = ⊥
Fin (suc n) = Fin n ⊎ Unit

_≡Fin_ : Fin n → Fin n → Type
_≡Fin_ {suc n} (inl x) (inl y) = _≡Fin_ x y
_≡Fin_ {suc n} (inl x) (inr y) = ⊥
_≡Fin_ {suc n} (inr x) (inl y) = ⊥
_≡Fin_ {suc n} (inr x) (inr y) = Unit

refl≡Fin : {k : Fin n} → k ≡Fin k
refl≡Fin {suc n} {inl x} = refl≡Fin {n}
refl≡Fin {suc n} {inr x} = tt

sym≡Fin : {k l : Fin n} → k ≡Fin l → l ≡Fin k
sym≡Fin {suc n} {inl x} {inl y} x≡y = sym≡Fin {n} x≡y
sym≡Fin {suc n} {inr x} {inr y} x≡y = tt

trans≡Fin : {k l m : Fin n} → k ≡Fin l → l ≡Fin m → k ≡Fin m
trans≡Fin {suc n} {inl x} {inl y} {inl z} x≡y y≡z = trans≡Fin {n} x≡y y≡z
trans≡Fin {suc n} {inr x} {inr y} {inl z} eq = λ u → u
trans≡Fin {suc n} {inr x} {inr y} {inr z} eq₁ eq₂ = tt

UnitIsProp : (x y : Unit) → x ≡ y
UnitIsProp tt tt = refl

≡Fin⊆≡ : {x y : Fin n} → x ≡Fin y → x ≡ y
≡Fin⊆≡ {suc n} {inl x} {inl y} ≡F = cong inl (≡Fin⊆≡ ≡F)
≡Fin⊆≡ {suc n} {inr x} {inr y} ≡F = cong inr (UnitIsProp x y)

_≼Fin_ : Fin n → Fin n → Type
_≼Fin_ {suc n} (inl x) (inl y) = _≼Fin_ x y
_≼Fin_ {suc n} (inl x) (inr y) = Unit
_≼Fin_ {suc n} (inr x) (inl y) = ⊥
_≼Fin_ {suc n} (inr x) (inr y) = Unit

≼inr : (x : Fin (suc n)) → x ≼Fin (inr tt)
≼inr (inl x) = tt
≼inr (inr x) = tt

_≺Fin_ : Fin n → Fin n → Type
_≺Fin_ {suc n} (inl x) (inl y) = _≺Fin_ x y
_≺Fin_ {suc n} (inl x) (inr y) = Unit
_≺Fin_ {suc n} (inr x) m = ⊥

isMonoFin1 : {A : Type ℓ} → (R : Rel A A ℓ') (f : Fin 1 → A) → isMonotone (_≺Fin_ {1}) R f
isMonoFin1 R f (inr x) (inr y) ()

nonRefl≺Fin : (x : Fin n) → x ≺Fin x → ⊥
nonRefl≺Fin {suc n} (inl x) x≺x = nonRefl≺Fin x x≺x

trans≺Fin : isTrans (_≺Fin_ {n})
trans≺Fin {suc n} (inl x) (inl y) (inl z) x≺y y≺z = trans≺Fin {n} x y z x≺y y≺z
trans≺Fin {suc n} (inl x) (inl y) (inr z) x≺y y≺z = tt

≼Fin⊆≡+≺ : {x y : Fin n} → x ≼Fin y → (x ≡Fin y) ⊎ (x ≺Fin y)
≼Fin⊆≡+≺ {suc n} {inl x} {inl y} ≼proof = ≼Fin⊆≡+≺ {n} {x} {y} ≼proof 
≼Fin⊆≡+≺ {suc n} {inl x} {inr y} ≼proof = inr tt
≼Fin⊆≡+≺ {suc n} {inr x} {inr y} ≼proof = inl tt

≼Fin⊆≡+≺' : {x y : Fin n} → x ≼Fin y → (y ≡Fin x) ⊎ (x ≺Fin y)
≼Fin⊆≡+≺' {n} ≼proof = ⊎.rec (λ u → inl (sym≡Fin {n} u))
                             (λ u → inr u)
                             (≼Fin⊆≡+≺ {n} ≼proof)

linear≺Fin : (x y : Fin n) → (x ≼Fin y) ⊎ (y ≺Fin x)
linear≺Fin {suc n} (inl x) (inl y) = linear≺Fin {n} x y
linear≺Fin {suc n} (inl x) (inr y) = inl tt
linear≺Fin {suc n} (inr x) (inl y) = inr tt
linear≺Fin {suc n} (inr x) (inr y) = inl tt


-- below we show that Fin n is an ordinal

prop≺Fin : isPropValued (_≺Fin_ {n})
prop≺Fin {suc n} (inl x) (inl y) l l' = prop≺Fin {n} x y l l'
prop≺Fin {suc n} (inl x) (inr y) l l' = UnitIsProp l l'

ext≺Fin' : (x y : Fin n) → ((z : Fin n) → (z ≺Fin x → z ≺Fin y) × (z ≺Fin y → z ≺Fin x)) →
            x ≡Fin y
ext≺Fin' {suc n} (inl x) (inl y) ext =
  ext≺Fin' x y λ z → fst (ext (inl z)) , snd (ext (inl z))
ext≺Fin' {suc n} (inl x) (inr y) ext = nonRefl≺Fin x (snd (ext (inl x)) tt)
ext≺Fin' {suc n} (inr x) (inl y) ext = nonRefl≺Fin y (fst (ext (inl y)) tt)
ext≺Fin' {suc n} (inr x) (inr y) ext = tt

ext≺Fin : isExtensional (_≺Fin_ {n})
ext≺Fin x y ext = ≡Fin⊆≡ (ext≺Fin' x y ext)

_≺Fin↓_ : Σ[ x ∈ Fin (suc n) ] x ≺Fin inr tt → Σ[ x ∈ Fin (suc n) ] x ≺Fin inr tt → Type
_≺Fin↓_ (inl x , _) (inl y , _) = x ≺Fin y

e : {x y : Fin n} → x ≺Fin y → (inl x , tt) ≺Fin↓ (inl y , tt)
e x≺y = x≺y

_≺Fin↓'_ : Fin n → Fin n → Type
x ≺Fin↓' y = (inl x , tt) ≺Fin↓ (inl y , tt)

prog≺inl : {x : Fin n} → Acc (_≺Fin_) x → Acc (_≺Fin_) (inl x)
prog≺inl {x = x} (acc f) = acc prog≺inlLemma
  where
  prog≺inlLemma : WFRec _≺Fin_ (Acc _≺Fin_) (inl x)
  prog≺inlLemma (inl y) ≺Proof = prog≺inl (f y ≺Proof)

wf≺Fin : WellFounded (_≺Fin_ {n})
wf≺Fin {suc n} (inl x) = prog≺inl (wf≺Fin {n} x)
wf≺Fin {suc n} (inr tt) = acc wf≺FinLemma
  where
  wf≺FinLemma : WFRec _≺Fin_ (Acc (_≺Fin_ {suc n})) (inr tt)
  wf≺FinLemma (inl y) ≺Proof = prog≺inl (wf≺Fin {n} y)

FinIsOrd : ℕ → Ord ℓ-zero ℓ-zero
FinIsOrd n = Fin n , (_≺Fin_ {n}) , prop≺Fin , wf≺Fin , ext≺Fin , trans≺Fin


-- a useful lemma

funFrom2 : (α : Ord ℓ ℓ') (x y : typeOf α) → Fin 2 → typeOf α
funFrom2 α x y (inl (inr k)) = x
funFrom2 α x y (inr l) = y

funFrom2Mono : (α : Ord ℓ ℓ') {x y : typeOf α} →
               orderOf α x y → isMonotone (_≺Fin_ {2}) (orderOf α) (funFrom2 α x y)
funFrom2Mono α x≺y (inl (inr k)) (inl (inr l)) ()
funFrom2Mono α x≺y (inl (inr k)) (inr l) _ = x≺y
funFrom2Mono α x≺y (inr k) (inl l) ()
funFrom2Mono α x≺y (inr k) (inr l) ()
