{-# OPTIONS --cubical --guardedness --safe #-}

module Quotient where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat
open import Cubical.Relation.Binary.Base
open BinaryRelation
open import Cubical.Induction.WellFounded
open import Cubical.HITs.PropositionalTruncation as ∥∥₁
import Cubical.HITs.SetQuotients as Q
open import Cubical.WildCat.Base
open WildCat
open WildCatIso

open import Base
open import FiniteSet
open import Diagram


private
  variable
    ℓ ℓ' : Level


≈ : (α : Ord ℓ-zero ℓ-zero) (x y : Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a))) → Type ℓ-zero
≈ α (u , x) (t , y) =
  ∥  Σ[ s ∈ 𝕁 α ] (Σ[ h₁ ∈ 𝕁WildCat α [ u , s ] ] (Σ[ h₂ ∈ 𝕁WildCat α [ t , s ] ]
       (fst (DiagramHom α {u} {s} h₁) x ≡ fst (DiagramHom α {t} {s} h₂) y))) ∥₁

∐ : (α : Ord ℓ-zero ℓ-zero) → Type ℓ-zero
∐ α = (Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a))) Q./ (≈ α)

≺QuoHProp : (α : Ord ℓ-zero ℓ-zero) (x y : ∐ α) → hProp ℓ-zero
≺QuoHProp α v w =
  Q.rec2 {A = Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a))}
         {B = Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a))}
         {R = ≈ α} {S = ≈ α}
         isSetHProp rel relCong₁ relCong₂ v w
  where
  rel : Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a)) →
        Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a)) → hProp ℓ-zero
  rel (c , x , t) (d , y , u) = orderOf α x y , fst (snd (snd α)) x y

  relCong₁ : (s t u : Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a))) →
               ≈ α s t → rel s u ≡ rel t u
  relCong₁ (c , x , s) (d , y , t) (e , z , u) congProof =
    let eq : x ≡ y
        eq = ∥∥₁.rec (ordIsSet α x y)
                     (λ (s₁ , h₁ , h₂ , eq') → fst (PathPΣ eq'))
                     congProof
    in ΣPathTransport→PathΣ
         (rel (c , x , s) (e , z , u))
         (rel (d , y , t) (e , z , u))
         (cong (λ w → orderOf α w z) eq ,
          isPropIsProp {A = fst (rel (d , y , t) (e , z , u))}
                       (transport (λ i → isProp (orderOf α (eq i) z))
                                  (snd (rel (c , x , s) (e , z , u))))
                       (snd (rel (d , y , t) (e , z , u))))

  relCong₂ : (u s t : Σ[ a ∈ 𝕁 α ] (typeOf (DiagramObj α a))) →
               ≈ α s t → rel u s ≡ rel u t
  relCong₂ (e , z , u) (c , x , s) (d , y , t) congProof =
    let eq : x ≡ y
        eq = ∥∥₁.rec (ordIsSet α x y)
                     (λ (s₁ , h₁ , h₂ , eq') → fst (PathPΣ eq'))
                     congProof
    in ΣPathTransport→PathΣ
         (rel (e , z , u) (c , x , s))
         (rel (e , z , u) (d , y , t))
         (cong (λ w → orderOf α z w) eq ,
          isPropIsProp {A = fst (rel (e , z , u) (d , y , t))}
                       (transport (λ i → isProp (orderOf α z (eq i)))
                                  (snd (rel (e , z , u) (c , x , s))))
                       (snd (rel (e , z , u) (d , y , t))))

≺Quo : (α : Ord ℓ-zero ℓ-zero) (x y : ∐ α) → Type ℓ-zero
≺Quo α x y = fst (≺QuoHProp α x y)

∐IsWF : Ord ℓ-zero ℓ-zero → WF ℓ-zero ℓ-zero
∐IsWF α = ∐ α , ≺Quo α , (λ v w → snd (≺QuoHProp α v w)) , wfLem₂ , transLem , Q.squash/
  where
  wfLem₁ : (n : ℕ) (f : OrdWildCat ℓ-zero ℓ-zero [ FinIsOrd n , α ])
           (x : typeOf α) (u : ∥ Σ[ k ∈ Fin n ] (fst f k ≡ x)  ∥₁) →
             Acc (orderOf α) x → Acc (≺Quo α) (Q.[ (n , f) , x , u ])
  wfLem₁ n f x u (acc g) =
    acc λ v → Q.elimProp (λ w → (isPropΠ {A = ≺Quo α w Q.[ (n , f) , x , u ]}
                                         (λ _ → isPropAcc {_<_ = ≺Quo α} w)))
                         (λ ((m , h) , y , t) IH → wfLem₁ m h y t (g y IH))
                         v

  wfLem₂ : WellFounded (≺Quo α)
  wfLem₂ v = Q.elimProp (isPropAcc {_<_ = ≺Quo α})
                        (λ ((m , h) , y , t) → wfLem₁ m h y t (wellFoundednessOf α y))
                        v
  
  transLem : isTrans (≺Quo α)
  transLem = Q.elimProp3
             (λ v _ u → isPropΠ2 (λ _ _ → snd (≺QuoHProp α v u)))
             λ (c₁ , x₁ , s₁) (c₂ , x₂ , s₂) (c₃ , x₃ , s₃) →
               transitivityOf α x₁ x₂ x₃

biInvEquiv∐ : (α : Ord ℓ-zero ℓ-zero) → BiInvEquiv (typeOf α) (∐ α)
biInvEquiv∐ α = biInvEquiv f g gisSection g λ _ → refl
  where
  f' : (x : typeOf α) → Fin 1 → typeOf α
  f' x _ = x

  isMonof : (x : typeOf α) → isMonotone (_≺Fin_ {1}) (orderOf α) (f' x)
  isMonof x = isMonoFin1 (orderOf α) (f' x)

  f : typeOf α → ∐ α
  f = λ x → Q.[ (suc zero , f' x , isMonof x) , x , ∣ (inr tt) , refl ∣₁ ]

  g : ∐ α → typeOf α
  g = Q.rec (ordIsSet α)
            (λ (_ , x , _) → x)
            λ (a , x , u) (b , y , t) congProof →
              ∥∥₁.rec (ordIsSet α x y)
                      (λ (c , h₁ , h₂ , eqProof) → fst (PathPΣ eqProof))
                      congProof

  gisSection : (v : ∐ α) → f (g v) ≡ v
  gisSection =
    Q.elimProp (λ v → Q.squash/ (f (g v)) v)
               λ ((n , h) , x , u) →
                 ∥∥₁.elim (λ s → Q.squash/ (f (g Q.[ (n , h) , x , s ])) Q.[ (n , h) , x , s ])
                          (λ (k , p) →
                            Q.eq/ ((1 , f' x , isMonof x) , x , ∣ inr tt , (λ _ → x) ∣₁)
                                  ((n , h) , x , ∣ k , p ∣₁)
                                  ∣ (n , h) ,
                                    ∣ ((λ _ → k) , isMonoFin1 (orderOf (FinIsOrd n)) (λ _ → k)) ,
                                      (λ _ → sym p) ∣₁ ,
                                    ∣ ((λ z → z) , (λ z₁ z₂ z₁≺z₂ → z₁≺z₂)) , (λ _ → refl) ∣₁ ,
                                    ΣPathTransport→PathΣ
                                      (x , ∣ k , (λ i → hcomp (doubleComp-faces (λ _ → fst h k) (λ _ → x) i) (p i)) ∣₁)
                                      (x , ∣ k , (λ i → hcomp (doubleComp-faces (λ _ → fst h k) p i) (fst h k)) ∣₁)
                                      (refl , ∥∥₁.squash₁ (transport (λ i → ∥ Σ[ l ∈ Fin n ] fst h l ≡ x ∥₁)
                                                                     ∣ k , (λ i → p i) ∙ (λ _ → f' (g Q.[ (n , h) , x , ∣ k , p ∣₁ ]) (inr tt)) ∣₁)
                                                          ∣ k , (λ i → fst h k) ∙ p ∣₁) ∣₁)
                          u

α≃∐α : (α : Ord ℓ-zero ℓ-zero) → (typeOf α) ≃ ∐ α
α≃∐α α = biInvEquiv→Equiv-right (biInvEquiv∐ α)

α≡∐αForType : (α : Ord ℓ-zero ℓ-zero) → (typeOf α) ≡ ∐ α
α≡∐αForType α = ua (α≃∐α α)

α≅∐α : (α : Ord ℓ-zero ℓ-zero) → WildCatIso (WFWildCat ℓ-zero ℓ-zero) (ordAsWF α) (∐IsWF α)
α≅∐α α .mor = BiInvEquiv.fun (biInvEquiv∐ α) ,
              λ _ _ x≺y → x≺y
α≅∐α α .inv =
  BiInvEquiv.invr (biInvEquiv∐ α) ,
  Q.elimProp2
    {P = λ v w → orderOf' (∐IsWF α) v w  →
                 orderOf' (ordAsWF α) (BiInvEquiv.invr (biInvEquiv∐ α) v)
                                      (BiInvEquiv.invr (biInvEquiv∐ α) w)}
    (λ v w → isPropΠ λ _ → propValuednessOf' (ordAsWF α) (BiInvEquiv.invr (biInvEquiv∐ α) v)
                                                         (BiInvEquiv.invr (biInvEquiv∐ α) w))
    λ (a , x , u) (b , y , s) ≺proof → ≺proof 
α≅∐α α .sec =
  ΣPathTransport→PathΣ
    (concatMor (WFWildCat ℓ-zero ℓ-zero) {x = ∐IsWF α} {y = ordAsWF α} {z = ∐IsWF α}
      (α≅∐α α .inv) (α≅∐α α .mor))
    ((λ x → x) , (λ _ _ u → u))
    (funExt (BiInvEquiv.invr-rightInv (biInvEquiv∐ α)) ,
    isMonoIsProp' (∐IsWF α) (∐IsWF α) (λ x → x)
      (transport (λ i → isMonotone (orderOf' (∐IsWF α))
                                   (orderOf' (∐IsWF α))
                                   (funExt (BiInvEquiv.invr-rightInv (biInvEquiv∐ α)) i))
                 (snd (concatMor (WFWildCat ℓ-zero ℓ-zero) {x = ∐IsWF α} {y = ordAsWF α} {z = ∐IsWF α}
                        (α≅∐α α .inv) (α≅∐α α .mor)))) (λ _ _ u → u))
α≅∐α α .ret =
  ΣPathTransport→PathΣ
    (concatMor (WFWildCat ℓ-zero ℓ-zero) {x = ordAsWF α} {y = ∐IsWF α} {z = ordAsWF α}
      (α≅∐α α .mor) (α≅∐α α .inv))
    ((λ x → x) , (λ _ _ u → u))
    (funExt (λ _ → refl) ,
    isMonoIsProp' (ordAsWF α) (ordAsWF α) (λ x → x)
      (transport (λ i → isMonotone (orderOf' (ordAsWF α))
                                   (orderOf' (ordAsWF α))
                                   (funExt (λ z _ →
                                     fst (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                         {x = ordAsWF α} {y = ∐IsWF α} {z = ordAsWF α}
                                         (α≅∐α α .mor) (α≅∐α α .inv)) z) i))
                 (snd (concatMor (WFWildCat ℓ-zero ℓ-zero)
                      {x = ordAsWF α} {y = ∐IsWF α} {z = ordAsWF α} (α≅∐α α .mor) (α≅∐α α .inv))))
      (λ _ _ u → u))

α≡∐α : (α : Ord ℓ-zero ℓ-zero) → (ordAsWF α) ≡ (∐IsWF α)
α≡∐α α = isoToIdWF (α≅∐α α)
