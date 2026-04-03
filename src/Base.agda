{-# OPTIONS --cubical --guardedness --safe #-}

module Base where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.Induction.WellFounded
open import Cubical.WildCat.Base
open WildCat
open WildCatIso
open import Cubical.WildCat.Functor
open WildFunctor

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ : Level
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level


_∘WFun_ : {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {E : WildCat ℓE ℓE'} →
          (G : WildFunctor D E) (F : WildFunctor C D) → WildFunctor C E
G ∘WFun F = comp-WildFunctor F G


isMonotone : {A : Type ℓ} {B : Type ℓ₁} (_≺A_ : Rel A A ℓ') (_≺B_ : Rel B B ℓ₂) →
               (f : A → B) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₂)
isMonotone {A = A} {B = B} _≺A_ _≺B_ f = (x y : A) → x ≺A y → (f x) ≺B (f y)

isExtensional : {A : Type ℓ} (_≺_ : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
isExtensional {A = A} _≺_  = (x y : A) → ((z : A) → (z ≺ x → z ≺ y) × (z ≺ y → z ≺ x)) → x ≡ y


Ord : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Ord ℓ ℓ' = Σ[ A ∈ Type ℓ ] Σ[ _≺_ ∈ (A → A → Type ℓ') ]
                (isPropValued _≺_ ×
                 WellFounded _≺_ ×
                 isExtensional _≺_ ×
                 isTrans _≺_)

typeOf : (α : Ord ℓ ℓ') → Type ℓ
typeOf α = fst α

orderOf : (α : Ord ℓ ℓ') (x y : typeOf α) → Type ℓ'
orderOf α x y = fst (snd α) x y

propValuednessOf : (α : Ord ℓ ℓ') → isPropValued (orderOf α)
propValuednessOf α = fst (snd (snd α))

wellFoundednessOf : (α : Ord ℓ ℓ') → WellFounded (orderOf α)
wellFoundednessOf α = fst (snd (snd (snd α)))

extensionalityOf : (α : Ord ℓ ℓ') → isExtensional (orderOf α)
extensionalityOf α = fst (snd (snd (snd (snd α))))

transitivityOf : (α : Ord ℓ ℓ') → isTrans (orderOf α)
transitivityOf α = snd (snd (snd (snd (snd α))))

irreflexivityOf : (α : Ord ℓ ℓ') (x : typeOf α) → orderOf α x x → ⊥
irreflexivityOf α x x≺x = subLem x (wellFoundednessOf α x) x≺x
  where
  subLem : (x : typeOf α) → Acc (orderOf α) x → orderOf α x x → ⊥
  subLem x (acc f) x≺x = subLem x (f x x≺x) x≺x

isMonoIsProp : (α β : Ord ℓ ℓ') (f : typeOf α → typeOf β) →
                isProp (isMonotone (orderOf α) (orderOf β) f)
isMonoIsProp α β f = isPropΠ2 λ x y → isPropΠ λ _ → propValuednessOf β (f x) (f y) 


preOrder : (α : Ord ℓ ℓ') (x y : typeOf α) → Type (ℓ-max ℓ ℓ')
preOrder α x y = (z : typeOf α) → orderOf α z x → orderOf α z y

poIsProp : (α : Ord ℓ ℓ') → isPropValued (preOrder α)
poIsProp α x y = isPropΠ λ z → isPropΠ λ z≺x → propValuednessOf α z y

preOrderRel : (α : Ord ℓ ℓ') → Rel (typeOf α) (typeOf α) (ℓ-max ℓ ℓ')
preOrderRel α = preOrder α

{- As Escardó observed, the prop-valuedness and extensionality of an ordinal imply that it is a set
   cf. Martín H. Escardó et al. Ordinals in univalent type theory in Agda notation, 2018. Agda development,
   URL: https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.index.html -}
ordIsSet : {ℓ ℓ' : Level} (α : Ord ℓ ℓ') → isSet (typeOf α)
ordIsSet {ℓ} {ℓ'} α = reflPropRelImpliesIdentity→isSet
               ≼×≽
               (λ _ → (λ _ v → v) , λ _ v → v)
               (λ x y → isProp× (poIsProp α x y) (poIsProp α y x))
               λ {x} {y} (x≼y , y≼x) → extensionalityOf α x y (λ z → x≼y z , y≼x z)
  where
  ≼×≽ : (x y : typeOf α) → Type (ℓ-max ℓ ℓ')
  ≼×≽ x y = preOrder α x y × preOrder α y x
  

WF : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
WF ℓ ℓ' = Σ[ A ∈ Type ℓ ] Σ[ _≺_ ∈ (A → A → Type ℓ') ]
                (isPropValued _≺_ ×
                 WellFounded _≺_ ×
                 isTrans _≺_ ×
                 isSet A)

typeOf' : (α : WF ℓ ℓ') → Type ℓ
typeOf' α = fst α

orderOf' : (α : WF ℓ ℓ') (x y : typeOf' α) → Type ℓ'
orderOf' α x y = fst (snd α) x y

propValuednessOf' : (α : WF ℓ ℓ') → isPropValued (orderOf' α)
propValuednessOf' α = fst (snd (snd α))

wellFoundednessOf' : (α : WF ℓ ℓ') → WellFounded (orderOf' α)
wellFoundednessOf' α = fst (snd (snd (snd α)))

transitivityOf' : (α : WF ℓ ℓ') → isTrans (orderOf' α)
transitivityOf' α = fst (snd (snd (snd (snd α))))

isMonoIsProp' : (α β : WF ℓ ℓ') (f : typeOf' α → typeOf' β) →
                isProp (isMonotone (orderOf' α) (orderOf' β) f)
isMonoIsProp' α β f = isPropΠ2 λ x y → isPropΠ λ _ → propValuednessOf' β (f x) (f y) 

wfIsSet : (α : WF ℓ ℓ') → isSet (typeOf' α)
wfIsSet α = snd (snd (snd (snd (snd α))))

ordAsWF : Ord ℓ ℓ' → WF ℓ ℓ'
ordAsWF α = typeOf α , orderOf α , propValuednessOf α , wellFoundednessOf α , transitivityOf α , ordIsSet α


module _ (ℓ ℓ' : Level) where

  OrdWildCat : WildCat (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  OrdWildCat .ob = Ord ℓ ℓ'
  OrdWildCat .Hom[_,_] α β = Σ[ f ∈ (typeOf α → typeOf β) ]
                               isMonotone (orderOf α) (orderOf β) f
  OrdWildCat .id = (λ x → x) , λ _ _ u → u
  OrdWildCat ._⋆_ f g = (λ x → (fst g (fst f x))) , λ a b u → snd g (fst f a) (fst f b) (snd f a b u)
  OrdWildCat .⋆IdL _ = refl
  OrdWildCat .⋆IdR _ = refl
  OrdWildCat .⋆Assoc _ _ _ = refl

  WFWildCat : WildCat (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  WFWildCat .ob = WF ℓ ℓ'
  WFWildCat .Hom[_,_] α β = Σ[ f ∈ (typeOf' α → typeOf' β) ]
                              isMonotone (orderOf' α) (orderOf' β) f
  WFWildCat .id = (λ x → x) , λ _ _ u → u
  WFWildCat ._⋆_ f g = (λ x → (fst g (fst f x))) , λ a b u → snd g (fst f a) (fst f b) (snd f a b u)
  WFWildCat .⋆IdL _ = refl
  WFWildCat .⋆IdR _ = refl
  WFWildCat .⋆Assoc _ _ _ = refl

OrdToWF : WildFunctor (OrdWildCat ℓ ℓ') (WFWildCat ℓ ℓ')
OrdToWF .F-ob α = ordAsWF α
OrdToWF .F-hom u = u
OrdToWF .F-id = refl
OrdToWF .F-seq _ _ = refl


transportCancel : {A : Type ℓ} (P : A → Type ℓ') {a b : A} (p : a ≡ b) (x : P a) →
                  transport (λ i → P (p (~ i))) (transport (λ i → P (p i)) x) ≡ x
transportCancel P {a = a} =
  J (λ b p → (x : P a) →
             transport (λ i → P (p (~ i))) (transport (λ i → P (p i)) x) ≡ x)
    λ x → transportRefl (transport (λ i → P a) x) ∙ transportRefl x


transportRelLemma : {ℓ₁ ℓ₂ : Level} {A : Type ℓ} {B : Type ℓ}
                    (p : A ≡ B) (C : (i : I) → Rel (p i) (p i) ℓ₁ → Type ℓ₂)
                    (X : Σ[ R ∈ Rel A A ℓ₁ ] C i0 R) (b₁ b₂ : B) →
                    (fst (transport (λ i → Σ[ R ∈ Rel (p i) (p i) ℓ₁ ] (C i R)) X) b₁ b₂ →
                      fst X (transport (sym p) b₁) (transport (sym p) b₂)) ×
                    (fst X (transport (sym p) b₁) (transport (sym p) b₂) →
                      fst (transport (λ i → Σ[ R ∈ Rel (p i) (p i) ℓ₁ ] (C i R)) X) b₁ b₂)
transportRelLemma _ _ _ _ _ = (λ u → u) , λ u → u
-- another proof using J-induction
-- transportRelLemma {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {A = A} p =
--   J (λ B p →
--       (C : (i : I) → Rel (p i) (p i) ℓ₁ → Type ℓ₂)
--       (X : Σ-syntax (Rel A A ℓ₁) λ R → C i0 R) (b₁ b₂ : B) →
--       (fst (transport (λ i → Σ-syntax (Rel (p i) (p i) ℓ₁) λ R → C i R) X) b₁ b₂ →
--         fst X (transport (sym p) b₁) (transport (sym p) b₂))
--       ×
--       (fst X (transport (sym p) b₁) (transport (sym p) b₂) →
--         fst (transport (λ i → Σ-syntax (Rel (p i) (p i) ℓ₁) λ R → C i R) X) b₁ b₂))
--     (λ _ _ _ _ → (λ u → u) , λ u → u) p


isoToIdWF : {ℓ ℓ' : Level} {α β : WF ℓ ℓ'} → WildCatIso (WFWildCat ℓ ℓ') α β → α ≡ β
isoToIdWF {ℓ} {ℓ'} {α} {β} α≅β =
  ΣPathTransport→PathΣ α β (typeEq ,
    ΣPathTransport→PathΣ sigmaProofSnd (snd β) (funExt (λ b₁ → funExt (eqLem b₁)) ,
      isProp×3 (isPropΠ2 λ b₁ b₂ → isPropIsProp {A = orderOf' β b₁ b₂})
               isPropWellFounded
               (isPropΠ3 (λ b₁ b₂ b₃ → isPropΠ2 λ _ _ → propValuednessOf' β b₁ b₃))
               isPropIsSet
               sigmaProofThd
               (snd (snd β))))
  where
  typeEquiv : typeOf' α ≃ typeOf' β
  typeEquiv = biInvEquiv→Equiv-right (biInvEquiv (fst (mor α≅β))
                                                 (fst (inv α≅β))
                                                 (funExt⁻ (cong fst (sec α≅β)))
                                                 (fst (inv α≅β))
                                                 (funExt⁻ (cong fst (ret α≅β)))) 
  typeEq : typeOf' α ≡ typeOf' β
  typeEq = ua typeEquiv
  -- another proof using contractible fibers
  -- typeEq = ua (fst (mor α≅β) ,
  --              record {
  --                equiv-proof =
  --                  λ b → (fst (inv α≅β) b , funExt⁻ (cong fst (sec α≅β)) b) ,
  --                        λ (a , fib) →
  --                          ΣPathTransport→PathΣ (fst (inv α≅β) b , funExt⁻ (λ i → fst (sec α≅β i)) b)
  --                                               (a , fib)
  --                                               (cong (fst (inv α≅β)) (sym fib) ∙
  --                                                  funExt⁻ (cong fst (ret α≅β)) a ,
  --                                                wfIsSet β
  --                                                        (fst (mor α≅β) a)
  --                                                        b
  --                                                        (transport (λ i →
  --                                                                     fst (mor α≅β) ((cong (fst (inv α≅β)) (sym fib) ∙
  --                                                                                       funExt⁻ (cong fst (ret α≅β)) a) i)
  --                                                                     ≡ b)
  --                                                                   (funExt⁻ (λ i → fst (sec α≅β i)) b))
  --                                                        fib)
  --              })

  ≺α↔≺β : (a₁ a₂ : typeOf' α) →
          ((orderOf' α) a₁ a₂ → (orderOf' β) (transport typeEq a₁) (transport typeEq a₂)) ×
          ((orderOf' β) (transport typeEq a₁) (transport typeEq a₂) → (orderOf' α) a₁ a₂)
  ≺α↔≺β a₁ a₂ = let famPath : (a : typeOf' α) → fst (inv α≅β) (transport typeEq a) ≡ a
                    famPath a = cong (fst (inv α≅β)) (uaβ typeEquiv a) ∙ funExt⁻ (cong fst (ret α≅β)) a

                    lem : orderOf' β (transport typeEq a₁) (transport typeEq a₂) →
                          orderOf' α (fst (inv α≅β) (transport typeEq a₁)) (fst (inv α≅β) (transport typeEq a₂))
                    lem seca₁≺seca₂ = snd (inv α≅β) (transport typeEq a₁) (transport typeEq a₂) seca₁≺seca₂

                in (λ a₁≺a₂ → transport (λ i → orderOf' β (transport typeEq a₁) (sym (uaβ typeEquiv a₂) i))
                                        (transport (λ i →
                                                     orderOf' β (sym (uaβ typeEquiv a₁) i) (fst (mor α≅β) a₂))
                                                   (snd (mor α≅β) a₁ a₂ a₁≺a₂))) ,
                   λ seca₁≺seca₂ → transport (λ i → orderOf' α a₁ (famPath a₂ i))
                                             (transport (λ i →
                                                          orderOf' α (famPath a₁ i) (fst (inv α≅β) (transport typeEq a₂)))
                                                        (lem seca₁≺seca₂))

  sigmaProofSnd : Σ[ _≺_ ∈ (typeOf' β → typeOf' β → Type ℓ') ] 
                  (isPropValued _≺_ × WellFounded _≺_ × isTrans _≺_ × isSet (typeOf' β))
  sigmaProofSnd = transport (λ i → Σ[ _≺_ ∈ (typeEq i → typeEq i → Type ℓ') ]
                              (isPropValued _≺_ × WellFounded _≺_ × isTrans _≺_ × isSet (typeEq i)))
                            (snd α)

  logEquivLem : (b₁ b₂ : typeOf' β) →
        (fst sigmaProofSnd b₁ b₂ → orderOf' β b₁ b₂) × (orderOf' β b₁ b₂ → fst sigmaProofSnd b₁ b₂)
  logEquivLem b₁ b₂ =
    let sublem₁ : (fst sigmaProofSnd b₁ b₂ →
                    orderOf' α (transport (sym typeEq) b₁) (transport (sym typeEq) b₂)) ×
                  (orderOf' α (transport (sym typeEq) b₁) (transport (sym typeEq) b₂) →
                    fst sigmaProofSnd b₁ b₂)
        sublem₁ = transportRelLemma typeEq
                                    (λ i R → isPropValued R × WellFounded R × isTrans R × isSet (typeEq i))
                                    (snd α) b₁ b₂

        sublem₂ : fst sigmaProofSnd b₁ b₂ →
                  orderOf' β (transport typeEq (transport (sym typeEq) b₁))
                             (transport typeEq (transport (sym typeEq) b₂))
        sublem₂ b₁≺b₂ = fst (≺α↔≺β (transport (sym typeEq) b₁) (transport (sym typeEq) b₂))
                            (fst sublem₁ b₁≺b₂)

        sublem₃ : fst sigmaProofSnd b₁ b₂ →
                  orderOf' β (transport typeEq (transport (ua (invEquiv typeEquiv)) b₁))
                             (transport typeEq (transport (ua (invEquiv typeEquiv)) b₂))
        sublem₃ b₁≺b₂ = transport (λ i → orderOf' β
                                           (transport typeEq (transport (sym (uaInvEquiv typeEquiv) i) b₁))
                                           (transport typeEq (transport (sym (uaInvEquiv typeEquiv) i) b₂)))
                                  (sublem₂ b₁≺b₂)

        famPath : (b : typeOf' β) →
                  transport typeEq (transport (ua (invEquiv typeEquiv)) b) ≡ b
        famPath b = uaβ typeEquiv (transport (ua (invEquiv typeEquiv)) b) ∙
                    cong (fst (mor α≅β)) (uaβ (invEquiv typeEquiv) b) ∙
                    funExt⁻ (cong fst (sec α≅β)) b

        sublem₄ : orderOf' β b₁ b₂ →
                  orderOf' α (transport (ua (invEquiv typeEquiv)) b₁) (transport (ua (invEquiv typeEquiv)) b₂)
        sublem₄ b₁≺b₂ =
          transport (λ i → orderOf' α (transport (ua (invEquiv typeEquiv)) b₁)
                                      (sym (uaβ (invEquiv typeEquiv) b₂) i))
                    (transport (λ i → orderOf' α (sym (uaβ (invEquiv typeEquiv) b₁) i)
                                                 (fst (inv α≅β) b₂))
                               (snd (inv α≅β) b₁ b₂ b₁≺b₂))
        famPath' : (b : typeOf' β) →
                   transport (ua (invEquiv typeEquiv)) b ≡ transport (sym typeEq) b
        famPath' b = transport (λ i → transport (sym (uaInvEquiv typeEquiv) i) b ≡ transport (sym typeEq) b) refl 
    in (λ b₁≺b₂ → transport (λ i → orderOf' β b₁ (famPath b₂ i))
                            (transport (λ i → orderOf' β (famPath b₁ i)
                                                         (transport typeEq (transport (ua (invEquiv typeEquiv)) b₂)))
                                       (sublem₃ b₁≺b₂))) ,
       λ b₁≺b₂ → snd sublem₁ (transport (λ i → orderOf' α (transport (sym typeEq) b₁) (famPath' b₂ i))
                                        (transport (λ i → orderOf' α (famPath' b₁ i)
                                                                     (transport (ua (invEquiv typeEquiv)) b₂))
                                                   (sublem₄ b₁≺b₂)))

  eqLem : (b₁ b₂ : typeOf' β) → fst sigmaProofSnd b₁ b₂ ≡ orderOf' β b₁ b₂
  eqLem b₁ b₂ = hPropExt (fst (snd sigmaProofSnd) b₁ b₂)
                        (propValuednessOf' β b₁ b₂)
                        (fst (logEquivLem b₁ b₂))
                        (snd (logEquivLem b₁ b₂))

  sigmaProofThd : isPropValued (orderOf' β) × WellFounded (orderOf' β) × isTrans (orderOf' β) × isSet (typeOf' β)
  sigmaProofThd = transport (λ i →
                              isPropValued (funExt (λ b₁ → funExt (eqLem b₁)) i) ×
                              WellFounded (funExt (λ b₁ → funExt (eqLem b₁)) i) ×
                              isTrans (funExt (λ b₁ → funExt (eqLem b₁)) i) ×
                              isSet (typeOf' β))
                            (snd sigmaProofSnd)
