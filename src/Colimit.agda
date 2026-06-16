{-# OPTIONS --cubical --guardedness --safe #-}

module Colimit where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation as ∥∥₁
import Cubical.HITs.SetQuotients as Q
open import Cubical.WildCat.Base
open WildCat
open WildCatIso
open import Cubical.WildCat.Functor
open WildFunctor

open import Base
open import FiniteSet
open import Diagram
open import Quotient


private
  variable
    ℓ₁ ℓ₂ : Level

{- the following definition of colimits is dual of the one for limits in

   https://github.com/agda/cubical/blob/master/Cubical/Categories/Limits/Limits.agda
   
   except that we do not require the uniqueness of a proof that a morphism from a colimit
   to a given cocone is a cocone morphism, since we are working with wild categories and
   so a type hom (C , D) is not necessarily a set -}

module _ {ℓJ ℓJ' ℓC ℓC' : Level} {J : WildCat ℓJ ℓJ'} {C : WildCat ℓC ℓC'} where

  record Cocone (D : WildFunctor J C) (c : ob C) : Type (ℓ-max (ℓ-max ℓJ ℓJ') ℓC') where
    constructor cocone

    field
      coconeIn : (v : ob J) → C [ F-ob D v , c ]
      coconeInCommutes : {u v : ob J} (e : J [ u , v ]) →
                         coconeIn u ≡ coconeIn v ∘⟨ C ⟩ D .F-hom e 

open Cocone

module _ {ℓJ ℓJ' ℓC ℓC' : Level} {J : WildCat ℓJ ℓJ'} {C : WildCat ℓC ℓC'} where

  private
    ℓ = ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓC) ℓC'

  isCoconeMor : {c₁ c₂ : ob C} {D : WildFunctor J C} →
                Cocone D c₁ → Cocone D c₂ → C [ c₁ , c₂ ] → Type (ℓ-max ℓJ ℓC')
  isCoconeMor coconec₁ coconec₂ f =
    (v : ob J) → f ∘⟨ C ⟩ coconeIn coconec₁ v ≡ coconeIn coconec₂ v

  isColimCocone : (D : WildFunctor J C) (c : ob C) → Cocone D c → Type ℓ
  isColimCocone D c coconec = (c' : ob C) (coconec' : Cocone D c') →
                              Σ[ f ∈ C [ c , c' ] ]
                              (isCoconeMor coconec coconec' f ×
                                ((a : Σ[ g ∈ C [ c , c' ] ] isCoconeMor coconec coconec' g) →
                                 f ≡ fst a))

  idIsCoconeMor : {c : ob C} {D : WildFunctor J C} (coconec : Cocone D c) →
                  isCoconeMor coconec coconec (id C)
  idIsCoconeMor {c = c} {D = D} coconec v = ⋆IdR C {F-ob D v} {c} (coconeIn coconec v)

  record ColimCocone (D : WildFunctor J C) : Type ℓ where
    constructor lim→

    field
      colim : ob C
      colimCocone : Cocone D colim
      univProperty : isColimCocone D colim colimCocone

    colimIn : (v : ob J) → C [ D .F-ob v , colim ]
    colimIn = coconeIn colimCocone

    colimInCommutes : {u v : ob J} (e : J [ u , v ]) →
                      colimIn u ≡ colimIn v ∘⟨ C ⟩ D .F-hom e
    colimInCommutes = coconeInCommutes colimCocone

    colimArrow : (c : ob C) → Cocone D c → C [ colim , c ]
    colimArrow c coconec = fst (univProperty c coconec)

    colimArrowCommutes : (c : ob C) (coconec : Cocone D c) (u : ob J) →
                         colimArrow c coconec ∘⟨ C ⟩ colimIn u ≡ coconeIn coconec u
    colimArrowCommutes c coconec = fst (snd (univProperty c coconec))

    colimArrowUnique : (c : ob C) (coconec : Cocone D c) (k : C [ colim , c ]) →
                       isCoconeMor colimCocone coconec k → colimArrow c coconec ≡ k
    colimArrowUnique c coconec k kIsCoconeMor =
      snd (snd (univProperty c coconec)) (k , kIsCoconeMor)

open ColimCocone


-- A colimit in a wild category is unique up to isomorphism

colimUnique : {ℓJ ℓJ' ℓC ℓC' : Level} {J : WildCat ℓJ ℓJ'} {C : WildCat ℓC ℓC'} (D : WildFunctor J C) →
              (c c' : ColimCocone D) → WildCatIso C (colim c) (colim c')
colimUnique D c c' .mor = colimArrow c (colim c') (colimCocone c')
colimUnique D c c' .inv = colimArrow c' (colim c) (colimCocone c)
colimUnique {C = C} D c c' .sec =
  sym (colimArrowUnique c' (colim c') (colimCocone c')
                           (concatMor C {colim c'} {colim c} {colim c'}
                           (colimUnique D c c' .inv)
                           (colimUnique D c c' .mor))
                           λ v → sym (⋆Assoc C {F-ob D v} {colim c'} {colim c} {colim c'}
                                             (coconeIn (colimCocone c') v)
                                             (colimUnique D c c' .inv)
                                             (colimUnique D c c' .mor)) ∙
                                 cong (comp' C {F-ob D v} {colim c} {colim c'}
                                               (colimUnique D c c' .mor))
                                      (colimArrowCommutes c' (colim c) (colimCocone c) v) ∙
                                 colimArrowCommutes c (colim c') (colimCocone c') v) ∙
  colimArrowUnique c' (colim c') (colimCocone c') (id C {colim c'}) (idIsCoconeMor (colimCocone c'))
colimUnique {C = C} D c c' .ret =
  sym (colimArrowUnique c (colim c) (colimCocone c)
                          (concatMor C {colim c} {colim c'} {colim c}
                          (colimUnique D c c' .mor)
                          (colimUnique D c c' .inv))
                          λ v → sym (⋆Assoc C {F-ob D v} {colim c} {colim c'} {colim c}
                                            (coconeIn (colimCocone c) v)
                                            (colimUnique D c c' .mor)
                                            (colimUnique D c c' .inv)) ∙
                                cong (comp' C {F-ob D v} {colim c'} {colim c}
                                              (colimUnique D c c' .inv))
                                     (colimArrowCommutes c (colim c') (colimCocone c') v) ∙
                                colimArrowCommutes c' (colim c) (colimCocone c) v) ∙
  colimArrowUnique c (colim c) (colimCocone c) (id C {colim c}) (idIsCoconeMor (colimCocone c))


-- We show that α is a colimit for Diagram α

ordIsCocone : (α : Ord ℓ-zero ℓ-zero) → Cocone (Diagram α) α
ordIsCocone α = cocone (λ x → (λ a → fst a) , λ _ _ → λ u → u) λ _ → refl


ordIsColimit : (α : Ord ℓ-zero ℓ-zero) → ColimCocone (Diagram α)
ordIsColimit α =
  lim→ α (ordIsCocone α) λ β coconeβ → (morInβ β coconeβ , morInβMono β coconeβ) ,
                                       morInβCoconeMor β coconeβ ,
                                       morInβUnique β coconeβ
  where
  morInβ : (β : Ord ℓ-zero ℓ-zero) → Cocone (Diagram α) β → typeOf α → typeOf β
  morInβ β coconeβ x = let f : (x : typeOf α) → Fin 1 → typeOf α
                           f x _ = x
                       in fst (coconeIn coconeβ (1 , (λ _ → x) , isMonoFin1 (orderOf α) (λ _ → x)))
                              (x , ∣ inr tt , refl ∣₁)

  morInβMono : (β : Ord ℓ-zero ℓ-zero) (coconeβ : Cocone (Diagram α) β) →
               isMonotone (orderOf α) (orderOf β) (morInβ β coconeβ)
  morInβMono β coconeβ x y x≺y =
    let k₁ : 𝕁 α
        k₁ = 1 , (λ _ → x) , isMonoFin1 (orderOf α) (λ _ → x)

        k₂ : 𝕁 α
        k₂ = 1 , (λ _ → y) , isMonoFin1 (orderOf α) (λ _ → y)

        k₃ : 𝕁 α
        k₃ = (2 , funFrom2 α x y , funFrom2Mono α x≺y)

        h₁ : 𝕁WildCat α [ k₁ , k₃ ]
        h₁ = ∣ ((λ _ → inl (inr tt)) , isMonoFin1 (_≺Fin_ {2}) (λ _ → inl (inr tt))) ,
              (λ _ → refl) ∣₁

        h₂ : 𝕁WildCat α [ k₂ , k₃ ]
        h₂ = ∣ ((λ _ → inr tt) , isMonoFin1 (_≺Fin_ {2}) (λ _ → inr tt)) ,
              (λ _ → refl) ∣₁

        x' : typeOf β
        x' = fst (coconeIn coconeβ k₃) (fst (DiagramHom α {k₁} {k₃} h₁) (x , ∣ inr tt , refl ∣₁))

        y' : typeOf β
        y' = fst (coconeIn coconeβ k₃) (fst (DiagramHom α {k₂} {k₃} h₂) (y , ∣ inr tt , refl ∣₁))

        x'≺y' : orderOf β x' y'
        x'≺y' = snd (coconeIn coconeβ k₃)
                    (fst (DiagramHom α {k₁} {k₃} h₁) (x , ∣ inr tt , refl ∣₁))
                    (fst (DiagramHom α {k₂} {k₃} h₂) (y , ∣ inr tt , refl ∣₁))
                    x≺y
        
    in subst2 (orderOf β)
              (sym (funExt⁻ (cong fst (coconeInCommutes coconeβ h₁)) (x , ∣ inr tt , refl ∣₁)))
              (sym (funExt⁻ (cong fst (coconeInCommutes coconeβ h₂)) (y , ∣ inr tt , refl ∣₁)))
              x'≺y'

  morInβCoconeMor : (β : Ord ℓ-zero ℓ-zero) (coconeβ : Cocone (Diagram α) β) →
                    isCoconeMor (ordIsCocone α) coconeβ (morInβ β coconeβ , morInβMono β coconeβ)
  morInβCoconeMor β coconeβ (n , f) =
    let h : (a : typeOf (DiagramObj α (n , f))) →
            𝕁WildCat α [ (1 , (λ _ → fst a) , isMonoFin1 (orderOf α) (λ _ → fst a)) , (n , f) ]
        h (x , u) = ∥∥₁.rec squash₁
                           (λ (k , p) →
                              ∣ ((λ _ → k) , isMonoFin1 (orderOf (FinIsOrd n)) (λ _ → k)) ,
                                (λ _ → sym p) ∣₁)
                           u

        p' : fst (comp' (OrdWildCat ℓ-zero ℓ-zero) {DiagramObj α (n , f)} {α} {β}
                        (morInβ β coconeβ , morInβMono β coconeβ)
                        (coconeIn (ordIsCocone α) (n , f)))
             ≡ fst (coconeIn coconeβ (n , f))
        p' = 
          funExt (λ (x , u) →
                   (funExt⁻ (cong fst (coconeInCommutes coconeβ (h (x , u))))
                            (x , ∣ inr tt , (λ _ → x) ∣₁))
                    ∙ cong (λ t → fst (coconeIn coconeβ (n , f)) (x , t))
                           (squash₁ (∥∥₁.rec squash₁
                                            (λ h' → ∣ fst (fst h') (inr tt) , (sym (snd h' (inr tt))) ∙ (λ _ → x) ∣₁)
                                            (∥∥₁.rec squash₁
                                                    (λ (k , p) →
                                                      ∣ ((λ _ → k) , isMonoFin1 (orderOf (FinIsOrd n)) (λ _ → k)) ,
                                                       (λ _ → sym p) ∣₁)
                                                    u))
                                    u))
    in ΣPathTransport→PathΣ
       (comp' (OrdWildCat ℓ-zero ℓ-zero) {DiagramObj α (n , f)} {α} {β}
              (morInβ β coconeβ , morInβMono β coconeβ)
              (coconeIn (ordIsCocone α) (n , f)))
       (coconeIn coconeβ (n , f))
       (p' ,
        isMonoIsProp (DiagramObj α (n , f))
                     β
                     (fst (coconeIn coconeβ (n , f)))
                     (transport (λ i → isMonotone (orderOf (DiagramObj α (n , f))) (orderOf β) (p' i))
                                (snd (comp' (OrdWildCat ℓ-zero ℓ-zero) {DiagramObj α (n , f)} {α} {β}
                                            (morInβ β coconeβ , morInβMono β coconeβ)
                                            (coconeIn (ordIsCocone α) (n , f)))))
                     (snd (coconeIn coconeβ (n , f))))

  morInβUnique : (β : Ord ℓ-zero ℓ-zero) (coconeβ : Cocone (Diagram α) β)
                 (a : Σ[ f ∈ OrdWildCat ℓ-zero ℓ-zero [ α , β ] ]
                   (isCoconeMor (ordIsCocone α) coconeβ f)) →
                 (morInβ β coconeβ , morInβMono β coconeβ) ≡ fst a
  morInβUnique β coconeβ (f , fCoconeMor) =
    let morinβ : Σ[ f ∈ OrdWildCat ℓ-zero ℓ-zero [ α , β ] ] (isCoconeMor (ordIsCocone α) coconeβ f)
        morinβ = (morInβ β coconeβ , morInβMono β coconeβ) , morInβCoconeMor β coconeβ

        lem : morInβ β coconeβ ≡ fst f
        lem = funExt (λ x → sym (funExt⁻ (cong fst (fCoconeMor (1 ,
                                                                (λ _ → x) ,
                                                                isMonoFin1 (orderOf α) (λ _ → x))))
                                         (x , ∣ inr tt , (λ _ → x) ∣₁)))
        
    in ΣPathTransport→PathΣ (fst morinβ) f
         (lem , 
          isMonoIsProp α β (fst f)
            (transport (λ i → isMonotone (orderOf α) (orderOf β) (lem i)) (morInβMono β coconeβ))
            (snd f))
