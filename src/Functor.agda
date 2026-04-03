{-# OPTIONS --cubical --guardedness --safe #-}

module Functor where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation as ∥∥₁
open import Cubical.WildCat.Base
open WildCat
open WildCatIso
open import Cubical.WildCat.Functor
open WildFunctor

open import Base
open import FiniteSet
open import Diagram
open import Quotient
open import Colimit
open Cocone
open ColimCocone

private
  variable
    ℓ₁ ℓ₂ : Level


isFunctorPreserveColim : {ℓC ℓC' ℓD ℓD' ℓJ ℓJ' : Level}
                         {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {J : WildCat ℓJ ℓJ'}
                         (F : WildFunctor C D) (G : WildFunctor J C) →
                         Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max ℓJ ℓJ'))
isFunctorPreserveColim {D = D} F G =
  (c : ColimCocone G) →
  Σ[ c' ∈ ColimCocone (F ∘WFun G) ] WildCatIso D (F-ob F (colim c)) (colim c')

OrdToWFPC : (α : Ord ℓ-zero ℓ-zero) → isFunctorPreserveColim OrdToWF (Diagram α)
OrdToWFPC α colimForDiagram =
  let colimD≅α : WildCatIso (OrdWildCat ℓ-zero ℓ-zero) (colim colimForDiagram) (colim (ordIsColimit α))
      colimD≅α = colimUnique (Diagram α) colimForDiagram (ordIsColimit α)

  in αIsColim ,
     record { mor = F-hom OrdToWF {colim colimForDiagram} {α} (mor colimD≅α);
              inv = F-hom OrdToWF {α} {colim colimForDiagram} (inv colimD≅α);
              sec = sec colimD≅α;
              ret = ret colimD≅α}
     where
     αIsColim : ColimCocone (OrdToWF ∘WFun (Diagram α))
     colim αIsColim = F-ob OrdToWF α
     coconeIn (colimCocone αIsColim) u =
       F-hom OrdToWF {F-ob (Diagram α) u} {α} (coconeIn (colimCocone (ordIsColimit α)) u)
     coconeInCommutes (colimCocone αIsColim) {u} {v} =
       λ f → coconeInCommutes (colimCocone (ordIsColimit α)) {u} {v} f
     univProperty αIsColim β coconeβ =
       (morInβ , morInβMono) ,
        morInβCoconeMor , morInβUnique
       where
       -- typeOf' (F-ob OrdToWF α) and orderOf' (F-ob OrdToWF α) are definitionally equal to
       -- typeOf α and orderOf α, respectively
       morInβ : typeOf α → typeOf' β
       morInβ x = let f : (x : typeOf α) → Fin 1 → typeOf α
                      f x _ = x
                  in fst (coconeIn coconeβ (1 , (λ _ → x) , isMonoFin1 (orderOf α) (λ _ → x)))
                         (x , ∣ inr tt , refl ∣₁)

       morInβMono : isMonotone (orderOf α) (orderOf' β) morInβ
       morInβMono x y x≺y =
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

             x' : typeOf' β
             x' = fst (coconeIn coconeβ k₃)
                      (fst (F-hom (OrdToWF ∘WFun (Diagram α)) {k₁} {k₃} h₁) (x , ∣ inr tt , refl ∣₁))

             y' : typeOf' β
             y' = fst (coconeIn coconeβ k₃)
                      (fst (F-hom (OrdToWF ∘WFun (Diagram α)) {k₂} {k₃} h₂) (y , ∣ inr tt , refl ∣₁))

             x'≺y' : orderOf' β x' y'
             x'≺y' = snd (coconeIn coconeβ k₃)
                         (fst (F-hom (OrdToWF ∘WFun (Diagram α)) {k₁} {k₃} h₁) (x , ∣ inr tt , refl ∣₁))
                         (fst (F-hom (OrdToWF ∘WFun (Diagram α)) {k₂} {k₃} h₂) (y , ∣ inr tt , refl ∣₁))
                         x≺y

         in subst2 (orderOf' β)
                   (sym (funExt⁻ (cong fst (coconeInCommutes coconeβ h₁)) (x , ∣ inr tt , refl ∣₁)))
                   (sym (funExt⁻ (cong fst (coconeInCommutes coconeβ h₂)) (y , ∣ inr tt , refl ∣₁)))
                   x'≺y'

       morInβCoconeMor : isCoconeMor (colimCocone αIsColim) coconeβ (morInβ , morInβMono)
       morInβCoconeMor (n , f) =
         let h : (a : typeOf' (F-ob (OrdToWF ∘WFun (Diagram α)) (n , f))) →
                 𝕁WildCat α [ (1 , (λ _ → fst a) , isMonoFin1 (orderOf α) (λ _ → fst a)) , (n , f) ]
             h (x , u) = ∥∥₁.rec squash₁
                                (λ (k , p) →
                                   ∣ ((λ _ → k) , isMonoFin1 (orderOf (FinIsOrd n)) (λ _ → k)) ,
                                     (λ _ → sym p) ∣₁)
                                u

             p' : fst (comp' (WFWildCat ℓ-zero ℓ-zero)
                             {F-ob (OrdToWF ∘WFun (Diagram α)) (n , f)}
                             {F-ob OrdToWF α}
                             {β}
                             (morInβ , morInβMono)
                             (coconeIn (colimCocone αIsColim) (n , f)))
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
            (comp' (WFWildCat ℓ-zero ℓ-zero)
                   {F-ob (OrdToWF ∘WFun (Diagram α)) (n , f)}
                   {F-ob OrdToWF α}
                   {β}
                   (morInβ , morInβMono)
                   (coconeIn (colimCocone αIsColim) (n , f)))
            (coconeIn coconeβ (n , f))
            (p' ,
             isMonoIsProp' (F-ob (OrdToWF ∘WFun (Diagram α)) (n , f))
                           β
                           (fst (coconeIn coconeβ (n , f)))
                           (transport (λ i → isMonotone (orderOf' (F-ob (OrdToWF ∘WFun (Diagram α)) (n , f)))
                                                        (orderOf' β)
                                                        (p' i))
                                      (snd (comp' (WFWildCat ℓ-zero ℓ-zero)
                                                  {F-ob (OrdToWF ∘WFun (Diagram α)) (n , f)}
                                                  {F-ob OrdToWF α}
                                                  {β}
                                                  (morInβ , morInβMono)
                                                  (coconeIn (colimCocone αIsColim) (n , f)))))
                           (snd (coconeIn coconeβ (n , f))))

       morInβUnique : (a : Σ[ f ∈ WFWildCat ℓ-zero ℓ-zero [ F-ob OrdToWF α , β ] ]
                        (isCoconeMor (colimCocone αIsColim) coconeβ f)) →
                      (morInβ , morInβMono) ≡ fst a
       morInβUnique (f , fCoconeMor) =
         let lem : morInβ ≡ fst f
             lem = funExt (λ x → sym (funExt⁻ (cong fst (fCoconeMor (1 ,
                                                                     (λ _ → x) ,
                                                                     isMonoFin1 (orderOf α) (λ _ → x))))
                                              (x , ∣ inr tt , (λ _ → x) ∣₁)))

         in ΣPathTransport→PathΣ (morInβ , morInβMono) f
              (lem ,
               isMonoIsProp' (F-ob OrdToWF α) β (fst f)
                 (transport (λ i → isMonotone (orderOf α) (orderOf' β) (lem i)) morInβMono)
                 (snd f))


equal≺ω : (F G : WildFunctor (WFWildCat ℓ-zero ℓ-zero) (WFWildCat ℓ-zero ℓ-zero))
          (α : Ord ℓ-zero ℓ-zero) → Type (ℓ-suc ℓ-zero)
equal≺ω F G α =
  Σ[ p ∈ F-ob (F ∘WFun (OrdToWF ∘WFun (Diagram α))) ≡ F-ob (G ∘WFun (OrdToWF ∘WFun (Diagram α))) ]
    ({u s : 𝕁 α} (h : 𝕁WildCat α [ u , s ]) →
    transport (λ i → WFWildCat ℓ-zero ℓ-zero [ p i u , p i s ])
      (F-hom (F ∘WFun (OrdToWF ∘WFun (Diagram α))) h) ≡
    F-hom (G ∘WFun (OrdToWF ∘WFun (Diagram α))) h)

equal≺ωSym : (F G : WildFunctor (WFWildCat ℓ-zero ℓ-zero) (WFWildCat ℓ-zero ℓ-zero))
             (α : Ord ℓ-zero ℓ-zero) → equal≺ω F G α → equal≺ω G F α
equal≺ωSym F G α equal =
  sym (fst equal) ,
  λ {u} {s} h → sym (cong (transport (λ i → WFWildCat ℓ-zero ℓ-zero [ sym (fst equal) i u , sym (fst equal) i s ]))
                          (snd equal h))
                ∙
                transportCancel (λ f → WFWildCat ℓ-zero ℓ-zero [ f u , f s ])
                                (fst equal)
                                (F-hom (F ∘WFun (OrdToWF ∘WFun Diagram α)) h)

transportLemma : {ℓC ℓC' ℓ₁ ℓ₂ : Level} (C : WildCat ℓC ℓC') {f g : ob C → ob (WFWildCat ℓ₁ ℓ₂)}
                 (p : f ≡ g) →
                 {c d : ob C} {e : ob (WFWildCat ℓ₁ ℓ₂)}
                 (h : WFWildCat ℓ₁ ℓ₂ [ f c , f d ]) (h₁ : WFWildCat ℓ₁ ℓ₂ [ f c , e ]) (h₂ : WFWildCat ℓ₁ ℓ₂ [ f d , e ]) →
                 h₁ ≡ comp' (WFWildCat ℓ₁ ℓ₂) {f c} {f d} {e} h₂ h →
                 transport (λ i → WFWildCat ℓ₁ ℓ₂ [ p i c , e ]) h₁ ≡
                   comp' (WFWildCat ℓ₁ ℓ₂) {g c} {g d} {e}
                         (transport (λ i → WFWildCat ℓ₁ ℓ₂ [ p i d , e ]) h₂)
                         (transport (λ i → WFWildCat ℓ₁ ℓ₂ [ p i c , p i d ]) h)
transportLemma {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} C {f} =                          
  J (λ g p → {c d : ob C} {e : ob (WFWildCat ℓ₁ ℓ₂)}
             (h : WFWildCat ℓ₁ ℓ₂ [ f c , f d ])
             (h₁ : WFWildCat ℓ₁ ℓ₂ [ f c , e ])
             (h₂ : WFWildCat ℓ₁ ℓ₂ [ f d , e ]) →
             h₁ ≡ comp' (WFWildCat ℓ₁ ℓ₂) {f c} {f d} {e} h₂ h →
             transport (λ i → WFWildCat ℓ₁ ℓ₂ [ p i c , e ]) h₁ ≡
               comp' (WFWildCat ℓ₁ ℓ₂) {g c} {g d} {e}
                     (transport (λ i → WFWildCat ℓ₁ ℓ₂ [ p i d , e ]) h₂)
                     (transport (λ i → WFWildCat ℓ₁ ℓ₂ [ p i c , p i d ]) h))
    λ {c} {d} {e} h h₁ h₂ commuteProof →
      transportRefl h₁ ∙
      transport (λ i → h₁ ≡ comp' (WFWildCat ℓ₁ ℓ₂) {f c} {f d} {e}
                                  (sym (transportRefl h₂) i)
                                  h)
                commuteProof ∙
      cong (comp' (WFWildCat ℓ₁ ℓ₂) {f c} {f d} {e}
                  (transport (λ i → WFWildCat ℓ₁ ℓ₂ [ f d , e ]) h₂))
           (sym (transportRefl h))

factorLemma : (C : WildCat ℓ₁ ℓ₂) {a b : ob C} (p : a ≡ b) {c : ob C} (h : C [ b , c ]) →
              transport (λ i → C [ p (~ i) , c ]) h ≡
              comp' C {a} {b} {c} h (transport (λ i → C [ a , p i ]) (id C {a}))
factorLemma C {a} = J (λ b p → {c : ob C} (h : C [ b , c ]) →
                               transport (λ i → C [ p (~ i) , c ]) h ≡
                               comp' C {a} {b} {c} h (transport (λ i → C [ a , p i ]) (id C {a})))
                      λ {c} h → transportRefl h ∙
                                sym (⋆IdL C h) ∙
                                cong (comp' C {a} {a} {c} h) (sym (transportRefl (id C {a})))

cancelLemma : (C : WildCat ℓ₁ ℓ₂) {a b : ob C} (p : a ≡ b) →
              concatMor C {b} {a} {b}
                (transport (λ i → C [ b , p (~ i) ]) (id C {b})) (transport (λ i → C [ a , p i ]) (id C {a})) ≡ id C {b}
cancelLemma C {a} = J (λ b p → concatMor C {b} {a} {b}
                                 (transport (λ i → C [ b , p (~ i) ]) (id C {b}))
                                 (transport (λ i → C [ a , p i ]) (id C {a})) ≡
                               id C {b})
                      (cong (concatMor C {a} {a} {a} (transport (λ i → C [ a , a ]) (id C {a})))
                            (transportRefl (id C {a})) ∙
                       cong (comp' C {a} {a} {a} (id C {a}))
                            (transportRefl (id C {a})) ∙
                       ⋆IdL C (id C {a}))

dilatingProperty : {F G : WildFunctor (WFWildCat ℓ-zero ℓ-zero) (WFWildCat ℓ-zero ℓ-zero)} →
                   ((α : Ord ℓ-zero ℓ-zero) → isFunctorPreserveColim F (OrdToWF ∘WFun (Diagram α)) ×
                                             isFunctorPreserveColim G (OrdToWF ∘WFun (Diagram α))) →
                   (α : Ord ℓ-zero ℓ-zero) → equal≺ω F G α → F-ob F (ordAsWF α) ≡ F-ob G (ordAsWF α)
dilatingProperty {F = F} {G = G} preserve α equal₁ =
  isoToIdWF isoFαColimFD ∙ isoToIdWF isoColimFDGD ∙ sym (isoToIdWF isoGαColimGD)
  where
  equal₂ : equal≺ω G F α
  equal₂ = equal≺ωSym F G α equal₁

  colimOrdToWF : Σ[ c ∈ ColimCocone (OrdToWF ∘WFun Diagram α) ]
                   WildCatIso (WFWildCat ℓ-zero ℓ-zero)
                   (ordAsWF α) (colim c)
  colimOrdToWF = OrdToWFPC α (ordIsColimit α)
  
  colimFD : Σ[ c ∈ ColimCocone (F ∘WFun (OrdToWF ∘WFun Diagram α)) ]
              WildCatIso (WFWildCat ℓ-zero ℓ-zero)
              (F-ob F (colim (fst colimOrdToWF))) (colim c)
  colimFD = fst (preserve α) (fst colimOrdToWF)

  colimGD : Σ[ c ∈ ColimCocone (G ∘WFun (OrdToWF ∘WFun Diagram α)) ]
              WildCatIso (WFWildCat ℓ-zero ℓ-zero)
              (F-ob G (colim (fst colimOrdToWF))) (colim c)
  colimGD = snd (preserve α) (fst colimOrdToWF)

  coconeFD : Cocone (F ∘WFun (OrdToWF ∘WFun Diagram α)) (colim (fst colimGD))
  coconeIn coconeFD v = transport (λ i →
                                   WFWildCat ℓ-zero ℓ-zero [ fst equal₂ i v , colim (fst colimGD) ])
                                   (coconeIn (colimCocone (fst colimGD)) v)
  coconeInCommutes coconeFD {u = u} {v = v} h =
    transportLemma (𝕁WildCat α)
                   (fst equal₂)
                   {u} {v} {colim (fst colimGD)}
                   (F-hom (G ∘WFun (OrdToWF ∘WFun Diagram α)) h)
                   (coconeIn (colimCocone (fst colimGD)) u)
                   (coconeIn (colimCocone (fst colimGD)) v)
                   (coconeInCommutes (colimCocone (fst colimGD)) h)
    ∙
    cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                {x = F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                {y = F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) v}
                {z = colim (fst colimGD)}
                (transport (λ i → WFWildCat ℓ-zero ℓ-zero [ fst equal₂ i v , colim (fst colimGD) ])
                           (coconeIn (colimCocone (fst colimGD)) v)))
         (snd equal₂ h)

  coconeGD : Cocone (G ∘WFun (OrdToWF ∘WFun Diagram α)) (colim (fst colimFD))
  coconeIn coconeGD v = transport (λ i →
                                   WFWildCat ℓ-zero ℓ-zero [ fst equal₁ i v , colim (fst colimFD) ])
                                   (coconeIn (colimCocone (fst colimFD)) v)
  coconeInCommutes coconeGD {u = u} {v = v} h =
    transportLemma (𝕁WildCat α)
                   (fst equal₁)
                   {u} {v} {colim (fst colimFD)}
                   (F-hom (F ∘WFun (OrdToWF ∘WFun Diagram α)) h)
                   (coconeIn (colimCocone (fst colimFD)) u)
                   (coconeIn (colimCocone (fst colimFD)) v)
                   (coconeInCommutes (colimCocone (fst colimFD)) h)
    ∙
    cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                {x = F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                {y = F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) v}
                {z = colim (fst colimFD)}
                (transport (λ i → WFWildCat ℓ-zero ℓ-zero [ fst equal₁ i v , colim (fst colimFD) ])
                           (coconeIn (colimCocone (fst colimFD)) v)))
         (snd equal₁ h)

  univPropertyFD : Σ[ f ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimFD) , colim (fst colimGD) ] ]
                   isCoconeMor (colimCocone (fst colimFD)) coconeFD f ×
                   ((a : Σ[ g ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimFD) , colim (fst colimGD) ] ]
                     (isCoconeMor (colimCocone (fst colimFD)) coconeFD g)) →
                   f ≡ fst a)
  univPropertyFD = univProperty (fst colimFD) (colim (fst colimGD)) coconeFD

  univPropertyGD : Σ[ f ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimGD) , colim (fst colimFD) ] ]
                   isCoconeMor (colimCocone (fst colimGD)) coconeGD f ×
                   ((a : Σ[ g ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimGD) , colim (fst colimFD) ] ]
                     (isCoconeMor (colimCocone (fst colimGD)) coconeGD g)) →
                   f ≡ fst a)
  univPropertyGD = univProperty (fst colimGD) (colim (fst colimFD)) coconeGD

  isoFαColimFD : WildCatIso (WFWildCat ℓ-zero ℓ-zero)
                 (F-ob F (ordAsWF α)) (colim (fst colimFD))
  mor isoFαColimFD =
    comp' (WFWildCat ℓ-zero ℓ-zero) {F-ob F (ordAsWF α)} {F-ob F (colim (fst colimOrdToWF))} {colim (fst colimFD)}
          (mor (snd colimFD))
          (F-hom F (mor (snd colimOrdToWF)))
  inv isoFαColimFD =
    comp' (WFWildCat ℓ-zero ℓ-zero) {colim (fst colimFD)} {F-ob F (colim (fst colimOrdToWF))} {F-ob F (ordAsWF α)}
          (F-hom F (inv (snd colimOrdToWF)))
          (inv (snd colimFD))
  sec isoFαColimFD = (((⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                               {colim (fst colimFD)}
                               {F-ob F (ordAsWF α)}
                               {F-ob F (colim (fst colimOrdToWF))}
                               {colim (fst colimFD)}
                               (inv isoFαColimFD)
                               (F-hom F (mor (snd colimOrdToWF)))
                               (mor (snd colimFD)) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {colim (fst colimFD)} {F-ob F (colim (fst colimOrdToWF))} {colim (fst colimFD)}
                                 (mor (snd colimFD)))
                          (sym (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                                       {colim (fst colimFD)}
                                       {F-ob F (colim (fst colimOrdToWF))}
                                       {F-ob F (ordAsWF α)}
                                       {F-ob F (colim (fst colimOrdToWF))}
                                       (inv (snd colimFD))
                                       (F-hom F (inv (snd colimOrdToWF)))
                                       (F-hom F (mor (snd colimOrdToWF)))))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {colim (fst colimFD)} {F-ob F (colim (fst colimOrdToWF))} {colim (fst colimFD)}
                                 (mor (snd colimFD)))
                          (cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                  {colim (fst colimFD)} {F-ob F (colim (fst colimOrdToWF))} {F-ob F (colim (fst colimOrdToWF))}
                                  (inv (snd colimFD)))
                                (sym (F-seq F
                                       {colim (fst colimOrdToWF)} {ordAsWF α} {colim (fst colimOrdToWF)}
                                       (inv (snd colimOrdToWF)) (mor (snd colimOrdToWF))) ∙
                                 cong (F-hom F) (sec (snd colimOrdToWF)) ∙
                                 F-id F))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {colim (fst colimFD)} {F-ob F (colim (fst colimOrdToWF))} {colim (fst colimFD)}
                                 (mor (snd colimFD)))
                          (⋆IdL (WFWildCat ℓ-zero ℓ-zero)
                                {colim (fst colimFD)} {F-ob F (colim (fst colimOrdToWF))}
                                (inv (snd colimFD)))) ∙
                     sec (snd colimFD)
  ret isoFαColimFD = (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                             {F-ob F (ordAsWF α)}
                             {colim (fst colimFD)}
                             {F-ob F (colim (fst colimOrdToWF))}
                             {F-ob F (ordAsWF α)}
                             (mor isoFαColimFD)
                             (inv (snd colimFD))
                             (F-hom F (inv (snd colimOrdToWF))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {F-ob F (ordAsWF α)}
                                 {F-ob F (colim (fst colimOrdToWF))}
                                 {F-ob F (ordAsWF α)}
                                 (F-hom F (inv (snd colimOrdToWF))))
                          (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                                 {F-ob F (ordAsWF α)}
                                 {F-ob F (colim (fst colimOrdToWF))}
                                 {colim (fst colimFD)}
                                 {F-ob F (colim (fst colimOrdToWF))}
                                 (F-hom F (mor (snd colimOrdToWF)))
                                 (mor (snd colimFD))
                                 (inv (snd colimFD)))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {F-ob F (ordAsWF α)} {F-ob F (colim (fst colimOrdToWF))} {F-ob F (ordAsWF α)}
                                 (F-hom F (inv (snd colimOrdToWF))))
                          (cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                           {F-ob F (ordAsWF α)} {F-ob F (colim (fst colimOrdToWF))} {F-ob F (colim (fst colimOrdToWF))}
                                           (F-hom F (mor (snd colimOrdToWF))))
                                (ret (snd colimFD)) ∙
                          ⋆IdL (WFWildCat ℓ-zero ℓ-zero)
                               {F-ob F (ordAsWF α)} {F-ob F (colim (fst colimOrdToWF))}
                               (F-hom F (mor (snd colimOrdToWF)))) ∙
                     sym (F-seq F {ordAsWF α}
                         {colim (fst colimOrdToWF)} {ordAsWF α}
                         (mor (snd colimOrdToWF)) (inv (snd colimOrdToWF))) ∙
                     cong (F-hom F) (ret (snd colimOrdToWF)) ∙
                     F-id F

  isoGαColimGD : WildCatIso (WFWildCat ℓ-zero ℓ-zero)
                 (F-ob G (ordAsWF α)) (colim (fst colimGD))
  mor isoGαColimGD =
    comp' (WFWildCat ℓ-zero ℓ-zero) {F-ob G (ordAsWF α)} {F-ob G (colim (fst colimOrdToWF))} {colim (fst colimGD)}
          (mor (snd colimGD))
          (F-hom G (mor (snd colimOrdToWF)))
  inv isoGαColimGD =
    comp' (WFWildCat ℓ-zero ℓ-zero) {colim (fst colimGD)} {F-ob G (colim (fst colimOrdToWF))} {F-ob G (ordAsWF α)}
          (F-hom G (inv (snd colimOrdToWF)))
          (inv (snd colimGD))

  sec isoGαColimGD = (((⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                               {colim (fst colimGD)}
                               {F-ob G (ordAsWF α)}
                               {F-ob G (colim (fst colimOrdToWF))}
                               {colim (fst colimGD)}
                               (inv isoGαColimGD)
                               (F-hom G (mor (snd colimOrdToWF)))
                               (mor (snd colimGD)) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {colim (fst colimGD)} {F-ob G (colim (fst colimOrdToWF))} {colim (fst colimGD)}
                                 (mor (snd colimGD)))
                          (sym (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                                       {colim (fst colimGD)}
                                       {F-ob G (colim (fst colimOrdToWF))}
                                       {F-ob G (ordAsWF α)}
                                       {F-ob G (colim (fst colimOrdToWF))}
                                       (inv (snd colimGD))
                                       (F-hom G (inv (snd colimOrdToWF)))
                                       (F-hom G (mor (snd colimOrdToWF)))))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {colim (fst colimGD)} {F-ob G (colim (fst colimOrdToWF))} {colim (fst colimGD)}
                                 (mor (snd colimGD)))
                          (cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                  {colim (fst colimGD)} {F-ob G (colim (fst colimOrdToWF))} {F-ob G (colim (fst colimOrdToWF))}
                                  (inv (snd colimGD)))
                                (sym (F-seq G
                                       {colim (fst colimOrdToWF)} {ordAsWF α} {colim (fst colimOrdToWF)}
                                       (inv (snd colimOrdToWF)) (mor (snd colimOrdToWF))) ∙
                                 cong (F-hom G) (sec (snd colimOrdToWF)) ∙
                                 F-id G))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {colim (fst colimGD)} {F-ob G (colim (fst colimOrdToWF))} {colim (fst colimGD)}
                                 (mor (snd colimGD)))
                          (⋆IdL (WFWildCat ℓ-zero ℓ-zero)
                                {colim (fst colimGD)} {F-ob G (colim (fst colimOrdToWF))}
                                (inv (snd colimGD)))) ∙
                     sec (snd colimGD)

  ret isoGαColimGD = (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                             {F-ob G (ordAsWF α)}
                             {colim (fst colimGD)}
                             {F-ob G (colim (fst colimOrdToWF))}
                             {F-ob G (ordAsWF α)}
                             (mor isoGαColimGD)
                             (inv (snd colimGD))
                             (F-hom G (inv (snd colimOrdToWF))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {F-ob G (ordAsWF α)}
                                 {F-ob G (colim (fst colimOrdToWF))}
                                 {F-ob G (ordAsWF α)}
                                 (F-hom G (inv (snd colimOrdToWF))))
                          (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                                 {F-ob G (ordAsWF α)}
                                 {F-ob G (colim (fst colimOrdToWF))}
                                 {colim (fst colimGD)}
                                 {F-ob G (colim (fst colimOrdToWF))}
                                 (F-hom G (mor (snd colimOrdToWF)))
                                 (mor (snd colimGD))
                                 (inv (snd colimGD)))) ∙
                     cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                 {F-ob G (ordAsWF α)} {F-ob G (colim (fst colimOrdToWF))} {F-ob G (ordAsWF α)}
                                 (F-hom G (inv (snd colimOrdToWF))))
                          (cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                           {F-ob G (ordAsWF α)} {F-ob G (colim (fst colimOrdToWF))} {F-ob G (colim (fst colimOrdToWF))}
                                           (F-hom G (mor (snd colimOrdToWF))))
                                (ret (snd colimGD)) ∙
                          ⋆IdL (WFWildCat ℓ-zero ℓ-zero)
                               {F-ob G (ordAsWF α)} {F-ob G (colim (fst colimOrdToWF))}
                               (F-hom G (mor (snd colimOrdToWF)))) ∙
                     sym (F-seq G {ordAsWF α}
                         {colim (fst colimOrdToWF)} {ordAsWF α}
                         (mor (snd colimOrdToWF)) (inv (snd colimOrdToWF))) ∙
                     cong (F-hom G) (ret (snd colimOrdToWF)) ∙
                     F-id G

  isoColimFDGD : WildCatIso (WFWildCat ℓ-zero ℓ-zero)
                 (colim (fst colimFD)) (colim (fst colimGD))
  mor isoColimFDGD = fst univPropertyFD
  inv isoColimFDGD = fst univPropertyGD
  sec isoColimFDGD =
    let invMor : WFWildCat ℓ-zero ℓ-zero [ colim (fst colimGD) , colim (fst colimGD) ]
        invMor = concatMor (WFWildCat ℓ-zero ℓ-zero)
                           {colim (fst colimGD)} {colim (fst colimFD)} {colim (fst colimGD)}
                           (fst univPropertyGD) (fst univPropertyFD)

        uniqueMor : Σ[ f ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimGD) , colim (fst colimGD) ] ]
                      isCoconeMor (colimCocone (fst colimGD)) (colimCocone (fst colimGD)) f ×
                      ((a : Σ[ g ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimGD) , colim (fst colimGD) ] ]
                              isCoconeMor (colimCocone (fst colimGD)) (colimCocone (fst colimGD)) g) →
                      f ≡ fst a)
        uniqueMor = univProperty (fst colimGD) (colim (fst colimGD)) (colimCocone (fst colimGD))
    in sym (snd (snd uniqueMor)
                (invMor ,
                 λ u → ⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                              {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {colim (fst colimGD)}
                              {colim (fst colimFD)}
                              {colim (fst colimGD)}
                              (coconeIn (colimCocone (fst colimGD)) u)
                              (inv isoColimFDGD)
                              (mor isoColimFDGD) ∙
                       cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimFD)}
                                   {colim (fst colimGD)}
                                   (mor isoColimFDGD))
                            (fst (snd univPropertyGD) u) ∙
                       cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimFD)}
                                   {colim (fst colimGD)}
                                   (mor isoColimFDGD))
                                   (factorLemma (WFWildCat ℓ-zero ℓ-zero)
                                                (sym (funExt⁻ (fst equal₁) u))
                                                {colim (fst colimFD)}
                                                (coconeIn (colimCocone (fst colimFD)) u)) ∙
                       sym (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimFD)}
                                   {colim (fst colimGD)}
                                   (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                                [ F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                                  funExt⁻ (fst equal₁) u (~ i) ])
                                              (id (WFWildCat ℓ-zero ℓ-zero)
                                                  {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}))
                                   (coconeIn (colimCocone (fst colimFD)) u)
                                   (mor isoColimFDGD)) ∙
                       cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                       {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {colim (fst colimGD)}
                                       (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                                     [ F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                                       funExt⁻ (fst equal₁) u (~ i) ])
                                                  (id (WFWildCat ℓ-zero ℓ-zero)
                                                      {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u})))
                            (fst (snd univPropertyFD) u) ∙
                       cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                       {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {colim (fst colimGD)}
                                       (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                                     [ F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                                       funExt⁻ (fst equal₁) u (~ i) ])
                                                  (id (WFWildCat ℓ-zero ℓ-zero)
                                                      {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u})))
                            (factorLemma (WFWildCat ℓ-zero ℓ-zero)
                                         (funExt⁻ (fst equal₁) u)
                                         {colim (fst colimGD)}
                                         (coconeIn (colimCocone (fst colimGD)) u)) ∙
                       ⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                              {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {colim (fst colimGD)}
                              (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                            [ F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                              funExt⁻ (fst equal₁) u (~ i) ])
                                         (id (WFWildCat ℓ-zero ℓ-zero)
                                             {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}))
                              (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                            [ F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                              funExt⁻ (fst equal₁) u i ])
                                         (id (WFWildCat ℓ-zero ℓ-zero)
                                             {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}))
                              (coconeIn (colimCocone (fst colimGD)) u) ∙
                       cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimGD)}
                                   (coconeIn (colimCocone (fst colimGD)) u))
                            (cancelLemma (WFWildCat ℓ-zero ℓ-zero) (funExt⁻ (fst equal₁) u)) ∙
                       ⋆IdL (WFWildCat ℓ-zero ℓ-zero)
                            {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                            {colim (fst colimGD)}
                            (coconeIn (colimCocone (fst colimGD)) u))) ∙
       snd (snd uniqueMor)
           (id (WFWildCat ℓ-zero ℓ-zero) {colim (fst colimGD)} ,
            idIsCoconeMor (colimCocone (fst colimGD)))
  ret isoColimFDGD =
    let morInv : WFWildCat ℓ-zero ℓ-zero [ colim (fst colimFD) , colim (fst colimFD) ]
        morInv = concatMor (WFWildCat ℓ-zero ℓ-zero)
                           {colim (fst colimFD)} {colim (fst colimGD)} {colim (fst colimFD)}
                           (fst univPropertyFD) (fst univPropertyGD)

        uniqueMor : Σ[ f ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimFD) , colim (fst colimFD) ] ]
                      isCoconeMor (colimCocone (fst colimFD)) (colimCocone (fst colimFD)) f ×
                      ((a : Σ[ g ∈ WFWildCat ℓ-zero ℓ-zero [ colim (fst colimFD) , colim (fst colimFD) ] ]
                              isCoconeMor (colimCocone (fst colimFD)) (colimCocone (fst colimFD)) g) →
                      f ≡ fst a)
        uniqueMor = univProperty (fst colimFD) (colim (fst colimFD)) (colimCocone (fst colimFD))
    in sym (snd (snd uniqueMor)
                (morInv ,
                 λ u → ⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                              {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {colim (fst colimFD)}
                              {colim (fst colimGD)}
                              {colim (fst colimFD)}
                              (coconeIn (colimCocone (fst colimFD)) u)
                              (mor isoColimFDGD)
                              (inv isoColimFDGD) ∙
                       cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimGD)}
                                   {colim (fst colimFD)}
                                   (inv isoColimFDGD))
                            (fst (snd univPropertyFD) u) ∙
                       cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimGD)}
                                   {colim (fst colimFD)}
                                   (inv isoColimFDGD))
                                   (factorLemma (WFWildCat ℓ-zero ℓ-zero)
                                                (funExt⁻ (fst equal₁) u)
                                                {colim (fst colimGD)}
                                                (coconeIn (colimCocone (fst colimGD)) u)) ∙
                       sym (⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimGD)}
                                   {colim (fst colimFD)}
                                   (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                                [ F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                                  funExt⁻ (fst equal₁) u i ])
                                              (id (WFWildCat ℓ-zero ℓ-zero)
                                                  {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}))
                                   (coconeIn (colimCocone (fst colimGD)) u)
                                   (inv isoColimFDGD)) ∙
                       cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                       {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {colim (fst colimFD)}
                                       (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                                     [ F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                                       funExt⁻ (fst equal₁) u i ])
                                                  (id (WFWildCat ℓ-zero ℓ-zero)
                                                      {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u})))
                            (fst (snd univPropertyGD) u) ∙
                       cong (concatMor (WFWildCat ℓ-zero ℓ-zero)
                                       {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                       {colim (fst colimFD)}
                                       (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                                     [ F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                                       funExt⁻ (fst equal₁) u i ])
                                                  (id (WFWildCat ℓ-zero ℓ-zero)
                                                      {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u})))
                            (factorLemma (WFWildCat ℓ-zero ℓ-zero)
                                         (sym (funExt⁻ (fst equal₁) u))
                                         {colim (fst colimFD)}
                                         (coconeIn (colimCocone (fst colimFD)) u)) ∙
                       ⋆Assoc (WFWildCat ℓ-zero ℓ-zero)
                              {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                              {colim (fst colimFD)}
                              (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                            [ F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                              funExt⁻ (fst equal₁) u i ])
                                         (id (WFWildCat ℓ-zero ℓ-zero)
                                             {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}))
                              (transport (λ i → WFWildCat ℓ-zero ℓ-zero
                                            [ F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u ,
                                              funExt⁻ (fst equal₁) u (~ i) ])
                                         (id (WFWildCat ℓ-zero ℓ-zero)
                                             {F-ob (G ∘WFun (OrdToWF ∘WFun Diagram α)) u}))
                              (coconeIn (colimCocone (fst colimFD)) u) ∙
                       cong (comp' (WFWildCat ℓ-zero ℓ-zero)
                                   {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                                   {colim (fst colimFD)}
                                   (coconeIn (colimCocone (fst colimFD)) u))
                            (cancelLemma (WFWildCat ℓ-zero ℓ-zero) (sym (funExt⁻ (fst equal₁) u))) ∙
                       ⋆IdL (WFWildCat ℓ-zero ℓ-zero)
                            {F-ob (F ∘WFun (OrdToWF ∘WFun Diagram α)) u}
                            {colim (fst colimFD)}
                            (coconeIn (colimCocone (fst colimFD)) u))) ∙
       snd (snd uniqueMor)
           (id (WFWildCat ℓ-zero ℓ-zero) {colim (fst colimFD)} ,
            idIsCoconeMor (colimCocone (fst colimFD)))
