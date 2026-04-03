{-# OPTIONS --cubical --guardedness --safe #-}

module Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat
open import Cubical.Relation.Binary.Base
open BinaryRelation
open import Cubical.Induction.WellFounded
open import Cubical.HITs.PropositionalTruncation as ∥∥₁
open import Cubical.WildCat.Base
open WildCat
open import Cubical.WildCat.Functor

open import Base
open import FiniteSet

private
  variable
    ℓ ℓ' : Level


𝕁 : Ord ℓ-zero ℓ-zero → Type ℓ-zero
𝕁 α = Σ[ n ∈ ℕ ] (OrdWildCat ℓ-zero ℓ-zero [ FinIsOrd n , α ])

𝕁WildCat : (α : Ord ℓ-zero ℓ-zero) → WildCat ℓ-zero ℓ-zero
𝕁WildCat α = record { ob = 𝕁 α
                    ; Hom[_,_] = λ (n , f) (m , g) →
                                   ∥ (Σ[ h ∈ (OrdWildCat ℓ-zero ℓ-zero [ FinIsOrd n , FinIsOrd m ])]
                                     ((i : Fin n) → fst f i ≡ fst g (fst h i))) ∥₁
                    ; id = ∣ ((λ x → x) , (λ _ _ u → u)) , (λ _ → refl) ∣₁
                    ; _⋆_ = λ {x} {y} {z} → lemComp x y z
                    ; ⋆IdL = λ {x} {y} f → squash₁
                                             (lemComp x x y
                                               ∣ ((λ v → v) , (λ _ _ u → u)) , (λ z _ → fst (x .snd) z) ∣₁ f)
                                             f
                    ; ⋆IdR = λ {x} {y} f → squash₁
                                             (lemComp x y y f
                                               ∣ ((λ v → v) , (λ _ _ u → u)) , (λ z _ → fst (y .snd) z) ∣₁)
                                             f
                    ; ⋆Assoc = λ {u} {v} {w} {x} f g h → squash₁ (lemComp u w x (lemComp u v w f g) h)
                                                                 (lemComp u v x f (lemComp v w x g h))}
  where
  lemComp : (x y z : 𝕁 α) → ∥ Σ[ f ∈ (OrdWildCat ℓ-zero ℓ-zero [ FinIsOrd (x .fst) , FinIsOrd (y .fst) ])]
                              ((a : Fin (x .fst)) → fst (x .snd) a ≡ fst (y .snd) (fst f a)) ∥₁ →
                            ∥ Σ[ g ∈ (OrdWildCat ℓ-zero ℓ-zero [ FinIsOrd (y .fst) , FinIsOrd (z .fst) ])]
                              ((a : Fin (y .fst)) → fst (y .snd) a ≡ fst (z .snd) (fst g a)) ∥₁ →
                            ∥ Σ[ h ∈ (OrdWildCat ℓ-zero ℓ-zero [ FinIsOrd (x .fst) , FinIsOrd (z .fst) ])]
                              ((a : Fin (x .fst)) → fst (x .snd) a ≡ fst (z .snd) (fst h a)) ∥₁
  lemComp x y z ∣ f , prf ∣₁ ∣ g , prf' ∣₁
    = ∣ ((λ x → fst g (fst f x)) , λ x' y' x'≺y' → snd g (fst f x') (fst f y') (snd f x' y' x'≺y')) ,
        (λ i → prf i ∙ prf' (fst f i)) ∣₁
  lemComp x y z ∣ f ∣₁ (squash₁ g g' i) =
    squash₁ (lemComp x y z ∣ f ∣₁ g) (lemComp x y z ∣ f ∣₁ g') i
  lemComp x y z (squash₁ f f' i) g = squash₁ (lemComp x y z f g) (lemComp x y z f' g) i


DiagramObj : (α : Ord ℓ-zero ℓ-zero) → 𝕁 α → Ord ℓ-zero ℓ-zero
DiagramObj α (n , f) = (Σ[ x ∈ typeOf α ] ∥ Σ[ k ∈ Fin n ] (fst f k ≡ x)  ∥₁) ,
                       (λ (x , u) (y , t) → orderOf α x y) ,
                       (λ (x , u) (y , t) → propValuednessOf α x y) ,
                       (λ (x , u) → subLemForWF x u (wellFoundednessOf α x)) ,
                       (λ a b ext-proof →
                         ΣPathTransport→PathΣ a b (subLemForExt a b ext-proof ,
                                                   squash₁ (transport
                                                             (λ i → ∥ Σ[ k ∈ Fin n ]
                                                                      (fst f k ≡
                                                                       subLemForExt a b ext-proof i) ∥₁)
                                                             (snd a))
                                                           (snd b))) ,
                       λ (x , u) (y , t) (z , v) x≺y y≺z →
                         transitivityOf α x y z x≺y y≺z
  where
  subLemForWF : (x : typeOf α) (u : ∥ Σ[ k ∈ Fin n ] (fst f k ≡ x) ∥₁) →
                  Acc (orderOf α) x →
                    Acc {A = Σ[ x ∈ typeOf α ] ∥ Σ[ k ∈ Fin n ] (fst f k ≡ x) ∥₁}
                        (λ (x , u) (y , t) → orderOf α x y) (x , u)
  subLemForWF x u (acc f) = acc λ (y , t) y≺x → subLemForWF y t (f y y≺x)

  subLemForExt : (a b : Σ[ x ∈ typeOf α ] ∥ Σ[ k ∈ Fin n ] (fst f k ≡ x) ∥₁) →
                 ((c : Σ[ x ∈ typeOf α ] ∥ Σ[ k ∈ Fin n ] (fst f k ≡ x) ∥₁) →
                   (orderOf α (fst c) (fst a) → orderOf α (fst c) (fst b)) ×
                   (orderOf α (fst c) (fst b) → orderOf α (fst c) (fst a))) →
                 fst a ≡ fst b    
  subLemForExt (x , ∣ v ∣₁) (y , ∣ w ∣₁) ext-proof =
    let subsubLem₀ : (k : Fin n) → orderOf (FinIsOrd n) k (fst v) →
                                   orderOf α (fst f k) (fst f (fst w))
        subsubLem₀ k k≺v = subst (λ x₁ → orderOf α (fst f k) x₁)
                                 (sym (snd w))
                                 (fst (ext-proof (fst f k , ∣ (k , refl) ∣₁))
                                      (subst (λ x₁ → orderOf α (fst f k) x₁) (snd v) (snd f k (fst v) k≺v)))

        subsubLem₁ : (k : Fin n) → orderOf (FinIsOrd n) k (fst w) →
                                   orderOf α (fst f k) (fst f (fst v))
        subsubLem₁ k k≺w = subst (λ x₁ → orderOf α (fst f k) x₁)
                                 (sym (snd v))
                                 (snd (ext-proof (fst f k , ∣ (k , refl) ∣₁))
                                      (subst (λ x₁ → orderOf α (fst f k) x₁) (snd w) (snd f k (fst w) k≺w)))

        subsubLem₂ : fst f (fst v) ≡ fst f (fst w)
        subsubLem₂ =
          congS (fst f)
                (fst (snd (snd (snd (snd (FinIsOrd n)))))
                     (fst v)
                     (fst w)
                     λ k → (λ k≺v → ⊎.rec (λ w≼k →
                                             ⊥.rec (⊎.rec (λ k≡w →
                                               irreflexivityOf α (fst f k)
                                                                 (subst (λ x₁ → orderOf α (fst f k) x₁)
                                                                        (congS (fst f) (sym (≡Fin⊆≡ k≡w)))
                                                                        (subsubLem₀ k k≺v)))
                                                          (λ w≺k →
                                               irreflexivityOf α (fst f k)
                                                                 (transitivityOf α (fst f k)
                                                                                   (fst f (fst w))
                                                                                   (fst f k)
                                                                                   (subsubLem₀ k k≺v)
                                                                                   (snd f (fst w) k w≺k)))
                                                          (≼Fin⊆≡+≺' {n} w≼k)))
                                          (λ l → l)
                                          (linear≺Fin (fst w) k)) ,
                            λ k≺w → ⊎.rec (λ v≼k →
                                            ⊥.rec (⊎.rec (λ k≡v →
                                              irreflexivityOf α (fst f k)
                                                                (subst (λ x₁ → orderOf α (fst f k) x₁)
                                                                       (congS (fst f) (sym (≡Fin⊆≡ k≡v)))
                                                                       (subsubLem₁ k k≺w)))
                                                         (λ v≺k →
                                              irreflexivityOf α (fst f k)
                                                                (transitivityOf α (fst f k)
                                                                                  (fst f (fst v))
                                                                                  (fst f k)
                                                                                  (subsubLem₁ k k≺w)
                                                                                  (snd f (fst v) k v≺k)))
                                                         (≼Fin⊆≡+≺' {n} v≼k)))
                                          (λ l → l)
                                          (linear≺Fin (fst v) k))
    in sym (snd v) ∙ subsubLem₂ ∙ snd w
  subLemForExt (x , ∣ v ∣₁) (y , squash₁ t₁ t₂ i) ext-proof =
    ordIsSet α x y (subLemForExt (x , ∣ v ∣₁) (y , t₁) ext-proof)
                   (subLemForExt (x , ∣ v ∣₁) (y , t₂) ext-proof)
                   i
  subLemForExt (x , squash₁ u₁ u₂ i) (y , t) ext-proof =
    ordIsSet α x y (subLemForExt (x , u₁) (y , t) ext-proof)
                   (subLemForExt (x , u₂) (y , t) ext-proof)
                   i

DiagramHom : (α : Ord ℓ-zero ℓ-zero) {x y : 𝕁WildCat α .ob} →
             𝕁WildCat α [ x , y ] →
             OrdWildCat ℓ-zero ℓ-zero [ DiagramObj α x , DiagramObj α y ]
DiagramHom α {(n , f)} {(m , g)} h =
  (λ (x , u) → (x , ∥∥₁.rec squash₁ (λ (k , p) → ∥∥₁.rec squash₁
                                                        (λ h' →
                                                           ∣ fst (fst h') k , sym (snd h' k) ∙ p ∣₁)
                                                        h)
                                    u)) ,
   λ _ _ u → u

lemForF-id : (α : Ord ℓ-zero ℓ-zero) (a : 𝕁 α) →
             DiagramHom α {a} {a} (id (𝕁WildCat α) {a}) ≡ id (OrdWildCat ℓ-zero ℓ-zero) {DiagramObj α a}
lemForF-id α a =
  let h : OrdWildCat ℓ-zero ℓ-zero [ DiagramObj α a , DiagramObj α a ]
      h = DiagramHom α {a} {a} (id (𝕁WildCat α) {a})

      subLem : (v : typeOf (DiagramObj α a)) → fst h v ≡ v
      subLem v = ΣPathTransport→PathΣ (fst h v)
                                        v
                                        (refl ,
                                         squash₁ (transport
                                                   (λ i →
                                                     ∥ Σ[ k ∈ Fin (fst a) ]
                                                       (fst (snd a) k ≡ fst (fst h v)) ∥₁)
                                                   (snd (fst h v)))
                                                 (snd v))
  in ΣPathTransport→PathΣ h ((λ x → x) , (λ _ _ u → u))
       (funExt subLem ,
        isMonoIsProp (DiagramObj α a)
                     (DiagramObj α a)
                     (λ x → x)
                     (transport (λ i →
                                  isMonotone (orderOf (DiagramObj α a))
                                             (orderOf (DiagramObj α a))
                                             (funExt subLem i))
                                (snd h))
                     (λ _ _ u → u))

lemForF-seq : (α : Ord ℓ-zero ℓ-zero) {a b c : 𝕁WildCat α .ob}
              (f : 𝕁WildCat α [ a , b ]) (g : 𝕁WildCat α [ b , c ]) →
              DiagramHom α {a} {c} (concatMor (𝕁WildCat α) {a} {b} {c} f g) ≡
              concatMor (OrdWildCat ℓ-zero ℓ-zero) {DiagramObj α a} {DiagramObj α b} {DiagramObj α c}
                (DiagramHom α {a} {b} f) (DiagramHom α {b} {c} g)
lemForF-seq α {a} {b} {c} f g =
  let mor₁ : OrdWildCat ℓ-zero ℓ-zero [ DiagramObj α a , DiagramObj α c ]
      mor₁ = DiagramHom α {a} {c} (concatMor (𝕁WildCat α) {a} {b} {c} f g)

      mor₂ : OrdWildCat ℓ-zero ℓ-zero [ DiagramObj α a , DiagramObj α c ]
      mor₂ = concatMor (OrdWildCat ℓ-zero ℓ-zero) {DiagramObj α a} {DiagramObj α b} {DiagramObj α c}
               (DiagramHom α {a} {b} f) (DiagramHom α {b} {c} g)

      subLem : (x : typeOf (DiagramObj α a)) → fst mor₁ x ≡ fst mor₂ x
      subLem x =
        ΣPathTransport→PathΣ (fst mor₁ x) (fst mor₂ x)
          (refl ,
           squash₁ (transport (λ i → ∥ Σ[ k ∈ Fin (fst c) ]
                                       (fst (snd c) k ≡ fst (fst mor₁ x)) ∥₁) (snd (fst mor₁ x)))
                   (snd (fst mor₂ x)))
  in ΣPathTransport→PathΣ mor₁ mor₂
     (funExt subLem ,
      isMonoIsProp (DiagramObj α a) (DiagramObj α c) (fst mor₂)
        (transport (λ i → isMonotone (orderOf (DiagramObj α a))
                                     (orderOf (DiagramObj α c))
                                     (funExt subLem i))
                   (snd mor₁))
        (snd mor₂))

Diagram : (α : Ord ℓ-zero ℓ-zero) → WildFunctor (𝕁WildCat α) (OrdWildCat ℓ-zero ℓ-zero)
Diagram α = record {F-ob = DiagramObj α
                   ; F-hom = λ {a} {b} → DiagramHom α {a} {b}
                   ; F-id = λ {a} → lemForF-id α a
                   ; F-seq = lemForF-seq α}
