{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Polynomial
open import PolyMagma
open import PolyMonad
open import Util

module wip.NotGood {ℓ} {I : Type ℓ} where

  module _ {ℓ} {I : Type ℓ} {P : Poly I} where

    W= : {i : I} (w w' : W P i) → Type ℓ
    W= (lf i) (lf . i) = Lift ⊤
    W= (lf _) (nd _) = Lift ⊥
    W= (nd _) (lf _) = Lift ⊥
    W= (nd (f , δ)) (nd (f' , δ')) = Σ (f == f') (λ p → δ == δ' [ (λ x → (j : I) (p : Param P x j) → W P j) ↓ p ])

    W=-eq : {i : I} (w w' : W P i) → (W= w w') ≃ (w == w')
    W=-eq (lf _) (nd _) = equiv (λ {()}) (λ ()) (λ ()) λ {()}
    W=-eq (nd _) (lf _) = equiv (λ {()}) (λ ()) (λ ()) λ {()}
    W=-eq (lf _) (lf _) = equiv (λ _ → idp) (λ _ → lift tt) (λ { idp → idp }) λ {(lift tt) → idp}
    W=-eq (nd (f , δ)) (nd (f' , δ')) = equiv ( λ { (p , q) → ap (λ { (f , δ) → nd (f , δ) }) (pair= p q) }) (λ { idp → (idp , idp)}) (λ { idp → idp }) (λ { (idp , idp) → idp })

  is-good : ∀ {ℓ} {I : Type ℓ} → Poly I → Type ℓ
  is-good {I = I} P = {i : I} (w : W P i) → is-contr (OutFrame P w)

  U : Poly (Lift ⊤)
  Op    U (lift tt) = Type ℓ 
  Param U X (lift tt) = Lift X

  μ-mgm : W U (lift tt) → Type ℓ
  μ-mgm (lf .(lift tt)) = Lift ⊤
  μ-mgm (nd (X , δ)) = Σ X (λ x → μ-mgm (δ (lift tt) (lift x)))

  μ-leaf-eq : (w : W U _) → μ-mgm w ≃ Leaf U w _
  μ-leaf-eq w = equiv (f w) (g w) (f-g w) (g-f w)
    where f : (w : W U _) → μ-mgm w → Leaf U w _
          f (lf _) _ = idp
          f (nd _) (x , Y) = (_ , lift x , f _ Y)

          g : (w : W U _) → Leaf U w _ → μ-mgm w
          g (lf _) _ = lift tt
          g (nd _) (_ , lift x , Y) = x , g _ Y

          f-g : (w : W U _) → (f w) ∘ (g w) ∼ idf _
          f-g (lf _) idp = idp
          f-g (nd _) _ = pair= idp (pair= idp (f-g _ _))

          g-f : (w : W U _) → (g w) ∘ (f w) ∼ idf _
          g-f (lf _) _ = idp
          g-f (nd _) (x , Y) = pair= idp (g-f _ _)

  μ-mgm-frm : (w : W U (lift tt)) → Frame U w (μ-mgm w)
  μ-mgm-frm w _ = lower-equiv ⁻¹ ∘e μ-leaf-eq w ⁻¹

  U-mgm : PolyMagma U
  μ     U-mgm = μ-mgm
  μ-frm U-mgm = μ-mgm-frm

  OutFrame-eq : (w : W U _) → OutFrame U w ≃ Σ (Type ℓ) (λ X → μ-mgm w == X)
  OutFrame-eq w = equiv f g f-g {!!}
    where f : OutFrame U w → Σ (Type ℓ) (λ X → μ-mgm w == X)
          f (X , frm) = (X , (ua (lower-equiv ∘e frm _  ∘e μ-leaf-eq _)))

          g : Σ (Type ℓ) (λ X → μ-mgm w == X) → OutFrame U w
          g (X , frm) = (X , λ _ → lower-equiv ⁻¹ ∘e coe-equiv frm ∘e μ-leaf-eq _ ⁻¹)

          f-g : f ∘ g ∼ idf _
          f-g (X , frm) =
            let pth : ua (lower-equiv ∘e (lower-equiv ⁻¹ ∘e coe-equiv frm ∘e μ-leaf-eq _ ⁻¹) ∘e μ-leaf-eq w) == frm
                pth = {!!} 
            in pair= idp pth

  U-is-good : is-good U
  U-is-good w = equiv-preserves-level (OutFrame-eq w ⁻¹) ⦃ pathfrom-is-contr _ ⦄


  -- What follows is the proof that (U // ⟪ U-mgm ⟫) is not good
  -- We consider the type Unit × Bool and the pasting diagram which associates nd (Unit , λ _ → corolla U Bool) with its corresponding two nodes.
  -- We then show that both nd (Unit , λ _ _ → corolla U Bool)) and nd (Bool , λ { _ false → lf _ ; _ true → corolla U Unit }) are the first components of
  -- two distinct elements of OutFrame (U // ⟪ U-mgm ⟫) pd.
  -- Supposing OutFrame (U // ⟪ U-mgm ⟫) pd is contractile, this allows us to derive an equality on the two trees implying, in particular, that Unit == Bool which
  -- is not the case.
  

  A = Lift {lzero} {ℓ} ⊤
 
  B = Lift {lzero} {ℓ} Bool

  A×B = A × B
          
  w : W U _
  w = nd (A , λ _ _ → corolla U B)
                                 
  fr : Frame U w A×B
  fr _ = equiv f g f-g g-f
    where f : Leaf U w _ → Lift A×B
          f (_ , _ , (_ , lift x , idp)) = lift (_ , x)
                                                     
          g : Lift A×B → Leaf U w _
          g (lift (_ , x)) = (_ , _ , (_ , lift x , idp))
                                                    
          f-g : f ∘ g ∼ idf _
          f-g (lift (_ , x)) = idp
                               
          g-f : g ∘ f ∼ idf _
          g-f (_ , _ , (_ , lift x , idp)) = idp
                                             
  α : (μ-mgm w , μ-mgm-frm w) == (A×B , fr)
  α = contr-has-all-paths ⦃ U-is-good  w ⦄ _ _
                                               
  δ : (f : Ops U) (n : Node U w f) → W (U // ⟪ U-mgm ⟫) f
  δ .(_ , A) (inl idp) = corolla (U // ⟪ U-mgm ⟫) ((w' , fr') , α')
     where w'  = corolla U A
           fr' = corolla-frm U A
                              
           α' : μ-mgm w' , μ-mgm-frm w' == A , fr'
           α' = contr-has-all-paths ⦃ U-is-good  w' ⦄ _ _            
  δ .(_ , B) (inr (_ , lift y , inl idp)) = corolla (U // ⟪ U-mgm ⟫) (((w' , fr') , α'))
     where w'  = corolla U B
           fr' = corolla-frm U B

           α' : μ-mgm w' , μ-mgm-frm w' == B , fr'
           α' = contr-has-all-paths ⦃ U-is-good  w' ⦄ _ _
  δ _ (inr (_ , _ , inr ()))
    
  pd : W (U // ⟪ U-mgm ⟫) (_ , A×B)
  pd = nd ((((w , fr) , α)) , δ)

  out-frm : OutFrame (U // ⟪ U-mgm ⟫) pd
  out-frm = (((w , fr) , α) , bd-frm _ pd)

  w' : W U _
  w' = nd (B , λ { _ (lift (lift true)) → corolla U A ; _ (lift (lift false)) → lf _ })

  nodes-eq : (f : Ops U) → Node U w f ≃ Node U w' f
  nodes-eq (_ , X) = equiv f g f-g g-f
    where f : Node U w (_ , X) → Node U w' (_ , X)
          f (inl idp) = inr (_ , lift (lift true) , inl idp)
          f (inr (_ , _ , inl idp)) = inl idp
          f (inr (_ , _ , inr ()))

          g : Node U w' (_ , X) → Node U w (_ , X)
          g (inl idp) = inr (_ , _ , inl idp)
          g (inr (_ , lift (lift true) , inl idp)) = inl idp
          g (inr (_ , lift (lift true) , inr ()))
          g (inr (_ , lift (lift false) , ()))

          f-g : f ∘ g ∼ idf _
          f-g (inl idp) = idp
          f-g (inr (_ , lift (lift true) , inl idp)) = idp
          f-g (inr (_ , lift (lift true) , inr ()))
          f-g (inr (_ , lift (lift false) , ()))

          g-f : g ∘ f ∼ idf _
          g-f (inl idp) = idp
          g-f (inr (_ , _ , inl idp)) = idp
          g-f (inr (_ , _ , inr ()))

  leaves-eq : Leaf U w _ ≃ Leaf U w' _
  leaves-eq = equiv f g f-g g-f
    where f : Leaf U w _ → Leaf U w' _
          f (_ , _ , (_ , lift (lift false) , idp)) = (_ , lift (lift false) , idp)
          f (_ , _ , (_ , lift (lift true) , idp)) = (_ , lift (lift true) , (_ , _ , idp))

          g : Leaf U w' _ → Leaf U w _
          g (_ , lift (lift false) , idp) = (_ , _ , (_ , lift (lift false) , idp))
          g (_ , lift (lift true) , (_ , _ , idp)) = (_ , _ , (_ , lift (lift true) , idp)) 

          f-g : f ∘ g ∼ idf _
          f-g (_ , lift (lift false) , idp) = idp
          f-g (_ , lift (lift true) , (_ , _ , idp)) = idp

          g-f : g ∘ f ∼ idf _
          g-f (_ , _ , (_ , lift (lift false) , idp)) = idp
          g-f (_ , _ , (_ , lift (lift true) , idp)) = idp

  fr' : Frame U w' A×B
  fr' _ = (fr _) ∘e leaves-eq ⁻¹

  α' : (μ-mgm w' , μ-mgm-frm w') == (A×B , fr')
  α' = contr-has-all-paths ⦃ U-is-good  w' ⦄ _ _

  out-frm' : OutFrame (U // ⟪ U-mgm ⟫) pd
  out-frm' = (((w' , fr') , α') , λ j → nodes-eq _ ∘e bd-frm _ pd j)

  w≠w' : w ≠ w'
  w≠w' p = contrad (coe-equiv A=B) 
    where A=B : A == B 
          A=B = fst (<– (W=-eq _ _) p)

          contrad : ¬ (A ≃ B)
          contrad q = {! !}
          

  out-frm≠out-frm' : out-frm ≠ out-frm' 
  out-frm≠out-frm' p = w≠w' (fst= (fst= (fst= p)))

  U//⟪U-mgm⟫-not-good : ¬ (is-good (U // ⟪ U-mgm ⟫))    
  U//⟪U-mgm⟫-not-good p = out-frm≠out-frm' (contr-has-all-paths ⦃ p pd ⦄ _ _)
