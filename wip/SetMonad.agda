{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import Util
open import UniCat
open import Biased
open import PolyMonad

module wip.SetMonad where

  --MgmRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  --MgmRel {P = P} M (i , f) (w , α) = Path {A = OutFrame P w} (μ M w , μ-frm M w) (f , α)
            
  --
  --  Our definition of a set-level monad.
  --

  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) (Mgm : PolyMagma P) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      outfrm-is-set : {i : I} (w : W P i) → is-set (OutFrame P w)
      invar       : SubInvar ⟪ Mgm ⟫

  open SetMonad

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (B : BiasedMgm P) where


{-
    -- Derived data

    homPoly : Poly (Ops P)
    homPoly = P // (↑ R)

    homRel : PolyRel homPoly
    homRel = FlattenRel (↑ R)

    -- Level calculations

    W-is-set : (i : I) → is-set (W P i)
    W-is-set = W-level P (op-is-set M) 

    hom-sort-is-gpd : is-gpd (Ops P)
    hom-sort-is-gpd = Σ-level (sort-is-gpd M) (λ i → raise-level _ (op-is-set M i))

    hom-op-is-set : (f : Ops P) → is-set (Op homPoly f)
    hom-op-is-set (i , f) = Σ-level (W-is-set i) (λ w →
      Σ-level (Frame-level P (sort-is-gpd M) (arity-is-set M) w f) (λ α → raise-level _
      (Σ-level (rel-is-prop M w f α) (λ _ → Lift-level Unit-level))))

    hom-arity-is-set : {f : Ops P} (pd : Op homPoly f) → is-set (Arity homPoly pd)
    hom-arity-is-set pd = Node-level P (arity-is-set M) (fst pd)

    hom-rel-is-prop : {f : Ops P} (pd : W homPoly f) (w : Op homPoly f)
      (α : Frame homPoly pd w) → is-prop (homRel pd w α)
    hom-rel-is-prop {i , f} pd (w , α , r) β = Σ-level
      (Σ-level (rel-is-prop M (flatten (↑ R) pd) f (flatten-frm (↑ R) pd)) (λ _ → Lift-level Unit-level))
      (λ s → has-level-apply (Σ-level (Σ-level (W-is-set i)
        (λ w₀ → Σ-level (Frame-level P (sort-is-gpd M) (arity-is-set M) w₀ f)
        (λ α₀ → raise-level _ (Σ-level (rel-is-prop M w₀ f α₀) (λ _ → Lift-level Unit-level)))))
        (λ w₁ → Frame-level (P // ↑ R) hom-sort-is-gpd hom-arity-is-set pd w₁))
         ((flatten (↑ R) pd , flatten-frm (↑ R) pd , s) , bd-frame (↑ R) pd)
         ((w , α , r) , β))

    -- Maybe there is a faster way?
    postulate
      hom-is-multip : {f : Ops P} (pd : W homPoly f) → is-contr (Composite homPoly homRel pd)
      
    -- hom-is-multip {i , f} pd = has-level-in (ctr , pth)

    --   where ctr : Composite homPoly homRel pd
    --         ctr = (flatten (↑ R) pd , flatten-frm (↑ R) pd , laws M f pd) ,
    --           bd-frame (↑ R) pd , laws M f pd , idp

    --         pth : (c : Composite homPoly homRel pd) → ctr == c
    --         pth ((._ , ._ , ._) , ._ , (m , lift tt) , idp) =
    --           pair= (pair= idp (pair= idp (pair=
    --             (prop-has-all-paths ⦃ rel-is-prop M (flatten (↑ R) pd) f (flatten-frm (↑ R) pd) ⦄
    --               (fst (laws M f pd)) m) (↓-cst-in idp)))) {!!}
    
    -- Derived laws
    hom-laws : {f : Ops P} (pd : Op homPoly f)
      → (coh : W (homPoly // (↑ homRel)) (f , pd))
      → (↑ homRel) (flatten (↑ homRel) coh) pd (flatten-frm (↑ homRel) coh)
    hom-laws {i , f} (w , α , r) coh =
      (s , globularity R (TRef R) (TRef homRel) w α r coh s q) , lift tt

      where s = laws M f (flatten (↑ homRel) coh)

            q : s == r [ uncurry (λ a → (↑ R) a f) ↓
                  pair= (flatten-flatten R (TRef R) (TRef homRel) w α r coh)
                  (flatten-frm-flatten R (TRef R) (TRef homRel) w α r coh) ]
            q = prop-has-all-paths-↓ {B = uncurry (λ a → (↑ R) a f)}
                  ⦃ Σ-level (rel-is-prop M w f α) (λ _ → Lift-level Unit-level) ⦄

    homMnd : SetMonad homPoly homRel
    sort-is-gpd homMnd = hom-sort-is-gpd
    op-is-set homMnd = hom-op-is-set
    arity-is-set homMnd = hom-arity-is-set
    rel-is-prop homMnd = hom-rel-is-prop
    is-multip homMnd = hom-is-multip
    laws homMnd = hom-laws

  -- Now, we want to define an OpetopicType associated to our monad
  MndType : ∀ {ℓ} {I : Type ℓ} (P : Poly I) (R : PolyRel P) (M : SetMonad P R) → OpetopicType P R
  Ref (MndType P R M) w f α r = Lift ⊤
  hom (MndType P R M) = MndType (homPoly R M) (homRel R M) (homMnd R M)

  set-mnd-is-algebraic : ∀ {ℓ} {I : Type ℓ} {P : Poly I} {R : PolyRel P} (M : SetMonad P R)
    → is-algebraic (MndType P R M)
  is-mult (set-mnd-is-algebraic {R = R} M) = ↑-is-mult R (is-multip M) 
  hom-is-alg (set-mnd-is-algebraic {R = R} M) =
    set-mnd-is-algebraic (homMnd R M)
-}

  
  record CatMonad i : Type (lsucc i)  where
    field
      I         : Type i
      P         : Poly I
      ply-mgm  : PolyMagma P
      mnd       : SetMonad P ply-mgm
      unary     : {i : I} (f : Op P i) → is-contr (Arity P f)
  
  open UniCat.Category
  open BiasedMgm
  open BiasedLaws

  module _ {lobj} (C : Category lobj (lsucc lobj)) where

    I : Type (lsucc lobj)
    I = Lift (obj C)

    P : Poly I 
    Op    P (lift i)         = Σ (obj C) (λ j → hom C j i)
    Param P (j , _) (lift i) = Lift (j == i)

    lf-equiv-pth : {i : I} (w : W P i) → Σ I (λ k → (j : I) → (Leaf P w j) ≃ (k == j)) 
    lf-equiv-pth (lf i) = i , λ _ → ide _
    lf-equiv-pth {i} w@(nd ((k , f) , ϕ)) =
      let (k' , e) = lf-equiv-pth (ϕ _ (lift idp))
      in (k' , λ j → (e j) ∘e (lem j))
        where     
          lem : (j : I) → Leaf P w j ≃ Leaf P (ϕ _ (lift idp)) j 
          lem j = equiv g h g-h h-g
            where g : Leaf P w j → Leaf P (ϕ _ (lift idp)) j
                  g (_ , lift idp , l') =  l'
                  
                  h : Leaf P (ϕ _ (lift idp)) j → Leaf P w j
                  h l = (lift k , lift idp , l)
                  
                  g-h : (l : Leaf P (ϕ _ (lift idp)) j) → (g ∘ h) l == l
                  g-h l = idp
                  
                  h-g : (l : Leaf P w j) → (h ∘ g) l == l
                  h-g (_ , lift idp , l') = idp

    lem : {i : I} (w : W P i) → Σ (obj C) (λ k → OutFrame P w ≃ hom C k (lower i))
    lem {i} w =

      let (n , e) = lf-equiv-pth w
                
          outfrm-equiv-hom : OutFrame P w ≃ hom C (lower n) (lower i)
          outfrm-equiv-hom = OutFrame P w                                                             ≃⟨ ide _ ⟩
                Σ (Op P i) (λ f → (j : I) → Leaf P w j ≃ Param P f j)                    ≃⟨ Σ-emap-r (λ f → Π-emap-r λ j → ≃-emap-l (e j)) ⟩
                Σ (Op P i) (λ { (k , f) → (j : I) → (n == j) ≃ Lift (k == lower j) })    ≃⟨ Σ-emap-r (λ f → Π-emap-r λ j → ≃-emap-r ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv) )⟩
                Σ (Op P i) (λ { (k , f) → (j : I) → (n == j) ≃ (lift k == j) })          ≃⟨ Σ-emap-r (λ { (k , f) → pth-yoneda _ _ } ) ⟩
                Σ (Op P i) (λ { (k , f) → lift k == n })                                 ≃⟨ Σ-assoc  ⟩ 
                Σ (obj C) (λ k → (hom C k (lower i)) × (lift k == n))                    ≃⟨ Σ-emap-r (λ k → ×-comm) ⟩
                Σ (obj C) (λ k → (lift k == n) × (hom C k (lower i)))                    ≃⟨ Σ-assoc ⁻¹  ⟩
                Σ (Σ (obj C) (λ k → (lift k == n))) (λ { (k , _) → hom C k (lower i) })  ≃⟨ Σ-emap-l _ (Σ-emap-r (λ k → pth-lift-equiv _ _)) ⟩
                Σ (Σ (obj C) (λ k → (k == lower n))) (λ { (k , _) → hom C k (lower i) }) ≃⟨ Σ-contr-base _ (pathto-is-contr _) ⟩
                hom C (lower n) (lower i)                                                ≃∎ 
                
      in (lower n , outfrm-equiv-hom)

    OutFrame-is-set : {i : I} (w : W P i) → is-set (OutFrame P w)
    OutFrame-is-set w =
      let (k , p) = lem w
      in transport is-set (! (ua p)) (homs-sets C _ _)
   
    bsd-mgm : BiasedMgm P
    η            bsd-mgm (lift i) = (i , id C)
    η-frm        bsd-mgm i j = equiv ( λ {idp → lift idp}) (λ { (lift idp) → idp }) (λ { (lift idp) → idp }) λ {idp → idp}
    γ            bsd-mgm (k , g) ϕ =
      let (j , f) = ϕ (lift k) (lift idp)
      in j , _●_ C g f
    γ-frm        bsd-mgm (j , f) ϕ (lift k) = equiv ( λ { (.(lift j) , lift idp , lift idp)  → lift idp }) (λ { (lift idp) → (lift j , lift idp , lift idp)}) ( λ { (lift idp) → idp }) λ { (.(lift j) , lift idp , lift idp)  → idp }

    bsd-mgm-invar : BiasedLaws P bsd-mgm
    unit-l     bsd-mgm-invar (j , f)                       = pair= idp (unit-r C f)
    unit-l-frm bsd-mgm-invar (j , f) .(lift j) (lift idp)  =
      let pth = transport (λ p → lift idp == lift idp [ (λ k → Lift (k == j)) ↓ p ]) (! (fst=-β idp (unit-r C f))) idp
      in ↓-ap-out _ fst (unit-l bsd-mgm-invar (j , f)) pth  
    unit-r     bsd-mgm-invar  ϕ   = pair= idp (! (unit-l C _))
    unit-r-frm bsd-mgm-invar ϕ (lift j) (lift idp) =
      let pth = transport (λ p → lift idp == lift idp [ (λ k → Lift (k == j)) ↓ p ]) (! (fst=-β idp (! (unit-l C _)))) idp 
      in ↓-ap-out _ fst (unit-r bsd-mgm-invar ϕ) pth
    assoc      bsd-mgm-invar f ϕ ψ  = pair= idp (! (assoc C _ _ _))
    assoc-frm  bsd-mgm-invar f ϕ ψ j k (lift idp) l (lift idp) (lift idp) =
      let pth = transport (λ p → lift idp == lift idp [ (λ m → Lift (m == _)) ↓ p ]) (! (fst=-β idp (! (assoc C _ _ _)))) idp
      in ↓-ap-out _ fst (assoc bsd-mgm-invar f ϕ ψ) pth

    ply-mgm : PolyMagma P
    ply-mgm = BsdMgm P bsd-mgm

    mnd : SetMonad P ply-mgm
    sort-is-gpd mnd = has-level-in (λ x y →
      equiv-preserves-level ((pth-lift-equiv _ _) ⁻¹ ∘e (univalent C (lower x) (lower y)))
                            ⦃ ≊-is-set _ _ ⦄)
    outfrm-is-set mnd = OutFrame-is-set
    invar         mnd = μ-bsd-invar _ _ bsd-mgm-invar

    Fun : CatMonad (lsucc lobj)
    CatMonad.I       Fun = I
    CatMonad.P       Fun = P
    CatMonad.ply-mgm Fun = ply-mgm 
    CatMonad.mnd     Fun = mnd
    CatMonad.unary   Fun (j , f) = has-level-in ((lift j , lift idp) , λ {(lift k , lift idp) →  idp })
