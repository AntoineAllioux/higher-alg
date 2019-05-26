{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
--open import SubstCoh
--open import Monad
--open import Globularity
open import Util
open import UniCat
--open import Biased
open import PolyMonad
open import PolyMagma
import wip.NotGood

module wip.SetMonad where

  --MgmRel : ∀ {ℓ} {I : Type ℓ} {P : Poly I} (M : PolyMagma P) → PolyRel P
  --MgmRel {P = P} M (i , f) (w , α) = Path {A = OutFrame P w} (μ M w , μ-frm M w) (f , α)
            
  --
  --  Our definition of a set-level monad.
  --

  module _ {ℓ} {I : Type ℓ} (P : Poly I) where
    corolla-pth-lift : {i : I} {f f' : Op P i} (p : f == f') → corolla P f == corolla P f'
    corolla-pth-lift idp = idp 

  record SetMonad {ℓ} {I : Type ℓ} (P : Poly I) (Mgm : PolyMagma P) : Type ℓ where
    field

      sort-is-gpd : is-gpd I
      opfr-is-set : {i : I} (w : W P i) → is-set (OutFrame P w)
      -- rel-is-prop : {i : I} (w : W P i) (f : Op P i) (α : Frame P w f) → is-prop (⟪ Mgm ⟫ (i , f) (w , α))
      invar       : SubInvar ⟪ Mgm ⟫

  open SetMonad


  module _ {ℓ} where
    open wip.NotGood ℓ

    U-is-set-monad : SetMonad U U-mgm
    opfr-is-set U-is-set-monad w = raise-level _ (raise-level _ (U-is-good _))
    invar       U-is-set-monad   = {!!} 
    sort-is-gpd U-is-set-monad   = equiv-preserves-level (lower-equiv ⁻¹) ⦃ Unit-level ⦄

    B = Lift {_} {ℓ} Bool

    w : W U _
    w = corolla U B

    pouet : Frame U w B
    pouet _ = equiv f g f-g g-f
      where f : Leaf U w _ → Lift B
            f (_ , b , idp) = b

            g : Lift B → Leaf U w _
            g b = (_ , b , idp)

            f-g : f ∘ g ∼ idf _
            f-g _ = idp

            g-f : g ∘ f ∼ idf _
            g-f (_ , _ , idp) = idp

    fr = corolla-frm U B

    α : (μ-mgm w , μ-mgm-frm w) == (B , fr)
    α = contr-has-all-paths ⦃ U-is-good _ ⦄ _ _ 

    pd : W (U // ⟪ U-mgm ⟫) (_ , B)
    pd = corolla _ ((w , fr) , α)

    fr↑ = bd-frm _ pd

    out-frm : OutFrame (U // ⟪ U-mgm ⟫) pd
    out-frm = (((w , fr) , α)) , fr↑

    negate : Bool → Bool
    negate true = false
    negate false = true

    negate-lem : negate ∘ negate ∼ idf _
    negate-lem true = idp
    negate-lem false = idp

    negate-pth : Bool == Bool
    negate-pth = ua (equiv negate negate negate-lem negate-lem)

    negate-pth≠idp : negate-pth ≠ idp
    negate-pth≠idp p = Bool-false≠true (transport (λ x → x == true) (coe-β _ _) (app= (ap coe p) true)) 

    

    w=w : w == w
    w=w = corolla-pth-lift _ (ap Lift negate-pth) -- –> (W=-eq _ _) (ap Lift negate-pth , from-transp _ _ {!!})

    fr' : Frame U w B
    fr' = transport (λ w → Frame U w B) w=w fr

    transp-↓' : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
      (p : a₁ == a₂) (y : P a₁) → y == transport P p y [ P ↓ p ]
    transp-↓' _ idp _ = idp

    fr=fr' : fr == fr' [ (λ w → Frame U w B) ↓ w=w ]
    fr=fr' = transp-↓' _ _ _

    α' : ⟪ U-mgm ⟫ (lift tt , B) (w , fr')
    α' = contr-has-all-paths ⦃ U-is-good  w ⦄ _ _

    α=α' : α == α' [ (λ { (w , fr) → ⟪ U-mgm ⟫ (lift tt , B) (w , fr) }) ↓ pair= w=w fr=fr' ]
    α=α' = from-transp _ _ (contr-has-all-paths ⦃ =-preserves-level (U-is-good _) ⦄ _ _)

    fr↑' = transport (λ { ((w , fr) , α) → Frame _ pd ((w , fr) , α) } ) (pair= (pair= w=w fr=fr') α=α') fr↑

    fr↑=fr↑' : fr↑ == fr↑' [ (λ { ((w , fr) , α) → Frame _ pd ((w , fr) , α) } ) ↓ (pair= (pair= w=w fr=fr') α=α') ]
    fr↑=fr↑' = transp-↓' _ _ _

    out-frm' : OutFrame (U // ⟪ U-mgm ⟫) pd
    out-frm' = (((w , fr') , α') , fr↑')

    out-frm=out-frm' : out-frm == out-frm'
    out-frm=out-frm' = pair= (pair= (pair= w=w fr=fr') α=α') fr↑=fr↑'

{-

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
    w-coe : {i j k : I} {f : Op P i} (p : Param P f j) (w : W P j) (q : Param P f k) → W P k
    w-coe {i} {j} {k} {f} p w q = transport (W P) (fst= (contr-has-all-paths {{(unary f)}} (j , p) (k , q))) w
    indices-eq-par : {i j k : I} {f : Op P i} (p : Param P f j) (p' : Param P f k) → j == k
    indices-eq-par {i} {j} {k} {f} p p' = ap fst (contr-path' (unary f) (j , p) (k , p'))
    indices-eq-par' : {i j k : I} {w : W P i} (l : Leaf P w j) (l' : Leaf P w k) → j == k
    indices-eq-par' {i} {j} {k} {w} l l' =  indices-eq-par (–> (μ-frm ply-mgm w j) l) (–> (μ-frm ply-mgm w k) l')
    par-uniq : {i j k : I} {f : Op P i} (p : Param P f j) (p' : Param P f k) → p == p' [ (λ (x : Σ I (Param P f)) → Param P f (fst x)) ↓ (contr-path' (unary f) (j , p) (k , p')) ] 
    par-uniq {i} {j} {k} {f} p p' = apd snd (contr-path' (unary f) (j , p) (k , p'))
    par-eq : {i j k : I} {w : W P i} (l : Leaf P w j) (l' : Leaf P w k) → (j , –> (μ-frm ply-mgm w j) l) == (k , –> (μ-frm ply-mgm w k) l')
    par-eq {i} {j} {k} {w}  l l' = contr-path' (unary (μ ply-mgm w)) (j , (–> (μ-frm ply-mgm w j) l)) (k , (–> (μ-frm ply-mgm w k) l'))

    canonical-lf : {i : I} (w : W P i) → Σ I (Leaf P w)
    canonical-lf (lf i) = i , idp
    canonical-lf (nd (f , δ)) =
      let x   = contr-center (unary f)
          hyp = canonical-lf (δ (fst x) (snd x))
      in fst hyp , (fst x , snd x , snd hyp)

{-  contr-lf : {i : I} (w : W P i) → is-contr (Σ I (Leaf P w))
    contr-lf (lf i) = has-level-in (((i , idp)) , λ { (.i , idp) → idp})
    contr-lf (nd (f , δ)) =
      let x   = contr-center (unary f)
          hyp = contr-lf (δ (fst x) (snd x))
      in has-level-in (canonical-lf (nd x) , λ { (j , l) → {!!} }) -}
{-
    canonical-par : {i : I} (w : W P i) → Σ I (λ j → Σ (Op P j) (λ f → Σ I (Param P f)))
    canonical-par (lf i) = {!!}
    canonical-par (nd x) = {!!}
-}
    lf-uniq : {i j k : I} {w : W P i} (l : Leaf P w j) (l' : Leaf P w k) → l == l' [ Leaf P w ↓ indices-eq-par' l l' ]
    lf-uniq {i} {j} {k} {w} l l' =
      let 
          par-eq' : (–> (μ-frm ply-mgm w j) l) == (–> (μ-frm ply-mgm w k) l') [ (λ (x : Σ I (Param P (μ ply-mgm w))) → Param P (μ ply-mgm w) (fst x)) ↓ par-eq l l' ] 
          par-eq' = apd snd (par-eq l l')

          par-eq'' : (–> (μ-frm ply-mgm w j) l) == (–> (μ-frm ply-mgm w k) l') [ Param P (μ ply-mgm w) ↓ indices-eq-par' l l' ] 
          par-eq'' = ↓-ap-in (Param P (μ ply-mgm w)) (fst) (apd snd (par-eq l l'))
           
       in apd↓ (λ {m} p → <– (μ-frm ply-mgm w m) p) par-eq''
            >> transport (λ x → x == (<– (μ-frm ply-mgm w k)) (–> (μ-frm ply-mgm w k) l') [ (λ { (m , _) → Leaf P w m }) ↓ pair= (indices-eq-par' l l') par-eq'' ]) (<–-inv-l (μ-frm ply-mgm w j) l)
            >> transport (λ x → l == x [ (λ { (m , _) → Leaf P w m }) ↓ pair= (indices-eq-par' l l') par-eq'' ]) (<–-inv-l (μ-frm ply-mgm w k) l')
            >> ↓-ap-in (Leaf P w) fst
            >> transport (λ x → l == l' [ Leaf P w ↓ x ]) (fst=-β (indices-eq-par' l l') par-eq'')
{-
    lf-uniq' : {i j : I} {w : W P i} (l l' : Leaf P w j) → l == l' [ Leaf P w ↓ indices-eq-par' l l' ]
    lf-uniq' {i} {j} {w} l l' =
      let 

          par-eq'' : (–> (μ-frm ply-mgm w j) l) == (–> (μ-frm ply-mgm w j) l') [ Param P (μ ply-mgm w) ↓ indices-eq-par' l l' ] 
          par-eq'' = ↓-ap-in (Param P (μ ply-mgm w)) (fst) (apd snd (par-eq l l'))
           
       in apd↓ (λ {m} p → <– (μ-frm ply-mgm w m) p) par-eq''
            >> transport (λ x → x == (<– (μ-frm ply-mgm w j)) (–> (μ-frm ply-mgm w j) l') [ (λ { (m , _) → Leaf P w m }) ↓ pair= (indices-eq-par' l l') par-eq'' ]) (<–-inv-l (μ-frm ply-mgm w j) l)
            >> transport (λ x → l == x [ (λ { (m , _) → Leaf P w m }) ↓ pair= (indices-eq-par' l l') par-eq'' ]) (<–-inv-l (μ-frm ply-mgm w j) l')
            >> ↓-ap-in (Leaf P w) fst
            >> transport (λ x → l == l' [ Leaf P w ↓ x ]) (fst=-β (indices-eq-par' l l') par-eq'')

    mul : {i : I} (w : W P i) → Op P i
    mul = μ ply-mgm  -- fst (contr-center (is-multip M w))
    op-id : (i : I) → Σ (Op P i) (λ f → (Param P f i))
    op-id i = (μ ply-mgm (lf i) , coe (ua (μ-frm ply-mgm (lf i) i)) idp) -}

  open UniCat.Category
  open BiasedMgm
  open BiasedLaws

  module _ {lobj} (C : Category lobj (lsucc lobj)) where

    pth-fib-contr : ∀ {i j} {A : Type i} (y : A) → is-contr {lmax i j} (Σ A (λ x → Lift {i} {j} (y == x)))
    pth-fib-contr y = has-level-in (((y , lift idp) , λ { (_ , lift idp) → idp })) 

    comp-helper : ∀ {lobj} {C : Category lobj (lsucc lobj)} {j k : obj C} (g : Σ (obj C) (λ j → hom C j k)) {p : fst g == j} (f : Σ (obj C) (λ i → hom C i j))  → Σ (obj C) (λ j → hom C j k)
    comp-helper {C = C} (j , g) {idp} (i , f) = (i , _●_ C g f)

    pth-lift-equiv : ∀ {i j} {A : Type i} (x y : A) → (lift {i} {j} x == lift y) ≃ (x == y)
    pth-lift-equiv _ _ = equiv (λ p → ap lower p) (λ p → ap lift p ) (λ p →  (∘-ap lower lift p) ∙ (ap-idf p) ) (λ p → (∘-ap lift lower p) ∙ (ap-idf p))

    lift-preserves-level : ∀ {i k} {A : Type i} {n : ℕ₋₂} → has-level n A ≃ has-level n (Lift {_} {k} A)
    lift-preserves-level = equiv f g f-g g-f
      where f : ∀ {i k} {A : Type i} {n : ℕ₋₂} → has-level n A → has-level n (Lift {_} {k} A)
            f {n = ⟨-2⟩}  (has-level-in (ctr , pth)) = has-level-in (lift ctr , λ { (lift y) → ap lift (pth y)})
            f {k = k} {n = (S n)} (has-level-in p) = has-level-in λ { (lift x) (lift y) → transport (has-level n) (ua ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv {_} {k})) (f (p x y)) }

            g : ∀ {i k} {A : Type i} {n : ℕ₋₂} → has-level n (Lift {_} {k} A) → has-level n A
            g {n = ⟨-2⟩}  (has-level-in (lift ctr , pth)) = has-level-in (ctr , λ y → ap lower (pth (lift y)))
            g {n = (S n)} (has-level-in p) = has-level-in λ x y → g (transport! (has-level n) (ua ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv)) (p (lift x) (lift y)))

            f-g : ∀ {i k} {A : Type i} {n : ℕ₋₂} (p : has-level n (Lift {_} {k} A)) → (f ∘ g) p == p
            f-g {n = ⟨-2⟩} (has-level-in (ctr , pth)) = ap (λ x → has-level-in (ctr , x)) (λ= λ { (lift y) →  (∘-ap _ _ _) ∙ (ap-idf _)  })
            f-g {n = S n} (has-level-in p) = ap has-level-in (λ= λ x → λ= λ y → ap (transport (has-level n) (ua ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv))) (f-g (transport! (has-level n) (ua ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv)) (p x y))) ∙ coe!-inv-r (ap (has-level n) (ua ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv))) (p x y))

            g-f : ∀ {i} {A : Type i} {n : ℕ₋₂} (p : has-level n A) → (g ∘ f) p == p
            g-f {n = ⟨-2⟩} (has-level-in (ctr , pth)) = ap (λ x → has-level-in (ctr , x)) ((λ= λ y → (∘-ap _ _ _) ∙ (ap-idf _)))
            g-f {n = S n} (has-level-in p) = ap has-level-in (λ= λ x → λ= λ y → ap g (coe!-inv-l (ap (has-level n) (ua ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv))) _) ∙ g-f _)


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

          bar : ∀ {i} {A B C : Type i} (p : A ≃ B) → (A ≃ C) ≃ (B ≃ C)
          bar p =
            let f q = q ∘e p ⁻¹
                g q = q ∘e p
                f-g q = ∘e-assoc _ _ _ ∙ (ap (_∘e_ q) (∘e-inv-r p)) ∙ ∘e-unit-r q
                g-f q = ∘e-assoc _ _ _ ∙ (ap (_∘e_ q) (∘e-inv-l p)) ∙ ∘e-unit-r q

            in equiv f g f-g g-f

          bar' : ∀ {i} {A B C : Type i} (p : B ≃ C) → (A ≃ B) ≃ (A ≃ C)
          bar' p =
            let f q = p ∘e q
                g q = p ⁻¹ ∘e q
                f-g q = ! (∘e-assoc _ _ _) ∙ ap (λ r → r ∘e q) (∘e-inv-r p) ∙ ∘e-unit-l q
                g-f q = ! (∘e-assoc _ _ _) ∙ ap (λ r → r ∘e q) (∘e-inv-l p) ∙ ∘e-unit-l q

            in equiv f g f-g g-f
            
          foo : OutFrame P w ≃ hom C (lower n) (lower i)
          foo = OutFrame P w                                                             ≃⟨ ide _ ⟩
                Σ (Op P i) (λ f → (j : I) → Leaf P w j ≃ Param P f j)                    ≃⟨ Σ-emap-r (λ f → Π-emap-r λ j → bar (e j)) ⟩
                Σ (Op P i) (λ { (k , f) → (j : I) → (n == j) ≃ Lift (k == lower j) })    ≃⟨ Σ-emap-r (λ f → Π-emap-r λ j → bar' ((pth-lift-equiv _ _) ⁻¹ ∘e lower-equiv)) ⟩
                Σ (Op P i) (λ { (k , f) → (j : I) → (n == j) ≃ (lift k == j) })          ≃⟨ Σ-emap-r (λ f → pth-yoneda _ _) ⟩
                Σ (Op P i) (λ { (k , f) → lift k == n })                                 ≃⟨ Σ-assoc  ⟩ 
                Σ (obj C) (λ k → (hom C k (lower i)) × (lift k == n))                    ≃⟨ Σ-emap-r (λ k → ×-comm) ⟩
                Σ (obj C) (λ k → (lift k == n) × (hom C k (lower i)))                    ≃⟨ Σ-assoc ⁻¹  ⟩
                Σ (Σ (obj C) (λ k → (lift k == n))) (λ { (k , _) → hom C k (lower i) })  ≃⟨ Σ-emap-l _ (Σ-emap-r (λ k → pth-lift-equiv _ _)) ⟩
                Σ (Σ (obj C) (λ k → (k == lower n))) (λ { (k , _) → hom C k (lower i) }) ≃⟨ Σ-contr-base _ (pathto-is-contr _)  ⟩
                hom C (lower n) (lower i)                                                ≃∎ 
                
      in (lower n , foo)

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
      equiv-preserves-level ((pth-lift-equiv _ _) ⁻¹ ∘e (unival {C = C} (lower x) (lower y)))
                            {{≊-is-set _ _}})
    opfr-is-set mnd = OutFrame-is-set
    rel-is-prop mnd w _ _ = has-level-apply (OutFrame-is-set w) _ _
    invar       mnd = μ-bsd-invar _ _ bsd-mgm-invar

    Fun : CatMonad (lsucc lobj)
    CatMonad.I       Fun = I
    CatMonad.P       Fun = P
    CatMonad.ply-mgm Fun = ply-mgm 
    CatMonad.mnd     Fun = mnd
    CatMonad.unary   Fun (j , f) = has-level-in ((lift j , lift idp) , λ {(lift k , lift idp) →  idp })

{-
    --{-# TERMINATING #-}
    Fun : CatMonad {lsucc lobj}

    BinOp : BiasedMgm P
    BinOp = biased-mgm (ply-mgm Fun) (laws (M Fun))

    BinLaws : BiasedLaws P BinOp 
    BinLaws = biased-mgm-laws (ply-mgm Fun) (laws (M Fun))

    OutFrame-is-set : {i : I Fun} (w : W P i) → is-set (OutFrame P w)

    I : Type
    I = Lift (obj C)

    P : Poly I 
    Op    P (lift i)         = Σ (obj C) (λ j → hom C j i)
    Param P (j , _) (lift i) = Lift (j == i)


    I            Fun  = Lift (obj C)
    Op           P (lift i) = Σ (obj C) (λ j → hom C j i)
    Param        P (j , _) (lift i) = Lift (j == i)
    ply-mgm         Fun     = BsdMgm P BinOp
    sort-is-gpd  (M Fun) = has-level-in (λ x y →
      equiv-preserves-level ((pth-lift-equiv _ _) ⁻¹ ∘e (unival {C = C} (lower x) (lower y)))
                            {{≊-is-set _ _}}) 
    opfr-is-set  (M Fun) = OutFrame-is-set 
    laws         (M Fun) = μ-bsd-invar _ _ BinLaws
    unary        Fun (j , f)  = has-level-in ((lift j , lift idp) , λ {(lift k , lift idp) →  idp })
    rel-is-prop  (M Fun) w f α = has-level-apply (OutFrame-is-set w) _ _

-}

    
    
    
    
  
    
{-
    Fun' : CatMonad {lsucc lobj}
    I            Fun'                                     = Lift (obj C × obj C) -- obj C
    Op           (P Fun') (lift (i , j))                  = Lift (hom C i j)     -- Op j = Σ I (λ i →hom C i j)
    Param        (P Fun') {lift (i , j)} f (lift (k , l)) = Lift (l == i) --  → Lift (l == i)        -- Param {i} (i , f) j = i == j 
    ply-mgm         Fun'         = {!!} -- BsdMgm P BinOp
    sort-is-gpd  (M Fun')     = {!!} 
    op-is-set    (M Fun') _   = {!!} --homs-sets C _ _ 
    arity-is-set (M Fun') {lift (i , _)} f =
      let foo : is-contr  (Arity (P Fun') f)
          foo = {!!} -- pth-fib-contr {lobj} {lsucc lobj} i -- (pth-fib-contr {lobj} {lsucc (lsucc lobj)} i)

          --lem : is-contr (Σ I (λ { (lift (k , l)) → Lift (l == i) }))
          --lem = has-level-in ((lift {!( , i)!} , {!idp!}) , {!!})

          --unary' : Σ I (λ { (lift (k , l)) → Lift (l == i) })

          bar : Arity (P Fun') f == Σ (I Fun') (λ { (lift (k , l)) → Lift (l == i) }) 
          bar = idp

          
      in raise-level {_} (S ⟨-2⟩) (raise-level {_} ⟨-2⟩  {!!}) --  
    laws (M Fun') = {!!} -- μ-bsd-invar _ _ BinLaws
    unary Fun' {i} _ = {!!} -- (j , f) = has-level-in ((lift j , lift idp) , λ {(lift k , lift idp) →  idp })
    rel-is-prop (M Fun') w f α = {!!}
-}
    
 

    -- R {P = P} {Mgm = Mgm} w f fr = Σ (μ ply-mgm w == f) (λ p → μ-frm ply-mgm w == fr [ Frame P w ↓ p ])          Show : Σ (μ ply-mgm (flatn (↑ R) pd) == (j , f)) (λ p → μ-frm ply-mgm (flatn (↑ R) pd) == (flatn-frm (↑ R) pd) [ Frame P (flatn (↑ R) pd) ↓ p ]) 

    
    --mgm : BiasedMgm P
    --mgm = biased-mgm ()Mgm 
    --η mgm i =
    --η-frm mgm
    --γ mgm 
    --γ-frm mgm 
{-

  module _ {lobj} (C : CatMonad {lobj}) where

    open import Grafting (P C)

    par-inv : ∀ {ℓ} {I : Type ℓ} (P : Poly I) {i j : I} (p : i == j) (f : Op P i) (k : I)
        → Param P f k ≃ Param P (transport (Op P) p f) k
    par-inv P idp f k = ide (Param P f k)



    {-# TERMINATING #-}
    Nuf : Category {lobj} {lobj}
    obj Nuf = I C
    hom Nuf i j = Σ (Op (P C) j) (λ f → Param (P C) f i)
    _●_ Nuf {i} {j} {k} (g , p) (f , q) =
      let mgm   = biased-mgm (ply-mgm C) (laws (M C))
          ϕ : (j' : I C) (p' : Param (P C) g j') → Op (P C) j'
          ϕ j' p' = transport _ (fst= (contr-path' (unary C g) (j , p) (j' , p'))) f 
          lf    = (j , p , –> (par-inv (P C) _ f i) q)

          --w = graft (corolla (P C) g) (λ { .k (k , p , idp) → (corolla (P C) f) })
      in (γ mgm g ϕ , –> (γ-frm mgm g ϕ i) lf)
   {-   let tr = nd (g , λ _ → w-coe C p (corolla (P C) f))
          op = μ (ply-mgm C) tr
          lf = (j , (p , –> (lf-inv (P C) (fst= (contr-path' (unary C g) (j , p) (j , p))) (corolla (P C ) f) i) (i , (q , idp))))
          par = –> (μ-frm (ply-mgm C) tr i) lf 
      in (op , par) -}
    -- μ (ply-mgm C) (nd (μ (ply-mgm C) (nd (h , λ _ → w-coe C r (corolla (P C) g)))  , (λ z → w-coe C (snd ((Nuf C ● h , r) (g , q))) (corolla P f))))
    -- == μ (ply-mgm C) (nd (h , (λ z → w-coe C r (nd (fst ((Nuf C ● g , q) (f , p)) , (λ j₁ p₁ → lf j₁))))))
    -- μ (nd ((μ (nd (h , λ _ → w-coe C r (corolla (P C) g)))) , λ _ → w-coe _ (corolla (P C) f)))
    -- == μ (nd (h , λ _ → w-coe C r (corolla (P C) (μ (ply-mgm C) (nd (g , λ _ → w-coe q (corolla (P C) f)))))))
    -- (Nuf C ● (Nuf C ● h , r) (g , q)) (f , p) == (Nuf C ● h , r) ((Nuf C ● g , q) (f , p))
    assoc Nuf {i} {j} {k} {l} (h , r) (g , q) (f , p) =
      let bsd-mgm   = biased-mgm (ply-mgm C) (laws (M C))
          bsd-mgm-laws = biased-mgm-laws (ply-mgm C) (laws (M C))

          -- left
          ϕ k' r' = transport _ (fst= (contr-path' (unary C h) (k , r) (k' , r'))) g
          
          lf-hg   = (k , r , –> (par-inv (P C) _ g j) q)
          hg-par  = –> (γ-frm bsd-mgm h ϕ j) lf-hg
          ψ j' q' = transport (Op (P C)) (fst= (contr-path' (unary C (γ bsd-mgm h ϕ)) (j , hg-par) (j' , q'))) f

          lf-hgf = (j , hg-par , –> (par-inv (P C) _ f i) p)
          hgf-par = –> (γ-frm bsd-mgm (γ bsd-mgm h ϕ) ψ i) lf-hgf

          -- right

          lf-gf = j , q , –> (par-inv (P C) _ f i) p 

          gf-par = –> (γ-frm bsd-mgm g (λ j' q' → transport (Op (P C)) ((fst= (contr-path' (unary C g) (j , q) (j' , q')))) f) i) lf-gf
          
          lf-hgf-left = (k , r , –> (par-inv (P C) _ (γ bsd-mgm g (λ j' q' → transport (Op (P C)) ((fst= (contr-path' (unary C g) (j , q) (j' , q')))) f )) i) gf-par)
          hgf-par-right = –> (γ-frm bsd-mgm h (λ k' r' → transport (Op (P C)) (fst= (contr-path' (unary C h) (k , r) (k' , r')))  (γ bsd-mgm g (λ j' q' → transport (Op (P C)) ((fst= (contr-path' (unary C g) (j , q) (j' , q')))) f ))) i) lf-hgf-left

          ψ' : (j' : I C) → Σ (I C) (λ k' → Σ (Param (P C) h k') (λ r' → Param (P C) (ϕ k' r') j')) → Op (P C) j'
          ψ' = λ { j' (k' , r' , q') → transport (Op (P C)) (fst= (contr-path' (unary C (γ bsd-mgm h ϕ)) (j , –> (γ-frm bsd-mgm h ϕ j) (k , r , –> (par-inv (P C) _ g j) q)) (j' , –> (γ-frm bsd-mgm h ϕ j') (k' , r' , q')))) f } 

          assoc' : γ bsd-mgm (γ bsd-mgm h ϕ) (λ j' p' → ψ' j' (<– (γ-frm bsd-mgm h ϕ j') p')) == γ bsd-mgm h (λ k' r' → γ bsd-mgm (ϕ k' r') (λ j' p' →  ψ' j' (k' , r' , p')))
          assoc' = ! (assoc bsd-mgm-laws h ϕ ψ') -- ! (assoc bsd-mgm-laws h ϕ {! (λ { j' (k' , r' , q') → transport (Op (P C)) (fst= (contr-path' (unary C (γ bsd-mgm h ϕ)) (j , hg-par) (j' , q')  )) f }) !} )
            
          ψ'' j' q' = transport (Op (P C)) (fst= (contr-path' (unary C (γ bsd-mgm h ϕ)) (j , hg-par) (j' , –> (γ-frm bsd-mgm h ϕ j') q'))) f



          foo' : γ bsd-mgm (γ bsd-mgm h ϕ) ψ
            == γ bsd-mgm h (λ k' r' → transport (Op (P C)) (fst= (contr-path' (unary C h) (k , r) (k' , r')))  (γ bsd-mgm g (λ j' q' → transport (Op (P C)) ((fst= (contr-path' (unary C g) (j , q) (j' , q')))) f )))
          foo' = ap (γ bsd-mgm (γ bsd-mgm h ϕ)) (λ= λ j' → λ= λ p' →  ap (λ x → ψ _ x) (! (<–-inv-r (γ-frm bsd-mgm h ϕ j') p')))
            ∙ (! (assoc bsd-mgm-laws h ϕ ψ'))
            ∙ ap (γ bsd-mgm h) (λ= λ k' → λ= λ r' → {!transport _  ? !})

          foo : γ bsd-mgm (γ bsd-mgm h ϕ) ψ , hgf-par
             == γ bsd-mgm h (λ k' r' → transport (Op (P C)) (fst= (contr-path' (unary C h) (k , r) (k' , r')))  (γ bsd-mgm g (λ j' q' → transport (Op (P C)) ((fst= (contr-path' (unary C g) (j , q) (j' , q')))) f ))) , hgf-par-right
          foo = pair= foo' {!!}
          
         -- ass : γ mgm hg ψ
      in foo --  pair= (! (assoc bsd-mgm-laws {!!} {!!} {!!}) ∙ ap (λ x → γ bsd-mgm h x) (λ= λ j → λ= λ z → {!!})  ) {!!}


  {-
      let mgm   = biased-mgm (ply-mgm C) (laws (M C))
          mgm-laws = biased-mgm-laws (ply-mgm C) (laws (M C))
          --ϕ j₁ l₁ = transport _ (fst= (contr-path' (unary C h) (k , r) (j₁ , l₁))) g
          --ψ j₁ l₁ j₂ l₂ = transport _ (fst= (contr-path' (unary C g) (j , q) (j₂ , l₂))) f
          ϕ : (j : I C) (p : Param (P C) h j) → Op (P C) j
          ϕ j₁ p₁ = transport _ (fst= (contr-path' (unary C h) (k , r) (j₁ , p₁))) g
          ψ : (j : I C) (p : Param (P C) h j) (k : I C) (q : Param (P C) (ϕ j p) k) → Op (P C) k
          ψ j₁ p₁ j₂ p₂ = transport _ (fst= (contr-path' (unary C g) (j , q) (j₂ , <– (par-inv (P C) _ g j₂) p₂))) f
        {-  p : μ (ply-mgm C) (nd (h , (λ j₁ l₁ → nd (transport (λ v → Op (P C) v) (fst= (contr-path' (unary C h) (k , r) (j₁ , l₁))) (μ (ply-mgm C) (nd (g , (λ j₂ l₂ → nd (transport (Op (P C)) (fst= (contr-path' (unary C g) (j , q) (j₂ , l₂))) f , (λ j₃ p₁ → lf j₃)))))) , (λ j₂ p₁ → lf j₂))))) == μ (ply-mgm C) (nd (h , (λ j₁ l₁ → nd ( (μ (ply-mgm C) (nd (transport (λ v → Op (P C) v) (fst= (contr-path' (unary C h) (k , r) (j₁ , l₁))) g , (λ j₂ l₂ → nd (transport (Op (P C)) (fst= (contr-path' (unary C g) (j , q) (j₂ , l₂))) f , (λ j₃ p₁ → lf j₃)))))) , (λ j₂ p₁ → lf j₂)))))
          p = ? 
            μ (nd (h , λ j p → corolla (μ (nd (ϕ j p , λ k q → ψ j p k q))))) -}
          lem = fst (_●_ (Nuf C) (h , r) (_●_ (Nuf C)  (g , q) (f , p))) =⟨ idp ⟩
                γ mgm h (λ j₁ p₁ → transport _ (fst= (contr-path' (unary C h) (k , r) (j₁ , p₁))) (γ mgm g (λ j₂ p₂ → transport _ (fst= (contr-path' (unary C g) (j , q) (j₂ , p₂))) f))) =⟨ idp ⟩
                γ mgm h (λ j₁ p₁ → transport _ (fst= (contr-path' (unary C h) (k , r) (j₁ , p₁))) (μ (ply-mgm C) (nd (g , (λ j₂ p₂ → corolla (P C) (transport _ (fst= (contr-path' (unary C g) (j , q) (j₂ , p₂))) f)))))) =⟨ (λ= λ j₁ → λ= λ p₁ → (! (μ-transp-commut (ply-mgm C) _ _))) |in-ctx (γ mgm h)  ⟩
                γ mgm h (λ j₁ p₁ → μ (ply-mgm C) (transport _ (fst= (contr-path' (unary C h) (k , r) (j₁ , p₁))) (nd (g , (λ j₂ p₂ → corolla (P C) (transport _ (fst= (contr-path' (unary C g) (j , q) (j₂ , p₂))) f)))))) =⟨  (λ= λ j₁ → λ= λ p₁ → nd-transp-commut (P C) _ _ _ |in-ctx (μ (ply-mgm C))) |in-ctx (γ mgm h)  ⟩
                γ mgm h (λ j₁ p₁ → μ (ply-mgm C) (nd (transport _ (fst= (contr-path' (unary C h) (k , r) (j₁ , p₁))) g , (λ j₂ p₂ → corolla (P C) (transport _ (fst= (contr-path' (unary C g) (j , q) (j₂ , <– (par-inv (P C) _ g j₂) p₂))) f))))) =⟨ idp ⟩
                γ mgm h (λ j₁ p₁ → γ mgm (ϕ j₁ p₁) (ψ _ _))  =⟨ assoc mgm-laws _ _ _ ⟩
                γ mgm  (γ mgm h ϕ) (λ j₂ p₂ → ψ _ _ j₂ (snd (snd (<– (γ-frm mgm h ϕ j₂) p₂)))) =⟨ ap (λ x → γ mgm (γ mgm h ϕ) x) (λ= λ j₂ → λ= λ p₂ → {!!}) ⟩

                fst (_●_ (Nuf C) (_●_ (Nuf C) (h , r)  (g , q)) (f , p)) ∎

      in pair= (! lem) {!!}
    let h∘g = _●_ (Nuf C) (h , r) (g , q)

          g∘f = _●_ (Nuf C) (g , q) (f , p)

          h∘⟨g∘f⟩ = _●_ (Nuf C) (h , r) (_●_ (Nuf C) (g , q) (f , p))

          ⟨h∘g⟩∘f = _●_ (Nuf C) (_●_ (Nuf C) (h , r) (g , q)) (f , p)

          tr : {i j k : I C} → hom (Nuf C) j k → hom (Nuf C) i j → W (P C) k
          tr = λ { (g , q) (f , p) → nd (g , λ _ → w-coe C q (corolla (P C) f)) }

          -- Case (h∘g)∘f

          w : W (P C // (MgmRel (ply-mgm C))) (l , fst h∘g)
          w = corolla (P C // (MgmRel (ply-mgm C))) ((tr (h , r) (g , q) , μ-frm (ply-mgm C) _) , pair= idp idp)

          κ : (ic : Ops (P C)) (n : Node (P C) (tr h∘g (f , p)) ic) → W (P C // (MgmRel (ply-mgm C))) ic 
          κ =  λ { .(l , fst h∘g) (inl idp)  → w ; (j , f) (inr (m , s , n)) → lf (j , f) }

          hgf = nd (h , λ _ → w-coe C r (nd (g , λ _ → w-coe C q (corolla (P C) f))))
          hg  = nd (h , λ _ → w-coe C r (corolla (P C) g))
          gf  = nd (g , λ _ → w-coe C q (corolla (P C) f))

          h∘g∘f = μ (ply-mgm C) hgf
  {-
          fr : Frame (P C) (tr h∘g (f , p)) h∘g∘f
          fr m = let right : {m : I C} → Leaf (P C) (tr h∘g (f , p)) m → Param (P C) h∘g∘f m
                     right {m} = λ { (_ , q' , l') →
                       let lf : Leaf (P C) hgf m
                           lf = (k , r , –> (lf-inv (P C) (indices-eq-par C r r) _ m)
                                  (j , q , –> (lf-inv (P C) (indices-eq-par C q q) _ m)
                                    (<– (lf-inv (P C) (indices-eq-par C (snd h∘g) q') _ m) l')
                                  )
                                )  
                       in –> (μ-frm (ply-mgm C) hgf m) lf    
                      }


                     lf-i : Leaf (P C) (tr h∘g (f , p)) i
                     lf-i = (j , snd h∘g , –>  (lf-inv (P C) (indices-eq-par C (snd h∘g) (snd h∘g)) (corolla (P C) f) i) (i , p , idp))

                     par-i : Param (P C) h∘g∘f i
                     par-i =
                       let lf : Leaf (P C) hgf i
                           lf = (k , r , –> (lf-inv (P C) (indices-eq-par C r r) (tr (g , q) (f , p)) i)
                                   (j , q , –> (lf-inv (P C) (indices-eq-par C q q) (corolla (P C) f) i) (i , p , idp)))
                        in –> (μ-frm (ply-mgm C) hgf i) lf

                     left : {m : I C} → Param (P C) h∘g∘f m → Leaf (P C) (tr h∘g (f , p)) m
                     left {m} par-m = transport _ (indices-eq-par C par-i par-m) lf-i

                     right-left : (par : Param (P C) h∘g∘f m) → right (transport _ (indices-eq-par C par-i par) lf-i) == par
                     right-left par = {!!}

                     left-right : (lf : Leaf (P C) (tr h∘g (f , p)) m) → left (right lf) == lf
  k                   left-right = {!!}

            in equiv right left right-left left-right
  -}
          left : W (P C // (MgmRel (ply-mgm C))) (l , fst ⟨h∘g⟩∘f)
          left = nd (((tr h∘g (f , p) , μ-frm (ply-mgm C) _) , pair= idp idp) , κ)




          -- Case h∘(g∘f)

          w' : W (P C // (MgmRel (ply-mgm C))) (k , fst g∘f)
          w' = corolla (P C // (MgmRel (ply-mgm C))) ((tr (g , q) (f , p) , μ-frm (ply-mgm C) _) , pair= idp idp)

          κ' : (ic : Ops (P C)) (n : Node (P C) (tr (h , r) g∘f) ic) → W (P C // (MgmRel (ply-mgm C))) ic 
          κ' = λ { .(l , h) (inl idp) → lf (l , h) ; ic (inr (m , s , n))  →  -- m : I  , s : Param h m , n : Node (corolla g∘f) ic
            let m' : I C
                m' = m

                s' : Param (P C) h m
                s' = s

                n' : Node (P C) (w-coe C r (corolla (P C) (fst g∘f)) s') ic
                n' = n

                tr4 : Node (P C) (corolla (P C) (fst g∘f)) ic
                tr4 = <– (nd-inv (P C) (fst= (contr-path' (unary C h) (k , r) (m , s))) (corolla (P C) (fst g∘f)) ic) n

                aux : {f g h : Ops (P C)} (n : Node (P C) (corolla (P C) (snd f)) g) (n' : Node (P C) (corolla (P C) (snd f)) h) → g == h
                aux = λ { (inl idp) (inl idp) → idp }

                pth : (k , fst g∘f) == ic
                pth = aux (inl idp) tr4
            in transport _ pth w' }

          right : W (P C // (MgmRel (ply-mgm C))) (l , fst h∘⟨g∘f⟩)
          right = nd (((tr (h , r) g∘f , μ-frm (ply-mgm C) _) , pair= idp idp) , κ')

          foo' : subst (P C) (tr h∘g (f , p)) (λ g n → flatn (MgmRel (ply-mgm C)) (κ g n) , flatn-frm (MgmRel (ply-mgm C)) (κ g n)) == flatn (MgmRel (ply-mgm C)) right
          foo' = {!idp!}

          --foo''' : 

          --w : W (P C // (MgmRel (ply-mgm C))) (l , fst h∘g)
          --w = corolla (P C // (MgmRel (ply-mgm C))) ((tr (h , r) (g , q) , μ-frm (ply-mgm C) _) , pair= idp idp)

          --κ : (ic : Ops (P C)) (n : Node (P C) (tr h∘g (f , p)) ic) → W (P C // (MgmRel (ply-mgm C))) ic 
          --κ =  λ { .(l , fst h∘g) (inl idp)  → w ; (j , f) (inr (m , s , n)) → lf (j , f) }
          -- μ w , μ-frm w = f
          -- nd (i , f) ((w , fr , α) , κ) => fr : Frame w f , α : μ w = f , μ-frm w = fr 

          bar3 : (μ (ply-mgm C) (flatn (MgmRel (ply-mgm C)) w) , μ-frm (ply-mgm C) (flatn (MgmRel (ply-mgm C)) w)) == (μ (ply-mgm C) hg , flatn-frm (MgmRel (ply-mgm C)) w)
          bar3 = laws (M C) w
          --Frame (flatn w) (μ (flatn w)) -> Frame (flatn w) (μ hg)

          flatn-w : flatn (MgmRel (ply-mgm C)) w == hg
          flatn-w = flatn-lem (MgmRel (ply-mgm C)) hg (μ-frm (ply-mgm C) hg) (pair= idp idp)

          coh : (ap (μ (ply-mgm C)) flatn-w) == (fst= bar3)
          coh = set-path (op-is-set (M C) l) _ _

          flatn-frm-w' : transport (λ x → Frame (P C) x (fst h∘g)) flatn-w (flatn-frm (MgmRel (ply-mgm C)) w) == μ-frm (ply-mgm C) hg 
          flatn-frm-w' = λ= λ j → pair= {!idp!} {!idp!} 

          -- Frame (P C) (flatn w) (μ hg) -> Frame (P C) (flatn w) (μ (flatn w))
          flatn-frm-w'' : flatn-frm (MgmRel (ply-mgm C)) w == μ-frm (ply-mgm C) (flatn (MgmRel (ply-mgm C)) w) [ (λ x → Frame (P C) (flatn (MgmRel (ply-mgm C)) w) x) ↓ ! (fst= (laws (M C) w)) ]
          flatn-frm-w'' = !ᵈ (snd= (laws (M C) w))
          -- Frame (P C) (flatn (MgmRel (ply-mgm C)) w) (μ (flatn (MgmRel (ply-mgm C)) w)) -> Frame (P C) hg (μ hg)
          flatn-frm-w3 : μ-frm (ply-mgm C) (flatn (MgmRel (ply-mgm C)) w) == μ-frm (ply-mgm C) hg [ (λ x → Frame (P C) x (μ (ply-mgm C) x)) ↓ flatn-w ]
          flatn-frm-w3 = (apd (μ-frm (ply-mgm C)) flatn-w)

          flatn-frm-w : flatn-frm (MgmRel (ply-mgm C)) w == μ-frm (ply-mgm C) hg [ (λ x → Frame (P C) x (μ (ply-mgm C) hg)) ↓ flatn-w ]
          flatn-frm-w = {!!} --flatn-frm-w'' ∙ᵈ ?

          in-fr : InFrame (P C) (l , μ (ply-mgm C) hg)
          in-fr = hg , transport (λ x → Frame (P C) x (μ (ply-mgm C) hg)) flatn-w (flatn-frm (MgmRel (ply-mgm C)) w)




          foo'' : flatn (MgmRel (ply-mgm C)) left == hgf
          foo'' = flatn (MgmRel (ply-mgm C)) left =⟨ idp ⟩

                  subst (P C) (tr h∘g (f , p)) (λ g n → flatn (MgmRel (ply-mgm C)) (κ g n) , flatn-frm (MgmRel (ply-mgm C)) (κ g n)) =⟨  idp  ⟩

                  subst (P C)
                    (tr h∘g (f , p))
                    (λ { .(l , fst h∘g) (inl idp) → flatn (MgmRel (ply-mgm C)) w , flatn-frm (MgmRel (ply-mgm C)) w ;
                          (j , f) (inr (m , s , n)) → flatn (MgmRel (ply-mgm C)) (lf (j , f)) , flatn-frm (MgmRel (ply-mgm C)) (lf (j , f)) })

                    =⟨ ap {A = (g : Ops (P C)) → Node (P C) (tr h∘g (f , p)) g → InFrame (P C) g} {B = W (P C) l} (subst (P C) (tr h∘g (f , p))) {x = (λ { .(l , fst h∘g) (inl idp) → flatn (MgmRel (ply-mgm C)) w , flatn-frm (MgmRel (ply-mgm C)) w ;
                          (j , f) (inr (m , s , n)) → flatn (MgmRel (ply-mgm C)) (lf (j , f)) , flatn-frm (MgmRel (ply-mgm C)) (lf (j , f)) })} {y = (λ { .(l , fst h∘g) (inl idp) → hg , μ-frm (ply-mgm C) _ ;
                           (j , f) (inr (m , s , n)) → flatn (MgmRel (ply-mgm C)) (lf (j , f)) , flatn-frm (MgmRel (ply-mgm C)) (lf (j , f)) })}  (λ= (λ _ → λ= λ { (inl idp) → pair= flatn-w flatn-frm-w ; (inr (m , s , n)) → idp  }))  ⟩

                  subst (P C)
                    (tr h∘g (f , p))
                    (λ { .(l , fst h∘g) (inl idp) → hg , μ-frm (ply-mgm C) _ ;
                           (j , f) (inr (m , s , n)) → flatn (MgmRel (ply-mgm C)) (lf (j , f)) , flatn-frm (MgmRel (ply-mgm C)) (lf (j , f)) })

                  =⟨ idp  ⟩

                  subst (P C)
                    (tr h∘g (f , p))
                    (λ { .(l , fst h∘g) (inl idp) → hg , μ-frm (ply-mgm C) _ ;
                           (j , f) (inr (m , s , n)) → corolla (P C) f ,  corolla-frm (P C) f })

                  =⟨ idp ⟩


                  graft (P C)
                    hg
                    (λ j l → subst (P C) (w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ j) l)) (λ jf _ →  (flatn (MgmRel (ply-mgm C)) (lf jf) , flatn-frm (MgmRel (ply-mgm C)) (lf jf)) )  )

                  =⟨ idp ⟩

                  nd (h , λ j p →
                    graft (P C)
                      (w-coe C r (corolla (P C) g) p)
                      (λ k l →
                        subst (P C)
                          (w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ k) (j , p , l)))
                          (λ jf _ →  (flatn (MgmRel (ply-mgm C)) (lf jf) , flatn-frm (MgmRel (ply-mgm C)) (lf jf)))))

                  =⟨ idp ⟩

                  nd (h , λ j p →
                    graft (P C)
                      (w-coe C r (corolla (P C) g) p)
                      (λ k l →
                        subst (P C)
                          (w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ k) (j , p , l)))
                            (λ jf _ →  (corolla (P C) (snd jf)) , corolla-frm (P C) (snd jf))))

                  =⟨ ap (λ δ → nd (h , δ)) (λ= λ j → λ= λ p → ap (graft (P C) (w-coe C r (corolla (P C) g) p)) (λ= λ k → λ= λ l → subst-lemma' (MgmRel (ply-mgm C)) _)) ⟩

                  nd (h , λ j p →
                    graft (P C)
                      (w-coe C r (corolla (P C) g) p)
                      (λ k l →
                        w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ k) (j , p , l))))

                  =⟨ ap (λ δ → nd (h , δ)) (λ= λ j → λ= λ p → graft-lemma (P C) (corolla (P C) g) _ _ _ ) ⟩

                  nd (h , λ j p →
                    w-coe C r
                      (graft (P C)
                        (corolla (P C) g)
                        (λ k l → w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ k) (j , p , (–> (lf-inv (P C) (fst= (contr-path' (unary C h) (_ , r) (_ , p))) (corolla (P C) g) k) l))))) p)

                   =⟨ idp ⟩

                   nd (h , λ j p →
                    w-coe C r
                      (nd (g , λ j' p' →
                        graft (P C)
                          (lf j')
                          (λ k l → w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ k) (j , p , (–> (lf-inv (P C) (fst= (contr-path' (unary C h) (_ , r) (_ , p))) (corolla (P C) g) k) (j' , p' , l)))) ))) p)

                   =⟨ idp ⟩

                   nd (h , λ j p →
                    w-coe C r
                      (nd (g , λ j' p' →
                        graft (P C)
                          (lf j')
                          (λ k l → w-coe C (snd h∘g) (corolla (P C) f) (–> (μ-frm (ply-mgm C) _ k) (j , p , (–> (lf-inv (P C) (fst= (contr-path' (unary C h) (_ , r) (_ , p))) (corolla (P C) g) k) (j' , p' , l)))) ))) p)

                   =⟨ idp ⟩

                   nd (h , λ j p →
                    w-coe C r
                      (nd (g , λ j' p' →
                        w-coe C (snd h∘g)
                          (corolla (P C) f)
                          (–> (μ-frm (ply-mgm C) _ j') (j , p , (–> (lf-inv (P C) (fst= (contr-path' (unary C h) (_ , r) (_ , p))) (corolla (P C) g) j') (j' , p' , idp))))))
                       p)

                   =⟨ ap (λ δ → nd (h , δ)) (λ= λ j → λ= λ p → ap (λ δ' → w-coe C r (nd (g , δ')) p) (λ= λ j' → λ= λ p' → {!snd h∘g!})) ⟩

                   nd (h , λ j p → w-coe C r (nd (g , λ j' p' → w-coe C q (corolla (P C) f) p')) p)

                   =⟨ idp ⟩

                   hgf  ∎





          --foo'' : (p : Param (P C) )  = snd h∘g

          --foo'' : fst= (contr-path' (unary C g) (snd h∘g) (–> (μ-frm (ply-mgm C) _ j') (j , p , (–> (lf-inv (P C) (fst= (contr-path' (unary C h) (_ , r) (_ , p))) (corolla (P C) g) j') (j' , p' , idp))))) 

          foo : flatn (MgmRel (ply-mgm C)) left == flatn (MgmRel (ply-mgm C)) right
          foo = {!idp!}

          μ-assoc : fst ⟨h∘g⟩∘f == fst h∘⟨g∘f⟩ 
          μ-assoc = fst ⟨h∘g⟩∘f                                =⟨ ! (fst= (laws (M C) left)) ⟩   
                    μ (ply-mgm C) (flatn (MgmRel (ply-mgm C)) left)  =⟨ ap (μ (ply-mgm C)) foo ⟩
                    μ (ply-mgm C) (flatn (MgmRel (ply-mgm C)) right) =⟨ fst= (laws (M C) right) ⟩
                    fst h∘⟨g∘f⟩  ∎



      in pair= μ-assoc {!!} -}
    id        Nuf {i} = {!!}
    unit-l     Nuf (f , p) = pair= {!apd _ (op-id-unit-l C (corolla (P C) f))!} {!!}
    unit-r     Nuf f = {!idp!}
    homs-sets Nuf i j = Σ-level (op-is-set (M C) j) {!λ f → arity-is-set (M C) f!}




    aux : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} (p : is-contr A) → Σ A B ≃ B (contr-center p)
    aux {A = A} {B = B} p =
      equiv
      (λ { (a , b) → transport B (! (contr-path p a)) b })
      (λ b → (contr-center p , b))
      (λ b → {!!})
      λ { (a , b) → pair= (contr-path p a) {!!} }


    -- Construire exemples
    -- U
    -- Fr P
    -- Subst P
    -- I → ∞-groupoid
    -- 

-}
-}
