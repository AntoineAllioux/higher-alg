{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Util
open import Polynomial
open import WPaths
open import Substitution
open import PolyMonad

module wip.Biased where

  record BiasedMgm {ℓ} {I : Type ℓ} (P : Poly I) : Type ℓ where
    field

      η : (i : I) → Op P i
      η-frm : (i : I) (j : I) → (i == j) ≃ Param P (η i) j 

      γ : {i : I} (f : Op P i) (ϕ : (j : I) → Param P f j → Op P j) → Op P i
      γ-frm : {i : I} (f : Op P i) (ϕ : (j : I) → Param P f j → Op P j)
        → (j : I) → Σ I (λ k → Σ (Param P f k) (λ p → Param P (ϕ k p) j)) ≃ Param P (γ f ϕ) j 

  module _ {ℓ} {I : Type ℓ} {P : Poly I} (B : BiasedMgm P) where

    open BiasedMgm B
    
    -- Here are some path over principles
    ↓-γ-param : {i j : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (Op P)}
      → (r : ϕ₀ == ϕ₁)
      → {k : I} {p : Param P f k}
      → {q₀ : Param P (ϕ₀ k p) j} {q₁ : Param P (ϕ₁ k p) j}
      → (c : q₀ == q₁ [ (λ x → Param P x j) ↓ app= (app= r k) p ])
      → –> (γ-frm f ϕ₀ j) (k , p , q₀) ==
        –> (γ-frm f ϕ₁ j) (k , p , q₁)
          [ (λ x → Param P x j) ↓ ap (γ f) r ]
    ↓-γ-param idp idp = idp

    -- This is now a simple consequence of the previous...
    ↓-γ-param' : {i j : I} {f : Op P i}
      → {ϕ₀ ϕ₁ : Decor P f (Op P)}
      → {ψ : (j : I) (p : Param P f j) → ϕ₀ j p == ϕ₁ j p}
      → {k : I} {p : Param P f k}
      → {q₀ : Param P (ϕ₀ k p) j} {q₁ : Param P (ϕ₁ k p) j}
      → (c : q₀ == q₁ [ (λ x → Param P x j) ↓ ψ k p ])
      → –> (γ-frm f ϕ₀ j) (k , p , q₀) ==
        –> (γ-frm f ϕ₁ j) (k , p , q₁)
          [ (λ x → Param P x j) ↓ ap (γ f) (Decor-== P ψ) ]
    ↓-γ-param' {ψ = ψ} {k} {p} {q₀} {q₁} c =
      ↓-γ-param (Decor-== P ψ) (transport (λ y → q₀ == q₁ [ (λ x → Param P x _) ↓ y ]) lem c)

      where lem : ψ k p == app= (app= (λ= (λ j → λ= (ψ j))) k) p
            lem = ψ k p =⟨ ! (app=-β (ψ k) p) ⟩
                  app= (λ= (ψ k)) p =⟨ ap (λ g → app= g p) (! (app=-β (λ j → λ= (ψ j)) k)) ⟩ 
                  app= (app= (λ= (λ j → λ= (ψ j))) k) p ∎


  record BiasedLaws {ℓ} {I : Type ℓ} (P : Poly I) (B : BiasedMgm P) : Type ℓ where

    open BiasedMgm B

    field

      unit-l : {i : I} (f : Op P i) → γ f (λ j _ → η j) == f
      unit-r : {i : I} (f : Op P i) → f == γ (η i) (λ j p → transport (Op P) (<– (η-frm i j) p) f)
      assoc : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
        → γ f (λ j p → γ (ϕ j p) (λ k q → ψ j p k q)) == 
          γ (γ f ϕ) (λ j p → let (k , p₀ , p₁) = <– (γ-frm f ϕ j) p in ψ k p₀ j p₁ ) 

    unit-l-param : {i : I} (f : Op P i) (j : I) (p : Param P f j)
      → Param P (γ f (λ j _ → η j)) j
    unit-l-param f j p = –> (γ-frm f (λ j _ → η j) j) (j , p , –> (η-frm j j) idp)

    unit-r-param : {i : I} (f : Op P i) (j : I) (p : Param P f j)
      → Param P (γ (η i) (λ j p → transport (Op P) (<– (η-frm i j) p) f)) j
    unit-r-param {i} f j p = –> (γ-frm (η i) (λ j p → transport (Op P) (<– (η-frm i j) p) f) j)
      (i , –> (η-frm i i) idp , transport! (λ x → Param P (transport (Op P) x f) j) (<–-inv-l (η-frm i i) idp) p )

    assoc-l-param : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
        → (j : I) (p : Param P f j) (k : I) (q : Param P (ϕ j p) k) (l : I) (r : Param P (ψ j p k q) l)
        → Param P (γ f (λ j p → γ (ϕ j p) (λ k q → ψ j p k q))) l
    assoc-l-param f ϕ ψ j p k q l r = –> (γ-frm f (λ j p → γ (ϕ j p) (λ k q → ψ j p k q)) l)
      (j , p , –> (γ-frm (ϕ j p) (λ k q → ψ j p k q) l) (k , q , r))

    assoc-r-param : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
        → (j : I) (p : Param P f j) (k : I) (q : Param P (ϕ j p) k) (l : I) (r : Param P (ψ j p k q) l)
        → Param P (γ (γ f ϕ) (λ j p → let (k , p₀ , p₁) = <– (γ-frm f ϕ j) p in ψ k p₀ j p₁ ) ) l
    assoc-r-param f ϕ ψ j p k q l r = –> (γ-frm (γ f ϕ) (λ j p → let (k , p₀ , p₁) = <– (γ-frm f ϕ j) p in ψ k p₀ j p₁) l)
      (k , –> (γ-frm f ϕ k) (j , p , q)  , transport! (λ x → Param P x l)
        (ap (λ x → ψ (fst x) (fst (snd x)) k (snd (snd x))) (<–-inv-l (γ-frm f ϕ k) (j , p , q))) r)

    field
    
      unit-l-frm : {i : I} (f : Op P i) (j : I) (p : Param P f j)
        → unit-l-param f j p == p [ (λ x → Param P x j) ↓ unit-l f ]

      unit-r-frm : (i : I) (f : Op P i) (j : I) (p : Param P f j)
        → p == unit-r-param f j p [ (λ x → Param P x j) ↓ unit-r f ]
             
      assoc-frm : {i : I} (f : Op P i)
        → (ϕ : (j : I) → Param P f j → Op P j)
        → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
        → (j : I) (p : Param P f j) (k : I) (q : Param P (ϕ j p) k) (l : I) (r : Param P (ψ j p k q) l)
        → assoc-l-param f ϕ ψ j p k q l r == assoc-r-param f ϕ ψ j p k q l r [ (λ x → Param P x l) ↓ assoc f ϕ ψ ]

  module _ {ℓ} {I : Type ℓ} (P : Poly I) (B : BiasedMgm P) where

    open BiasedMgm B

    μ-bsd : {i : I} → W P i → Op P i
    μ-bsd (lf i) = η i
    μ-bsd (nd (f , ϕ)) = γ f (λ j p → μ-bsd (ϕ j p))

    μ-bsd-frm-to : {i : I} (w : W P i) (j : I)
      → Leaf P w j
      → Param P (μ-bsd w) j
    μ-bsd-frm-to (lf i) j l = –> (η-frm i j) l
    μ-bsd-frm-to (nd (f , ϕ)) j (k , p , l) =
      let ψ' j p = μ-bsd (ϕ j p)
      in –> (γ-frm f ψ' j) (k , p , μ-bsd-frm-to (ϕ k p) j l)

    μ-bsd-frm-from : {i : I} (w : W P i) (j : I)
      → Param P (μ-bsd w) j
      → Leaf P w j
    μ-bsd-frm-from (lf i) j p = <– (η-frm i j) p
    μ-bsd-frm-from (nd (f , ϕ)) j p = 
      let ψ' j p = μ-bsd (ϕ j p)
          (k , p , q) = <– (γ-frm f ψ' j) p
      in k , p , μ-bsd-frm-from (ϕ k p) j q
      
    postulate

      μ-bsd-frm-to-from : {i : I} (w : W P i) (j : I)
        → (p : Param P (μ-bsd w) j)
        → μ-bsd-frm-to w j (μ-bsd-frm-from w j p) == p

      μ-bsd-frm-from-to : {i : I} (w : W P i) (j : I)
        → (l : Leaf P w j)
        → μ-bsd-frm-from w j (μ-bsd-frm-to w j l) == l

    -- Shows the above can be written as a composition ...
    -- μ-bsd-frm : {i : I} (w : W P i) → Frame P w (μ-bsd w)
    -- μ-bsd-frm (lf i) = η-frm i
    -- μ-bsd-frm (nd (f , ϕ)) j = (γ-frm f (λ j p → μ-bsd (ϕ j p)) j) ∘e
    --   Σ-emap-r (λ k → Σ-emap-r (λ p → μ-bsd-frm (ϕ k p) j))

    μ-bsd-frm : {i : I} (w : W P i) → Frame P w (μ-bsd w)
    μ-bsd-frm w j = equiv (μ-bsd-frm-to w j) (μ-bsd-frm-from w j)
      (μ-bsd-frm-to-from w j) (μ-bsd-frm-from-to w j)

    BsdMgm : PolyMagma P
    μ BsdMgm = μ-bsd
    μ-frm BsdMgm = μ-bsd-frm

    module _ (L : BiasedLaws P B) where

      private
        R = ⟪ BsdMgm ⟫ 

      open BiasedLaws L

      μ-graft-inv-lem₀ : {i : I} 
        → (ψ : ∀ j → Leaf P (lf i) j → W P j)
        → {j : I} (q : i == j)
        → transport (Op P) q (μ-bsd (ψ i idp)) == μ-bsd (ψ j q)
      μ-graft-inv-lem₀ ψ idp = idp

        -- ap (γ (η i)) (Decor-== P (λ j p → μ-graft-inv-lem₀ ψ (<– (η-frm i j) p)))


      μ-graft-inv-lem₁ : {i : I} 
        → (ψ : ∀ j → Leaf P (lf i) j → W P j)
        → {j : I} (q : i == j)
        → (l : Leaf P (ψ i idp) j)
        → {!(<–-inv-l (η-frm i i) idp)!} == {!!} [ (λ x → Param P x j) ↓ μ-graft-inv-lem₀ ψ q ]
      μ-graft-inv-lem₁ = {!!}


            -- a = transport! (λ x → Param P (transport (Op P) x (μ-bsd (ψ i idp))) j) (<–-inv-l (η-frm i i) idp) (–> (μ-bsd-frm (ψ i idp) j) l)
            -- b = transport! (λ x → Param P (μ-bsd (ψ k x)) j) (<–-inv-l (μ-bsd-frm (lf i) k) p) (–> (μ-bsd-frm (ψ k p) j) l₀)


-- Goal: PathOver (λ x → Param P x j)
--       (μ-graft-inv-lem₀ ψ
--        (is-equiv.g (snd (η-frm i i)) (–> (η-frm i i) idp)))
--       (transport!
--        (λ x → Param P (transport (Op P) x (μ-bsd (ψ i idp))) j)
--        (<–-inv-l (η-frm i i) idp) (fst (μ-bsd-frm (ψ i idp) j) l))
--       (transport!
--        (λ x →
--           Param P
--           (μ-bsd
--            (ψ (fst (is-equiv.g (snd (graft-leaf-eqv P (lf i) ψ j)) l)) x))
--           j)
--        (is-equiv.g-f
--         (snd
--          (μ-bsd-frm (lf i)
--           (fst (is-equiv.g (snd (graft-leaf-eqv P (lf i) ψ j)) l))))
--         (fst (snd (is-equiv.g (snd (graft-leaf-eqv P (lf i) ψ j)) l))))
--        (fst
--         (μ-bsd-frm
--          (ψ (fst (is-equiv.g (snd (graft-leaf-eqv P (lf i) ψ j)) l))
--           (fst (snd (is-equiv.g (snd (graft-leaf-eqv P (lf i) ψ j)) l))))
--          j)
--         (snd (snd (is-equiv.g (snd (graft-leaf-eqv P (lf i) ψ j)) l)))))



      μ-graft-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → μ-bsd (graft P w ψ) ==
          γ (μ-bsd w) (λ j p → μ-bsd (ψ j (<– (μ-bsd-frm w j) p)))
      μ-graft-inv (lf i) ψ = unit-r (μ-bsd (ψ i idp)) ∙
        ap (γ (η i)) (Decor-== P (λ j p → μ-graft-inv-lem₀ ψ (<– (η-frm i j) p)))
      μ-graft-inv (nd (f , ϕ)) ψ = 
        let ih j p = μ-graft-inv (ϕ j p) (λ k l → ψ k (j , p , l))
            ϕ' j p = μ-bsd (ϕ j p)
            ψ' j p k q = μ-bsd (ψ k (j , p , <– (μ-bsd-frm (ϕ j p) k) q))
        in ap (γ f) (Decor-== P ih) ∙ (assoc f ϕ' ψ') 
        -- in γ f (λ j p → μ-bsd (graft P (ϕ j p) (λ k l → ψ k (j , p , l))))
        --      =⟨ ap (γ f) (Decor-== P ih) ⟩
        --    γ f (λ j p → γ (μ-bsd (ϕ j p)) (λ k q → μ-bsd (ψ k (j , p , <– (μ-bsd-frm (ϕ j p) k) q))))
        --      =⟨ assoc f ϕ' ψ' ⟩
        --    γ (γ f (λ j p → μ-bsd (ϕ j p))) (λ j p → μ-bsd (ψ j (<– (μ-bsd-frm (nd (f , ϕ)) j) p))) ∎

      μ-graft-lf-param : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → (j : I) (l : Leaf P (graft P w ψ) j)
        → Param P (γ (μ-bsd w) (λ j p → μ-bsd (ψ j (<– (μ-bsd-frm w j) p)))) j
      μ-graft-lf-param w ψ j l = 
        let (k , l₀ , l₁) = <– (graft-leaf-eqv P w ψ j) l
        in (–> (γ-frm (μ-bsd w) (λ k p → μ-bsd (ψ k (<– (μ-bsd-frm w k) p))) j))
             (k , –> (μ-bsd-frm w k) l₀ , transport! (λ x → Param P (μ-bsd (ψ k x)) j)
               (<–-inv-l (μ-bsd-frm w k) l₀) (–> (μ-bsd-frm (ψ k l₀) j) l₁))

      μ-graft-lf-inv : {i : I} (w : W P i)
        → (ψ : ∀ j → Leaf P w j → W P j)
        → (j : I) (l : Leaf P (graft P w ψ) j)
        → –> (μ-bsd-frm (graft P w ψ) j) l == μ-graft-lf-param w ψ j l
            [ (λ x → Param P x j) ↓ μ-graft-inv w ψ ]
      μ-graft-lf-inv (lf i) ψ j l =
        let (k , p , l₀) = <– (graft-leaf-eqv P (lf i) ψ j) l
            a = transport! (λ x → Param P (transport (Op P) x (μ-bsd (ψ i idp))) j) (<–-inv-l (η-frm i i) idp) (–> (μ-bsd-frm (ψ i idp) j) l)
            b = transport! (λ x → Param P (μ-bsd (ψ k x)) j)                        (<–-inv-l (η-frm i k) p)   (–> (μ-bsd-frm (ψ k p) j) l₀)
        in unit-r-frm i (μ-bsd (ψ i idp)) j (–> (μ-bsd-frm (ψ i idp) j) l) ∙ᵈ
           ↓-γ-param' B {!!}

      μ-graft-lf-inv (nd (f , ϕ)) ψ j (k , p , l) =
        let ih-inv j p = μ-graft-inv (ϕ j p) (λ k l → ψ k (j , p , l))
            ih = μ-graft-lf-inv (ϕ k p) (λ k' l → ψ k' (k , p , l)) j l
            ϕ' j p = μ-bsd (ϕ j p)
            ψ' j p k q = μ-bsd (ψ k (j , p , <– (μ-bsd-frm (ϕ j p) k) q))
            (k₀ , l₀ , l₁) = <– (graft-leaf-eqv P (ϕ k p) (λ k' l' → ψ k' (k , p , l')) j) l
            p₀ = μ-bsd-frm-to (ϕ k p) k₀ l₀
            p₁ = μ-bsd-frm-to (ψ k₀ (k , p , l₀)) j l₁
            p₁' = transport! (λ x → Param P (μ-bsd (ψ k₀ (k , p , x))) j) (<–-inv-l (μ-bsd-frm (ϕ k p) k₀) l₀) p₁

            right-fix : assoc-r-param f ϕ' ψ' k p k₀ p₀ j p₁' == μ-graft-lf-param (nd (f , ϕ)) ψ j (k , p , l)
            right-fix = {!!}
            
        in ↓-γ-param' B ih ∙ᵈ assoc-frm f ϕ' ψ' k p k₀ p₀ j p₁' ∙'ᵈ right-fix  

      -- assoc-r-param : {i : I} (f : Op P i)
      --     → (ϕ : (j : I) → Param P f j → Op P j)
      --     → (ψ : (j : I) (p : Param P f j) (k : I) → Param P (ϕ j p) k → Op P k)
      --     → (j : I) (p : Param P f j) (k : I) (q : Param P (ϕ j p) k) (l : I) (r : Param P (ψ j p k q) l)
      --     → Param P (γ (γ f ϕ) (λ j p → let (k , p₀ , p₁) = <– (γ-frm f ϕ j) p in ψ k p₀ j p₁ ) ) l
      -- assoc-r-param f ϕ ψ j p k q l r = –> (γ-frm (γ f ϕ) (λ j p → let (k , p₀ , p₁) = <– (γ-frm f ϕ j) p in ψ k p₀ j p₁) l)
      --   (k , –> (γ-frm f ϕ k) (j , p , q)  , transport! (λ x → Param P x l)
      --     (ap (λ x → ψ (fst x) (fst (snd x)) k (snd (snd x))) (<–-inv-l (γ-frm f ϕ k) (j , p , q))) r)
      
      --
      --  2-level substitution invariance
      --

      μ-subst-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → μ-bsd (subst P w (λ g n → fst (κ g n))) == μ-bsd w

      μ-subst-inv-lem : {i : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : Op (P // R) (i , f))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → μ-bsd (graft P (fst (fst w))
                  (λ j l → subst P (ϕ j (–> (snd (fst w) j) l))
                  (λ g n → fst (κ g (inr (j , –> (snd (fst w) j) l , n)))))) ==
          γ f (λ j p → μ-bsd (ϕ j p))

      μ-subst-invar (lf i) κ = idp
      μ-subst-invar (nd (f , ϕ)) κ =
        μ-subst-inv-lem f ϕ (κ (_ , f) (inl idp)) κ

      μ-subst-inv-lem ._ ϕ ((w , ._) , idp) κ = 
        let κp j p g n = κ g (inr (j , p , n))
            ψp j p = subst P (ϕ j p) (λ g n → fst (κp j p g n))
            ψ j l = ψp j (–> (μ-bsd-frm w j) l)
            ih j p = ap (λ x → μ-bsd (ψp j x)) (<–-inv-r (μ-bsd-frm w j) p) ∙ μ-subst-invar (ϕ j p) (κp j p)
         in μ-graft-inv w ψ ∙ ap (γ (μ-bsd w)) (Decor-== P ih)
        -- in μ-bsd (graft P w ψ) 
        --      =⟨ μ-graft-inv w ψ ⟩
        --    γ (μ-bsd w) (λ j p → μ-bsd (ψp j (–> (μ-bsd-frm w j) (<– (μ-bsd-frm w j) p))))
        --      =⟨ λ= (λ j → λ= (λ p → ih j p)) |in-ctx (λ x → γ (μ-bsd w) x) ⟩ 
        --    γ (μ-bsd w) (λ j p → μ-bsd (ϕ j p)) ∎


      μ-lf-invar : {i : I} (w : W P i)
        → (κ : (g : Ops P) → Node P w g → Op (P // R) g)
        → (j : I) (l : Leaf P (subst P w (λ g n → fst (κ g n))) j)
        → –> (μ-bsd-frm (subst P w (λ g n → fst (κ g n))) j) l  == 
          –> (μ-bsd-frm w j ∘e subst-lf-eqv P w (λ g n → fst (κ g n)) j) l
            [ (λ x → Param P x j) ↓ μ-subst-invar w κ ]

      μ-subst-lf-inv-lem : {i j : I} (f : Op P i) (ϕ : Decor P f (W P))
        → (w : W P i) (α : Frame P w f) (r : R (i , f) (w , α))
        → (κ : (g : Ops P) → Node P (nd (f , ϕ)) g → Op (P // R) g)
        → (l : Leaf P (graft P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , (–> (α j') l') , n))) ))) j)
        → –> (μ-bsd-frm (graft P w (λ j' l' → subst P (ϕ j' (–> (α j') l')) (λ g n → fst (κ g (inr (j' , (–> (α j') l') , n))) ))) j) l ==
          –> (γ-frm f (λ k p → μ-bsd (ϕ k p)) j) (graft-leaf-rec P w (λ j l → subst P (ϕ j (–> (α j) l))
                  (λ g n → fst (κ g (inr (j , –> (α j) l , n))))) j
                  (λ k l₀ l₁ → k , (–> (α k) l₀) ,
                  (–> (μ-bsd-frm (ϕ k (–> (α k) l₀)) j)
                  (subst-lf-to P (ϕ k (–> (α k) l₀)) (λ g n → fst (κ g (inr (k , (–> (α k) l₀) , n)))) j l₁))) l) 
            [ (λ x → Param P x j) ↓ μ-subst-inv-lem f ϕ ((w , α) , r) κ ]

      μ-lf-invar (lf i) κ j l = idp
      μ-lf-invar (nd (f , ϕ)) κ j l =
        let ((w , α) , r) = κ (_ , f) (inl idp)
        in μ-subst-lf-inv-lem f ϕ w α r κ l ∙'ᵈ {!!}

      μ-subst-lf-inv-lem ._ ϕ w ._ idp κ l = {!!}

      --
      --  Full substitution invariance
      --

      μ-bsd-invar : {i : I} {f : Op P i} (pd : W (P // R) (i , f))
        → μ-bsd (flatn R pd) == f
        
      μ-bsd-invar-frm : {f : Ops P} (pd : W (P // R) f)
        → μ-bsd-frm (flatn R pd) == flatn-frm R pd [ Frame P (flatn R pd) ↓ μ-bsd-invar pd ]

      μ-invar : SubInvar R
      μ-invar pd = pair= (μ-bsd-invar pd) (μ-bsd-invar-frm pd)

      μ-bsd-invar (lf (i , f)) = unit-l f
      μ-bsd-invar (nd (((w , ._) , idp) , κ)) =
        let κ' g n = (flatn R (κ g n) , flatn-frm R (κ g n)) , μ-invar (κ g n)
        in μ-subst-invar w κ'

      μ-bsd-invar-frm (lf (i , f)) = ↓-Op-Frame-in P (unit-l f) lem
      
        where lem : (j : I) (l : Leaf P (corolla P f) j)
                → –> (μ-bsd-frm (corolla P f) j) l ==
                  –> (corolla-frm P f j) l [ (λ x → Param P x j) ↓ unit-l f ]
              lem j (j , p , idp) = unit-l-frm f j p

      μ-bsd-invar-frm (nd (((w , ._) , idp) , κ)) =
        ↓-Op-Frame-in P (μ-subst-invar w κ')
                        (μ-lf-invar w κ')

        where κ' : (g : Ops P) (n : Node P w g) → Σ (InFrame P g) (R g)
              κ' g n = (flatn R (κ g n) , flatn-frm R (κ g n)) , μ-invar (κ g n)
