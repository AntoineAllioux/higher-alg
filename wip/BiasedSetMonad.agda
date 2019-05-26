{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Polynomial
open import PolyMagma
open import PolyMonad
open import Slice
open import Substitution
open import wip.BiasedRel
--open import Biased

module wip.BiasedSetMonad where 

  record BsdSetMonad {ℓ} {I : Type ℓ} {P : Poly I} (Mgm : BiasedMgm P) : Type ℓ where
    field
      sort-is-gpd : is-gpd I
      opfr-is-set : {i : I} (w : W P i) → is-set (OutFrame P w)
      assoc      : BiasedLaws Mgm

  open BsdSetMonad

  λ=↓ : ∀ {ℓ} {A B : Type ℓ} {C : A → B → Type ℓ} {x y : A} (p : x == y) {f : Π B (C x)} {g : Π B (C y)} (pth : (x : B) → f x == g x [ (λ y → C y x) ↓ p ]) → f == g [ (λ x → Π B (C x)) ↓ p ]
  λ=↓ idp {f} {g} pth = λ= pth

   

    
  module _ {ℓ} {I : Type ℓ} {P : Poly I} {B : BiasedMgm P} (M : BsdSetMonad B) where
    private R = ⟪ BsdMgm B  ⟫

    --open (BiasedRel P ⟪ Bsd  ⟫)

    open BiasedLaws -- P 

    η-rel-set : (f : Ops P) → R f (subst-η P f)
    η-rel-set (i , f) = pair= (unit-l (assoc M) f) (λ=↓ (unit-l (assoc M) f) (λ j → ↓-Subtype-in (λ f → is-equiv-prop) (λ=↓ (unit-l (assoc M) f) λ { (.j , p , idp) → unit-l-frm (assoc M) f j p  })))

    γ-rel-set : (f : Ops P) (wα : InFrame P f) (r : R f wα) (κ : Decor (P PolyMonad.// R) (wα , r) (Op (P PolyMonad.// R))) → R f (subst-γ P f wα (λ g n → fst (κ g n)))
    γ-rel-set (i , f) wα r κ = pair= {!μ-bsd-flatn-invar ?!} {!!}

    set-monad-biased-rel : BiasedRel P ⟪ BsdMgm B  ⟫
    set-monad-biased-rel = LawsRel B (assoc M) -- record { η-rel = η-rel-set ; γ-rel = γ-rel-set }

    open BiasedRelLaws

    rel-is-prop : (f : Ops P) (wα : InFrame P f) → is-prop (⟪ BsdMgm B ⟫ f wα)
    rel-is-prop f wα = has-level-apply (opfr-is-set M _) _ _

    set-monad-biased-rel-laws : BiasedRelLaws _ _ set-monad-biased-rel
    subst-unit-l-rel set-monad-biased-rel-laws w α r = prop-has-all-paths-↓ ⦃ rel-is-prop _ _ ⦄
    subst-unit-r-rel set-monad-biased-rel-laws {f = f} κ = prop-has-all-paths-↓ ⦃ rel-is-prop _ _ ⦄
    subst-assoc-rel set-monad-biased-rel-laws w α r κ ν = prop-has-all-paths-↓ ⦃ rel-is-prop _ _ ⦄

    
    BsdSetMonad-is-polymonad : PolyMonad P
    Mgm BsdSetMonad-is-polymonad = BsdMgm B
    Coh BsdSetMonad-is-polymonad = foo
      where foo : CohStruct (BsdMgm B)μ 
            Ψ foo = {!LawsInvar ? ?!}
            H foo = {!!}
    

    --BiasedRel → BiasedLasws ()
    
