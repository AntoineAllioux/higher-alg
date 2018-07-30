{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Util
open import Polynomial
open import Substitution
open import SubstCoh
open import PolyMonad

module Examples where

  𝕌 : Poly ⊤
  γ 𝕌 unit = Type₀
  ρ 𝕌 X unit = X

  -- BDDomain : {I : Type₀} (P : Poly I)
  --   → (μ : {i : I} (w : W P i) → γ P i)
  --   → (ϕ : {i : I} (w : W P i) → Frame P w (μ w))
  --   → (α : (F : FillingFamily P) {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  --     → Path {A = Σ (γ P i) (λ c₀ → Frame P (flatten F pd) c₀)}
  --       (c , flatten-frm F pd) (μ (flatten F pd) , ϕ (flatten F pd)))
  --   → PolyDomain P
  -- F (BDDomain P μ ϕ α) w c f = (c , f) == (μ w , ϕ w)
  -- H (BDDomain P μ ϕ α) = BDDomain (P // (λ w c f → (c , f) == (μ w , ϕ w)))
  --   (λ { {i , c} pd → flatten (λ w c f → (c , f) == (μ w , ϕ w)) pd ,
  --                     flatten-frm (λ w c f → (c , f) == (μ w , ϕ w)) pd ,
  --                     α (λ w c f → (c , f) == (μ w , ϕ w)) pd })
  --   (λ pd → bd-frame (λ w c f → (c , f) == (μ w , ϕ w)) pd)
  --   λ { F {i , .(μ w)} {w , .(ϕ w) , idp} pd → {!!} }

  module _ {I : Type₀} (P : Poly I)
    (is-f : {i : I} (w : W P i) → is-contr (Σ (γ P i) (Frame P w))) where

    CF : FillingFamily P
    CF w c f = contr-center (is-f w) == (c , f) 

    claim₀ : {ic : Σ I (γ P)} (pd : W (P // CF) ic) → Σ (γ (P // CF) ic) (Frame (P // CF) pd)
    claim₀ {i , c} pd = (flatten CF pd , flatten-frm CF pd , contr-path (is-f (flatten CF pd)) (c , flatten-frm CF pd)) , bd-frame CF pd

    claim₁ : {ic : Σ I (γ P)} (pd : W (P // CF) ic)
      → (α : Σ (γ (P // CF) ic) (Frame (P // CF) pd))
      → claim₀ pd == α
    claim₁ (lf (i , ._)) ((w , ._ , idp) , s) = pair= {!!} {!!}
    claim₁ (nd {i , c} ((w , f , x) , κ)) α = {!!}

  --   claim : {ic : Σ I (γ P)} (pd : W (P // CF) ic) → is-contr (Σ (γ (P // CF) ic) (Frame (P // CF) pd))
  --   claim {i , c} pd = has-level-in (ctr , pth)

  --     where ctr : Σ (Σ (W P i) (λ w → Σ (Frame P w c) (CF w c))) (Frame (P // CF) pd)
  --           ctr = (flatten CF pd , flatten-frm CF pd , contr-path (is-f (flatten CF pd)) (c , flatten-frm CF pd)) , bd-frame CF pd

  --           pth : (α : Σ (Σ (W P i) (λ w → Σ (Frame P w c) (CF w c))) (Frame (P // CF) pd)) → ctr == α
  --           pth ((w , cf , r) , sf) = {!!}

    -- What do we know at this point?  We know that c
    -- is the multipled object and the frame is the chosen one.

    -- Now, we have this pasting diagram and a frame which
    -- witnesses that the nodes of the flattened tree are w's
    -- and the output frame is the right one and so on.

    -- But I don't think this will be enough.  Yes, indeed.
    -- This says nothing about the outside frame and w and so on.



  -- Let's rephrase.  Suppose you don't give me μ and ϕ,
  -- but rather a proof that they are contractible.  Then
  -- I have this guy for free, no?
  -- BDDomain : {I : Type₀} (P : Poly I)
  --   → (is-f : {i : I} (w : W P i) → is-contr (Σ (γ P i) (Frame P w)))
  --   → PolyDomain P
  -- F (BDDomain P is-f) w c f = contr-center (is-f w) == (c , f) 
  -- H (BDDomain P is-f) = BDDomain (P // (λ w c f → contr-center (is-f w) == (c , f))) (claim P is-f)

  -- module _ {I : Type₀} (P : Poly I)
  --   (μ : {i : I} (w : W P i) → γ P i)
  --   (ϕ : {i : I} (w : W P i) → Frame P w (μ w)) where

  --   CF : FillingFamily P
  --   CF w c f = (c , f) == (μ w , ϕ w)

  --   -- What is contractible with this definition?
  --   cmp-contr : {i : I} (w : W P i) → is-contr (CompositeFor CF w)
  --   cmp-contr w = has-level-in (ctr , pth)

  --     where ctr : CompositeFor CF w
  --           ctr = μ w , ϕ w , idp

  --           pth : (cmp : CompositeFor CF w) → ctr == cmp
  --           pth (.(μ w) , .(ϕ w) , idp) = idp
            
    -- Yes, that's right.  So you were, in a sense, trying to
    -- show the wrong thing above.
  
  MFam : {I : Type₀} (P : Poly I)
    → (m : {i : I} (w : W P i) → Σ (γ P i) (Frame P w))
    → FillingFamily P
  MFam P m w c f = m w == (c , f)
  
  record MultOp {I : Type₀} (P : Poly I) : Type₀ where
    field

      m : {i : I} (w : W P i) → Σ (γ P i) (Frame P w)
      
      unit-m : {i : I} {c : γ P i}
        →  m (corolla P c) == (c , flatten-frm (MFam P m) (lf (i , c))) 

      assoc-m : {i : I} {w : W P i}
        → (κ : (ic : Σ I (γ P)) → Node P w (snd ic) → W (P // MFam P m) ic)
        → m (substitute (MFam P m) w κ) == (fst (m w) , flatten-frm (MFam P m) (nd ((w , snd (m w) , idp) , κ))) 


  open MultOp


  
  -- Uh-oh, that didn't quite come out like I expected.  It looks
  -- unfortunately, like we are being asked for another coherence.
  -- Hmmm.
  module _ {I : Type₀} (P : Poly I) (op : MultOp P) where

    Fm = MFam P (m op)
  
    lem : {i : I} {c : γ P i} (pd : W (P // Fm) (i , c))
      → Path {A = Σ (γ P i) (λ c₀ → Frame P (flatten Fm pd) c₀)}
        (m op (flatten Fm pd)) (c , flatten-frm Fm pd) 
    lem (lf (i , c)) = unit-m op
    lem (nd ((w , ._ , idp) , κ)) = assoc-m op κ

    thm : MultOp (P // MFam P (m op))
    m thm w = (flatten Fm w , flatten-frm Fm w , lem w) , bd-frame Fm w
    unit-m thm {i , .(fst (m op w))} {w , .(snd (m op w)) , idp} = {!!} 
      -- pair= (pair= (substitute-unit Fm w) (↓-Σ-in (substitute-unit-frm Fm w (fst (m op w)) (snd (m op w)) idp) (↓-=-in {!!}))) {!!} 
    assoc-m thm {w = lf (i , c)} κ = pair= idp {!!}
    assoc-m thm {w = nd ((w₀ , .(snd (m op w₀)) , idp) , δ)} κ = pair= (pair= {!!} {!!}) {!!}


  -- EQFamily : {I : Type₀} (P : Poly I)
  --   → (μ : {i : I} (w : W P i) → γ P i)
  --   → (ϕ : {i : I} (w : W P i) → Frame P w (μ w))
  --   → FillingFamily P
  -- EQFamily P μ ϕ w c f = (μ w , ϕ w) == (c , f)

  -- module _ {I : Type₀} (P : Poly I)
  --   (μ : {i : I} (w : W P i) → γ P i)
  --   (ϕ : {i : I} (w : W P i) → Frame P w (μ w))
  --   (unit-law : {i : I} {c : γ P i} → (c , flatten-frm (EQFamily P μ ϕ) (lf (i , c))) == (μ (corolla P c) , ϕ (corolla P c)))
  --   (assoc-law : {i : I} {w : W P i}
  --     → (κ : (ic : Σ I (γ P)) → Node P w (snd ic) → W (P // (EQFamily P μ ϕ)) ic)
  --     → (μ w , flatten-frm (EQFamily P μ ϕ) (nd ((w , ϕ w , idp) , κ))) == (μ (substitute (EQFamily P μ ϕ) w κ) , ϕ (substitute (EQFamily P μ ϕ) w κ)))
  --   where

  --   CF = EQFamily P μ ϕ
    
  --   -- In other words, we can reduce the previous assumption
  --   -- to saying that μ preserves the corolla and substitution
  --   -- and that ϕ is compatible with that.
  --   lemma : {i : I} {c : γ P i} (pd : W (P // CF) (i , c))
  --     → Path {A = Σ (γ P i) (λ c₀ → Frame P (flatten CF pd) c₀)}
  --       (c , flatten-frm CF pd) (μ (flatten CF pd) , ϕ (flatten CF pd))
  --   lemma (lf (i , c)) = unit-law
  --   lemma (nd {i , .(μ w)} ((w , .(ϕ w) , idp) , s)) = assoc-law s

  --   μ₁ : {ic : Σ I (γ P)} (pd : W (P // CF) ic) → γ (P // CF) ic
  --   μ₁ {i , c} pd = flatten CF pd , flatten-frm CF pd , ! (lemma pd)

  --   ϕ₁ : {ic : Σ I (γ P)} (pd : W (P // CF) ic) → Frame (P // CF) pd (μ₁ pd)
  --   ϕ₁ {i , c} pd = bd-frame CF pd

  --   -- Yeah, it's funny.  If you apply the substitution unit to the assoc law above,
  --   -- it seems like the two actually do get linked and that the path over,
  --   -- which will be composition, might just link them up.  So surprisingly,
  --   -- this does not look completely hopeless.
  --   unit-law₁ : {ic : Σ I (γ P)} {cc : γ (P // CF) ic}
  --     → Path {A = Σ (γ (P // CF) ic) (Frame (P // CF) (corolla (P // CF) cc))}
  --       (cc , flatten-frm (EQFamily (P // CF) μ₁ ϕ₁) (lf (ic , cc))) (μ₁ (corolla (P // CF) cc) , ϕ₁ (corolla (P // CF) cc))
  --   unit-law₁ {i , .(μ w)} {w , .(ϕ w) , idp} = pair= (pair= (substitute-unit CF w) (↓-Σ-in {!!} {!!})) {!!}

  -- Okay, interesting.  So I'm being asked, as I expected, for some
  -- compatibility with bd.  That is, if I multiply a flattened tree,
  -- who had, for output, c, then I still get c.  And moreover, that
  -- when I calculate the frame of such a thing, it is the same as
  -- the canonical frame given by flattening.

  -- Okay, and the thing is, I guess it is important that this *not*
  -- depend on the filling family.  Nice.  This is actually pretty
  -- interesting.  The point is that, one way to have a coherent
  -- structure would be for it to work for *any* filling family.
  -- And the canonical example of such a thing is baez-dolan
  -- subsitution itself.

  -- -- 𝕌-Family : FillingFamily 𝕌
  -- -- 𝕌-Family w X f = ⊤

  -- -- TermFamily : {I : Type₀} (P : Poly I) → FillingFamily P
  -- -- TermFamily P w c f = ⊤

  -- -- module _ {I : Type₀} (P : Poly I)
  -- --   -- (is-f : {i : I} (w : W P i) → is-contr (CompositeFor (TermFamily P) w))
  -- --   (is-c : {i : I} {c : γ P i} (pd : W (P // TermFamily P) (i , c)) →
  -- --     is-equiv (CoherenceToComposite (TermFamily (P // TermFamily P)) pd)) where

  -- --   conj : {ic : Σ I (γ P)} (pd : W (P // TermFamily P) ic) → is-contr (CompositeFor (TermFamily (P // TermFamily P)) pd)
  -- --   conj {i , c} pd = has-level-in (ctr , pth)

  -- --     where ctr : CompositeFor (TermFamily (P // TermFamily P)) pd
  -- --           ctr = (flatten (TermFamily P) pd , flatten-frm (TermFamily P) pd , unit) , bd-frame (TermFamily P) pd , unit

  -- --           pth : (cmp : CompositeFor (TermFamily (P // TermFamily P)) pd) → ctr == cmp
  -- --           pth ((w , f , unit) , ff , unit) = is-equiv.f-g (is-c pd) ((w , f , unit) , ff , unit)
    
  -- --   conj₀ : {ic : Σ I (γ P)} {cc : γ (P // TermFamily P) ic} (coh : W ((P // TermFamily P) // TermFamily (P // TermFamily P)) (ic , cc))
  -- --     → is-contr (CoherenceFor (TermFamily ((P // TermFamily P) // TermFamily (P // TermFamily P))) coh)
  -- --   conj₀ {i , c} {w , f , unit} coh = has-level-in (ctr , λ _ → idp)

  -- --     where ctr : CoherenceFor (TermFamily ((P // TermFamily P) // TermFamily (P // TermFamily P))) coh
  -- --           ctr = tt , tt
            
  -- --   crazy : {ic : Σ I (γ P)} {cc : γ (P // TermFamily P) ic} (coh : W ((P // TermFamily P) // TermFamily (P // TermFamily P)) (ic , cc))
  -- --     → is-equiv (CoherenceToComposite (TermFamily ((P // TermFamily P) // TermFamily (P // TermFamily P))) coh)
  -- --   crazy coh = any-contr-eqv (conj₀ coh) {!!} _
            
  -- module _ {I : Type₀} {P : Poly I} (F : FillingFamily P)
  --   {i : I} {c : γ P i} (pd : W (P // F) (i , c)) 
  --   (w : W P i) (f : Frame P w c) (x : F w c f) (ff : Frame (P // F) pd (w , f , x)) where

  --   tx : (wp : w == flatten F pd)
  --     → (fp : f == flatten-frm F pd [ (λ w₀ → Frame P w₀ c) ↓ wp ])
  --     → F (flatten F pd) c (flatten-frm F pd)
  --   tx idp idp = x 

  --   finally : (wp : w == flatten F pd)
  --     → (fp : f == flatten-frm F pd [ (λ w₀ → Frame P w₀ c) ↓ wp ])
  --     → Path {A = Σ (W P i) (λ w₀ → Σ (Frame P w₀ c) (λ f₀ → F w₀ c f₀))}
  --            (w , f , x) (flatten F pd , flatten-frm F pd , tx wp fp)
  --   finally idp idp = idp

  --   record CanonicalFiller  : Type₀ where
  --     constructor cf
  --     field

  --       w-pth : w == flatten F pd
  --       f-pth : f == flatten-frm F pd [ (λ w₀ → Frame P w₀ c) ↓ w-pth ]
  --       ff-pth : ff == bd-frame F pd [ (λ { (w₀ , f₀ , x₀) → Frame (P // F) pd (w₀ , f₀ , x₀) }) ↓ finally w-pth f-pth ] 

  -- CanonicalFamily : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  --  → FillingFamily (P // F)
  -- CanonicalFamily F {i , c} pd (w , f , x) = CanonicalFiller F pd w f x

  -- module _ {I : Type₀} (P : Poly I) where

  --   claim : {ic : Σ I (γ P)} (pd : W (P // TermFamily P) ic) → is-contr (CompositeFor (CanonicalFamily (TermFamily P)) pd)
  --   claim {i , c} pd = has-level-in (ctr , pth)

  --     where ctr : CompositeFor (CanonicalFamily (TermFamily P)) pd
  --           ctr = (flatten (TermFamily P) pd , flatten-frm (TermFamily P) pd , unit) , bd-frame (TermFamily P) pd , cf idp idp idp

  --           pth : (cmp : CompositeFor (CanonicalFamily (TermFamily P)) pd) → ctr == cmp
  --           pth ((.(flatten  (TermFamily P) pd) , .(flatten-frm (TermFamily P) pd) , unit) , .(bd-frame (TermFamily P) pd) , cf idp idp idp) = idp


  --   next : {idx : Σ (Σ I (γ P)) (γ (P // TermFamily P))} (pd : W ((P // TermFamily P) // CanonicalFamily (TermFamily P)) idx)
  --     → is-contr (CompositeFor (CanonicalFamily (CanonicalFamily (TermFamily P))) pd)
  --   next {(i , c) , (w , f , unit)} pd = has-level-in (ctr , pth)

  --     where ctr : CompositeFor (CanonicalFamily (CanonicalFamily (TermFamily P))) pd
  --           ctr = (flatten (CanonicalFamily (TermFamily P)) pd , flatten-frm (CanonicalFamily (TermFamily P)) pd , cf {!!} {!!} {!!}) ,
  --                 bd-frame (CanonicalFamily (TermFamily P)) pd , cf idp idp idp

  --           pth : (cmp : CompositeFor (CanonicalFamily (CanonicalFamily (TermFamily P))) pd) → ctr == cmp
  --           pth ((._ , ._ , ccc) , ._ , cf idp idp idp) = {!c!}

  --   -- Yeah, so it looks like what you need is that other axiom to "inhabit" as it were
  --   -- the coherence type based on these compositions, find that they are equal since
  --   -- that type is contractible, then apply this equality to the inclusion function.

  --   -- You kind of saw this idea before.  So like, probably you need to define the two in
  --   -- parallel, but I'm a bit concerned because, like, it doesn't look, a priori, like the
  --   -- cohernce type is contractible.  But of course, your axioms imply that it ought to be.

  --   -- On the other hand, here you work with a generic polynomial, wheras you expect to
  --   -- prove this is special cases.  In particular, the terminal guy rarely should have
  --   -- a contractible multiplication, so ....
    
  --   -- Yup, exactly.  What about the coherences are they contractible?

  --   maybe : {i : I} {c : γ P i} (pd : W (P // TermFamily P) (i , c))
  --     → is-contr (CoherenceFor (CanonicalFamily (TermFamily P)) pd)
  --   maybe pd = has-level-in (ctr , {!!})

  --     where ctr : CoherenceFor (CanonicalFamily (TermFamily P)) pd
  --           ctr = tt , cf idp idp idp

  --           pth : (coh : CoherenceFor (CanonicalFamily (TermFamily P)) pd) → tt , cf idp idp idp == coh
  --           pth (tt , cf w-pth f-pth ff-pth) = {!!}


  --   -- No!  So we cannot somehow just repeat.
  --   -- But then is this a problem?  Like, is there
  --   -- something wrong with your definition or something?

  --   -- Well, I mean, you could try to see if the *next* guy works too, just to
  --   -- see if there is a pattern....


  -- -- CoherenceToComposite : {I : Type₀} {P : Poly I} {F : FillingFamily P} (FF : FillingFamily (P // F))
  -- --  {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  -- --  → CoherenceFor FF pd → CompositeFor FF pd
  -- -- CoherenceToComposite {P = P} {F} FF pd (f₀ , f₁) =
  -- --   (flatten F pd , flatten-frm F pd , f₀) , bd-frame F pd , f₁


  -- -- CoherenceFor : {I : Type₀} {P : Poly I} {F : FillingFamily P} (FF : FillingFamily (P // F))
  -- --   {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → Type₀
  -- -- CoherenceFor {P = P} {F} FF {c = c} pd = Σ (F (flatten F pd) c (flatten-frm F pd))
  -- --   (λ f → FF pd (flatten F pd , flatten-frm F pd , f) (bd-frame F pd))


  -- -- module _ {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- --   (is-c : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CoherenceFor (CanonicalFamily F) pd)) where

  -- --   -- Okay, this seems like progress because we no longer have a completely arbitrary
  -- --   -- section running around that we have to be compatible with.  It seems that the
  -- --   -- equations are completely general coherences related to the Baez-Dolan construction.
  -- --   conj : {ic : Σ I (γ P)} {cc : γ (P // F) ic} (coh : W ((P // F) // CanonicalFamily F) (ic , cc))
  -- --     → is-contr (CoherenceFor (CanonicalFamily (CanonicalFamily F)) coh)
  -- --   conj {i , c} {w , f , x} (lf .((i , c) , w , f , x)) = has-level-in ({!!} , {!!})

  -- --     where ctr : CoherenceFor (CanonicalFamily (CanonicalFamily F)) (lf ((i , c) , w , f , x))
  -- --           ctr = (cf (substitute-unit F w) {!!} {!!}) , (cf idp idp idp)

  -- --           pth : (coh : CoherenceFor (CanonicalFamily (CanonicalFamily F)) (lf ((i , c) , w , f , x)))
  -- --             → ctr == coh
  -- --           pth (f₀ , cf w-pth f-pth ff-pth) = {!!}
                    
  -- --     -- has-level-in (((cf (substitute-unit F w) {!!} {!!}) , (cf idp idp idp)) , {!!})
  -- --   conj {i , c} {.(flatten F pd) , .(flatten-frm F pd) , x} (nd ((pd , .(bd-frame F pd) , cf idp idp idp) , sf)) =
  -- --     has-level-in (((cf {!!} {!!} {!!}) , (cf idp idp idp)) , {!!})


  -- -- -- Right, interesting.  So then, doesn't it seem like this map ought to be
  -- -- -- an equivalence?  And then, if that's the case, wouldn't a proof that this
  -- -- -- was contractible finish the job?
  -- -- CanonicalInverse : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- --   → {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  -- --   → CompositeFor (CanonicalFamily F) pd → CoherenceFor (CanonicalFamily F) pd
  -- -- CanonicalInverse F pd ((.(flatten F pd) , .(flatten-frm F pd) , x) , .(bd-frame F pd) , cf idp idp idp) =
  -- --   x , cf idp idp idp

  -- -- CanonicalToFrom : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- --   → {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  -- --   → (cmp : CompositeFor (CanonicalFamily F) pd)
  -- --   → CoherenceToComposite (CanonicalFamily F) pd (CanonicalInverse F pd cmp) == cmp
  -- -- CanonicalToFrom F pd ((.(flatten F pd) , .(flatten-frm F pd) , x) , .(bd-frame F pd) , cf idp idp idp) = idp

  -- -- -- So here we get stuck.  However, if we assume the coherences were contractible,
  -- -- -- then we would finish.  And that would imply the uniqueness of composites in the
  -- -- -- next dimension.  And we would be left to prove that this property was inherited
  -- -- -- by the next canonical family ...
  -- -- CanonicalFromTo : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- --   → {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  -- --   → (coh : CoherenceFor (CanonicalFamily F) pd)
  -- --   → CanonicalInverse F pd (CoherenceToComposite (CanonicalFamily F) pd coh) == coh
  -- -- CanonicalFromTo F pd (x , cf w-pth f-pth ff-pth) = {!!}


  -- -- -- CoherenceFor : {I : Type₀} {P : Poly I} {F : FillingFamily P} (FF : FillingFamily (P // F))
  -- -- --   {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → Type₀
  -- -- -- CoherenceFor {P = P} {F} FF {c = c} pd = Σ (F (flatten F pd) c (flatten-frm F pd))
  -- -- --   (λ f → FF pd (flatten F pd , flatten-frm F pd , f) (bd-frame F pd))

  -- -- -- CanonicalHasFillers : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- -- --   → (is-f : {i : I} (w : W P i) → is-contr (CompositeFor F w))
  -- -- --   → (is-c : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CoherenceFor (CanonicalFamily F) pd))
  -- -- --   → {ic : Σ I (γ P)} (pd : W (P // F) ic) → is-contr (CompositeFor (CanonicalFamily F) pd)
  -- -- -- CanonicalHasFillers F is-f is-c pd = has-level-in ({!!} , {!!})

  -- -- --   where ctr : CompositeFor (CanonicalFamily F) pd
  -- -- --         ctr = (flatten F pd , flatten-frm F pd , {!!}) , bd-frame F pd , cf idp idp idp

  -- -- --         pth : (x : CompositeFor (CanonicalFamily F) pd) → ctr == x
  -- -- --         pth ((._ , ._ , x) , ._ , (cf idp idp idp)) = {!!}

  -- -- -- -- frame-and-target : {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- -- -- --   → (is-f : {i : I} (w : W P i) → is-contr (CompositeFor F w))
  -- -- -- --   → {i : I} (w : W P i) → Σ (γ P i) (Frame P w)
  -- -- -- -- frame-and-target F is-f w = let cmp = contr-center (is-f w) in fst cmp , fst (snd cmp)

  -- -- -- -- module _ {I : Type₀} {P : Poly I} (F : FillingFamily P)
  -- -- -- --   (is-f : {i : I} (w : W P i) → is-contr (CompositeFor F w))
  -- -- -- --   (hyp : {i : I} {c : γ P i} (pd : W (P // F) (i , c))
  -- -- -- --       → frame-and-target F is-f (flatten F pd) == c , flatten-frm F pd) where

  -- -- -- --   filler : {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → F (flatten F pd) c (flatten-frm F pd)
  -- -- -- --   filler pd = transport (λ pr → F (flatten F pd) (fst pr) (snd pr)) (hyp pd) (snd (snd (contr-center (is-f (flatten F pd)))))

  -- -- -- --   path-family : FillingFamily (P // F)
  -- -- -- --   path-family {i , c} pd (w , f , x) ff =
  -- -- -- --     Path {A = Σ (Σ (W P i) (λ w₀ → Σ (Frame P w₀ c) (F w₀ c))) (Frame (P // F) pd) }
  -- -- -- --       ((w , f , x) , ff)
  -- -- -- --       ((flatten F pd , flatten-frm F pd , filler pd) , bd-frame F pd)

  -- -- -- --   path-is-f : {ic : Σ I (γ P)} (pd : W (P // F) ic) → is-contr (CompositeFor path-family pd)
  -- -- -- --   path-is-f {i , c} pd = has-level-in (ctr , pth) 
  
  -- -- -- --     where ctr : CompositeFor path-family pd
  -- -- -- --           ctr = ((flatten F pd , flatten-frm F pd , filler pd) , bd-frame F pd , idp)

  -- -- -- --           pth : (coh : CompositeFor path-family pd) → ctr == coh
  -- -- -- --           pth (.(flatten F pd , flatten-frm F pd , filler pd) , .(bd-frame F pd) , idp) = idp

  -- -- -- --   conj : {ic : Σ I (γ P)} {flr : γ (P // F) ic} (coh : W ((P // F) // path-family) (ic , flr))
  -- -- -- --     → frame-and-target path-family path-is-f (flatten path-family coh)
  -- -- -- --       == flr , flatten-frm path-family coh
  -- -- -- --   conj {i , c} {w , f , x} (lf .((i , c) , w , f , x)) = pair= (pair= {!!} {!!}) {!!}
  -- -- -- --   conj {i , c} {.(flatten F pd) , .(flatten-frm F pd) , .(filler pd)} (nd ((pd , .(bd-frame F pd) , idp) , sfrm)) = {!!}

  -- -- --   -- So, it seems we still end up with a proof to do by induction.
  -- -- --   -- Mmmm.  So maybe your previous formulation is in fact simpler,
  -- -- --   -- as it does not require this extra equality ...

  -- -- --   -- Indeed, in the current formulation, it appears that we are asked to prove a
  -- -- --   -- number of (pretty reasonable) equalities, that is, coherences about the baez-dolan
  -- -- --   -- construction.  I think these two forumations are basically equivalent: in the other
  -- -- --   -- formulation, we will be asked to create an element of the path filling family, which
  -- -- --   -- should be just the same as the equality we are being asked to produce here.

  -- -- --   -- Still, for some reason I seem to have a preference for the other formulation, as it involves
  -- -- --   -- one less equality....
    

  -- -- -- Sectioned : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  -- -- -- Sectioned {I} {P} F = {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → F (flatten F pd) c (flatten-frm F pd)

  -- -- -- -- Ah, okay, maybe the interesting case is when its a *proposition*.
  -- -- -- -- Because it seems that this is what will happen in the case of set-level objects ...
  -- -- -- StrongSectioned : {I : Type₀} {P : Poly I} (F : FillingFamily P) → Type₀
  -- -- -- StrongSectioned {I} {P} F = {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (F (flatten F pd) c (flatten-frm F pd))

  -- -- -- SectionedFillers : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  -- -- --   → Sectioned F
  -- -- --   → FillingFamily (P // F)
  -- -- -- SectionedFillers P F σ {i , c} pd (w , f , x) ff =
  -- -- --   Path {A = Σ (Σ (W P i) (λ w₀ → Σ (Frame P w₀ c) (F w₀ c))) (Frame (P // F) pd) }
  -- -- --     ((w , f , x) , ff)
  -- -- --     ((flatten F pd , flatten-frm F pd , σ pd) , bd-frame F pd)

  -- -- -- -- Right, so this is pretty huge.  What does it get you?
  -- -- -- sectioned-lemma : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  -- -- --   → (σ : Sectioned F)
  -- -- --   → {i : I} {c : γ P i} (pd : W (P // F) (i , c)) → is-contr (CompositeFor (SectionedFillers P F σ) pd)
  -- -- -- sectioned-lemma P F σ {i} {c} pd = has-level-in (ctr , pth)

  -- -- --   where ctr : CompositeFor (SectionedFillers P F σ) pd
  -- -- --         ctr = (flatten F pd , flatten-frm F pd , σ pd) , bd-frame F pd , idp

  -- -- --         pth : (x : CompositeFor (SectionedFillers P F σ) pd) → ctr == x
  -- -- --         pth ((._ , ._ , ._) , ._ , idp) = idp

  -- -- -- conj : {I : Type₀} (P : Poly I) (F : FillingFamily P) (σ : Sectioned F)
  -- -- --   → Sectioned (SectionedFillers P F σ)
  -- -- -- conj P F σ {i , c} {w , f , x} (lf .((i , c) , w , f , x)) = pair= (pair= w-unit {!!}) {!!}

  -- -- --   where w-unit : w == substitute F w (λ j p → lf j)
  -- -- --         w-unit = {!!}

  -- -- --         crl : W (P // F) (i , c)
  -- -- --         crl = nd ((w , f , x) , λ j p → lf j)

  -- -- --         fpth : f == flatten-frm F crl [ (λ w₀ → Frame P w₀ c) ↓ w-unit ]
  -- -- --         fpth = {!!}

  -- -- --         -- This one is a bit of a question mark.  I don't necessarily see
  -- -- --         -- that there should be such a path.  What links your arbitrary x to
  -- -- --         -- the chosen σ?
  -- -- --         spth : x == σ crl [ uncurry (λ w₀ f₀ → F w₀ c f₀) ↓ pair= w-unit fpth ]
  -- -- --         spth = {!!}
          
  -- -- --         next : (f , x) == (flatten-frm F crl , σ crl) [ (λ w₀ → Σ (Frame P w₀ c) (F w₀ c)) ↓ w-unit ]
  -- -- --         next = ↓-Σ-in {A = W P i} {B = λ w₀ → Frame P w₀ c} {C = λ w₀ f → F w₀ c f}
  -- -- --                       {p = w-unit} {r = f} {r' = flatten-frm F crl}
  -- -- --                       {s = x} {s' = σ crl}
  -- -- --                       fpth {!!} -- spth

  -- -- -- -- ↓-Σ-in : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
  -- -- -- --   {s : C x r} {s' : C x' r'}
  -- -- -- --   (q : r == r' [ B ↓ p ])
  -- -- -- --   → s == s' [ uncurry C ↓ pair= p q ]
  -- -- -- --   → (r , s) == (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ]
  -- -- -- -- ↓-Σ-in {p = idp} idp t = pair= idp t


  -- -- -- conj P F σ {i , c} {.(flatten F pd) , .(flatten-frm F pd) , .(σ pd)} (nd ((pd , .(bd-frame F pd) , idp) , κ)) = pair= (pair= {!!} {!!}) {!!}

  -- -- -- -- Indeed, after path induction, this theorem looks entirely reasonable, if tedious.
  -- -- -- -- Hmmm.  But on the other hand, if feels like we will need some more hypotheses on
  -- -- -- -- σ, since otherwise, why should this at all be connected with x?

  -- -- -- -- SectionedDomain : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  -- -- -- --   → (σ : Sectioned F)
  -- -- -- --   → PolyDomain (P // F)
  -- -- -- -- F (SectionedDomain P F σ) = SectionedFillers P F σ
  -- -- -- -- H (SectionedDomain P F σ) = SectionedDomain (P // F) (SectionedFillers P F σ) (conj P F σ)

  -- -- -- -- SectionedMonad : {I : Type₀} (P : Poly I) (F : FillingFamily P)
  -- -- -- --   → (σ : Sectioned F)
  -- -- -- --   → is-algebraic (SectionedDomain P F σ)
  -- -- -- -- is-fillable (SectionedMonad P F σ) = sectioned-lemma P F σ 
  -- -- -- -- is-coherent (SectionedMonad P F σ) = {!!}
  -- -- -- -- coh-algebraic (SectionedMonad P F σ) = SectionedMonad (P // F) (SectionedFillers P F σ) (conj P F σ)
