import HodgeLean.Adapters.KleimanProductProofs

/-! # Normal maps for smooth intersections without a translation action -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Filter
open Topology
open scoped ContDiff Manifold
open AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

/-- Expected codimension and smooth intersection give a submersive pair of normal maps. -/
theorem smooth_intersection_chart_submersion
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (hsm : ∀ v : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X y 0 : Set X.left) →
      v ∈ ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι ≫ X.hom).smoothLocus)
    (w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme)
    (hcod : Order.coheight ((ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (U : Opens (ComplexPoint X))
    (f : C(U, Fin p → ℂ))
    (hfzero : ∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x)
    (hfhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hfsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u))
    (h : C(U, Fin q → ℂ))
    (hhzero : ∀ u : U,
      h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X y)
    (hhhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h)
    (hhsub : ∀ u : U, h u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u))
    (hzero : ∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
      u.1 ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subschemeι w))
    (a : U) (ha : hc9k_appendCoordinates f h a = 0)
    (hax : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (hay : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X
      y 0)
    (haw : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X
      ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w) 0) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
      (hc9k_appendCoordinates f h) a) := by
  have ha' : Fin.append (f a) (h a) = 0 := ha
  rw [hc9k_append_eq_zero_iff] at ha'
  have haxS := (hfzero a).mp ha'.1
  have hayS := (hhzero a).mp ha'.2
  have hawS := (hzero a).mp ha
  obtain ⟨Vw, haVw, gw, hgw0, hgw⟩ :=
    hc9k_exists_component_normalMap X d (p + q) _ hcod a.1 hawS haw
  obtain ⟨n, Y, hY, j, zY, hjz, hjS, W, haW, σ, u, b, α, β, hσ, hrel, hα, hβ, hu⟩ :=
    hc9k_transverse_local_data X d x y hsm a.1 haxS hayS hax hay
  exact hc9k_pair_submersion_of_local_data X d p q _ _ _ U f hfzero hfhol hfsub h hhzero hhhol
    hhsub hzero a ha Vw haVw gw hgw0 (hgw a.1 haVw) n Y j zY hjz hjS W haW σ u b α β hσ hrel
    hα hβ hu


#print axioms smooth_intersection_chart_submersion
/-- For a smooth proper intersection of generic length one, the supported cup class is the intersection class. -/
theorem smooth_supported_intersection_product
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (h : 2 * p + 2 * q = 2 * (p + q)) (x y : X.left)
    (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (hsm : ∀ v : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X y 0 : Set X.left) →
      v ∈ ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι ≫ X.hom).smoothLocus)
    (hlength : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      ccm11_intersectionLength X.left (ccm3_primeIdeal X.left x) (ccm3_primeIdeal X.left y) w = 1)
    (hregular : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X
            y 0 : Set X.left))
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (hsupport : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subschemeι w) ≤
        cycleComponentAnalyticClosedSupport X x ⊓
          cycleComponentAnalyticClosedSupport X y) :
    ccm16_supportedCup X (cycleComponentAnalyticClosedSupport X x)
        (cycleComponentAnalyticClosedSupport X y) (2 * p) (2 * q)
        (cycleComponentSupportedInjectiveClass X x hx)
        (cycleComponentSupportedInjectiveClass X y
          hy) =
      h.symm ▸ hc9k_supportedIntersectionClass X p q x y
        hcodim hsupport := by
  set_option backward.isDefEq.respectTransparency false in
  · classical
    let : Fintype {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme} :=
      (hc9k_components_finite X x y).fintype
    choose a haS hother hsing hax hay using
      fun c => hc9k_exists_component_point X x y hregular c
    refine hc9k_supportedClass_eq_of_generic_germs_aux X
      {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme}
      (p + q)
      (fun c => (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1)
      (fun c => hcodim c.1 c.2) _ (hc9k_support_inf_eq_iSup X x y) (2 * p + 2 * q)
      (show 2 * p + 2 * q = 2 * (p + q) by omega) a
      haS (fun c => hc9k_mem_componentBoundary_compl X _ _ c (a c) (hother c) (hsing c)) _ _ ?_
    intro c
    have hother' : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
        closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left y).subscheme → w' ≠ c.1 →
        a c ∉ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w') :=
      fun w' hw' hne => hother c ⟨w', hw'⟩ (fun he => hne (congrArg Subtype.val he))
    let B : Opens (ComplexPoint X) :=
      (cycleComponentSingularAnalyticClosedFiltration X x 0 ⊔
        cycleComponentSingularAnalyticClosedFiltration X y 0 ⊔
        cycleComponentSingularAnalyticClosedFiltration X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) 0).compl
    have haB : a c ∈ B := by
      rintro ((h1 | h2) | h3)
      exacts [hax c h1, hay c h2, hsing c h3]
    obtain ⟨U, haU, hUB, f, g, hfzero, hfhol, hfsub, hgzero, hghol, hgsub, hzero⟩ :=
      hc9k_exists_transverse_chart_in X (dim X.left) p q x y hx hy c.1 c.2 (a c) (haS c)
        (hax c) (hay c) (fun w' hw' hm => by
          by_contra hne
          exact hother' w' hw' hne hm) B haB
    have hpair : ∀ u : U, hc9k_appendCoordinates f g u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
          (hc9k_appendCoordinates f g) u) := fun u hu => by
      have huB : u.1 ∈ B := hUB u.2
      exact smooth_intersection_chart_submersion X (dim X.left) p q x y hx hy hsm c.1 c.2
        (hcodim c.1 c.2) U
        f hfzero hfhol hfsub g hgzero hghol hgsub hzero u hu
        (fun h1 => huB (Or.inl (Or.inl h1))) (fun h2 => huB (Or.inl (Or.inr h2)))
        (fun h3 => huB (Or.inr h3))
    have hlen : ((ccm11_intersectionLength X.left (ccm3_primeIdeal X.left x)
        (ccm3_primeIdeal X.left y) c.1).toNat : ℚ) = 1 := by
      rw [hlength c.1 c.2]
      rfl
    have hR :
        ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
            cycleComponentAnalyticClosedSupport X y) (2 * (p + q)) (a c)
          (hc9k_supportedIntersectionClass X p q x y hcodim hsupport) =
          supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU
            (relativeCohomologyMap ℚ (2 * (p + q))
              (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X x ⊓
                cycleComponentAnalyticClosedSupport X y) (p + q) (hc9k_appendCoordinates f g)
                (fun u hu => ⟨(hfzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).1,
                  (hgzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).2⟩))
              (normalizedPointCoclass (p + q))) := by
      have hfin := hc9k_components_finite X x y
      unfold hc9k_supportedIntersectionClass
      rw [map_finsum _ (hfin.subset fun w' hw' => by
        by_contra hn
        exact hw' (dite_eq_right_iff.mpr fun h => absurd h hn))]
      rw [finsum_eq_single _ c.1 (fun w' hw' => by
        by_cases hc : closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme) ∈
              irreducibleComponents (ccm3_primeIdeal X.left x ⊔
                ccm3_primeIdeal X.left y).subscheme
        · rw [dite_eq_left_of_eq_true (eq_true hc), Nat.cast_smul_eq_nsmul ℚ, map_nsmul,
            hc9k_supportGerm_enlarge_eq_zero_of_not_mem X _ _ (a c) (hother' w' hc hw'), nsmul_zero]
        · rw [dite_eq_right_of_eq_false (eq_false hc), map_zero])]
      rw [dite_eq_left_of_eq_true (eq_true c.2), Nat.cast_smul_eq_nsmul ℚ, map_nsmul, ccm5_supportGerm_enlarge,
        ← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X)) _ _
          (le_top : U ≤ ⊤) (a c) haU]
      have hloc := hc9k_relativeCohomologyMap_map_of_comp (2 * (p + q))
        (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from le_top)
          ((cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y :
            Closeds (ComplexPoint X)) : Set (ComplexPoint X)))
        (neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr (hsupport c.1 c.2)))
        (neighborhoodSupportEnlargePairMap (U : Set (ComplexPoint X))
          (SetLike.coe_subset_coe.mpr (hsupport c.1 c.2)) ≫
          neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
            (⊤ : Opens (ComplexPoint X)) from le_top)
            (cycleComponentAnalyticClosedSupport X
              ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) :
                Set (ComplexPoint X)))
        (by apply MorphismProperty.Arrow.Hom.ext <;> rfl)
      rw [hloc, ← hc9k_relativeCohomologyMap_map_of_comp (2 * (p + q))
        (neighborhoodSupportEnlargePairMap (U : Set (ComplexPoint X))
          (SetLike.coe_subset_coe.mpr (hsupport c.1 c.2)))
        (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
            (⊤ : Opens (ComplexPoint X)) from le_top)
            (cycleComponentAnalyticClosedSupport X
              ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) :
                Set (ComplexPoint X))) _ rfl]
      have hsmul : ∀ (k : ℕ) (z : RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (U : Set (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y :
            Closeds (ComplexPoint X)) : Set (ComplexPoint X))) (2 * (p + q))),
          k • supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU z =
          supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU (k • z) := by
        intro k z
        simp only [supportRelativeCohomologyGerm, map_nsmul]
      rw [hsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, hlen, one_smul,
        hc9k_intersection_supportedClass_chart_aux X (dim X.left) p q x y c.1 c.2 (hcodim c.1 c.2) U
          f hfzero hfhol hfsub g hgzero hghol hgsub hzero hpair,
        hc9k_relativeCohomologyMap_map_of_comp _ _ _ _ rfl]
      congr 2
    have hL :
        ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
            cycleComponentAnalyticClosedSupport X y) (2 * p + 2 * q) (a c)
          (ccm16_supportedCup X (cycleComponentAnalyticClosedSupport X x)
            (cycleComponentAnalyticClosedSupport X y) (2 * p) (2 * q)
            (cycleComponentSupportedInjectiveClass X x hx)
            (cycleComponentSupportedInjectiveClass X y hy)) =
          h.symm ▸ supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU
            (relativeCohomologyMap ℚ (2 * (p + q))
              (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X x ⊓
                cycleComponentAnalyticClosedSupport X y) (p + q) (hc9k_appendCoordinates f g)
                (fun u hu => ⟨(hfzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).1,
                  (hgzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).2⟩))
              (normalizedPointCoclass (p + q))) := by
      rw [ccm17_supportedCup_germ X _ _ U (2 * p) (2 * q) (a c) haU,
        hc9k_supportedComparison_restrict, hc9k_supportedComparison_restrict,
        hc9k_prime_supportedClass_chart_aux X (dim X.left) p x hx U f hfzero hfhol hfsub,
        hc9k_prime_supportedClass_chart_aux X (dim X.left) q y hy U g hgzero hghol hgsub,
        hc9k_normalCoordinatePair_head _ U _ p q f g hfzero, hc9k_normalCoordinatePair_tail _ U _ p q f g hgzero]
      have hSx : (cycleComponentAnalyticClosedSupport X x).preimage
          (continuous_subtype_val (p := fun z => z ∈ U)) =
          (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p
            (hc9k_coordinateHead p q)).preimage (hc9k_appendCoordinates f g).continuous := by
        ext u
        change u.1 ∈ cycleComponentAnalyticClosedSupport X x ↔
          hc9k_coordinateHead p q (hc9k_appendCoordinates f g u) = 0
        rw [hc9k_coordinateHead_append, hfzero]
      have hSy : (cycleComponentAnalyticClosedSupport X y).preimage
          (continuous_subtype_val (p := fun z => z ∈ U)) =
          (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q
            (hc9k_coordinateTail p q)).preimage (hc9k_appendCoordinates f g).continuous := by
        ext u
        change u.1 ∈ cycleComponentAnalyticClosedSupport X y ↔
          hc9k_coordinateTail p q (hc9k_appendCoordinates f g u) = 0
        rw [hc9k_coordinateTail_append, hgzero]
      rw [hc9k_relativeCup_congr (TopCat.of U) _ _ _ _ hSx hSy,
        ← ccm17_relativeCup_pullback, hc9k_coordinate_product_general_aux,
        hc9k_coordinateIntersectionClass, hc9k_relativeCohomologyMap_cast,
        hc9k_relativeCohomologyMap_cast, hc9k_supportRelativeCohomologyGerm_cast]
      congr 2
      rw [hc9k_relativeCohomologyMap_map_of_comp _ _ _ _ rfl]
      apply hc9k_relativeCohomologyMap_map_of_comp
      apply MorphismProperty.Arrow.Hom.ext <;> rfl
    rw [hL, hc9k_supportGerm_cast X _ h.symm, hR]


#print axioms smooth_supported_intersection_product
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero
