import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian13ComparisonProofs

/-! # Equation comparison at a smooth regular anchor

Implication from a smooth component anchor and a regular equation to equality
of the two degree-two germs. No assertion of smoothness at an arbitrary regular
zero is made here. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

/-- At a smooth regular anchor, the transported component and equation coclasses have equal germs.
Source: `bh13_exponential_normal_chart`, `bh10_equation_chart`, `bh9_chart_germ`,
and `supportRelativeCohomologyGerm_restrict`. -/
theorem bh13_smooth_local_comparison
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (p : Fin (dim X.left) → ℂ) (hp : f p = 0) (hd : fderiv ℂ f p ≠ 0)
    (ha : abelianExp X p ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    supportRelativeCohomologyGerm (TopCat.of (Fin (dim X.left) → ℂ))
      {z | f z = 0} 2 ⊤ p (mem_univ p)
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim X.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim X.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_coverMap X x f hs)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2)
            (cycleComponentSupportedInjectiveClass X x hx))))) =
    supportRelativeCohomologyGerm (TopCat.of (Fin (dim X.left) → ℂ))
      {z | f z = 0} 2 ⊤ p (mem_univ p)
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim X.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim X.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_normalMap (dim X.left) f
        (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt))
        (normalizedPointCoclass 1))) :=
  bh13_smooth_local_comparison_aux X x hx f hf hs p hp hd ha

open HodgeLean.Foundations.Curves

example : ∃ (x : E.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim E.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ p, f p = 0 ↔ abelianExp E p ∈ bh4_componentSupport E x),
    supportRelativeCohomologyGerm (TopCat.of (Fin (dim E.left) → ℂ))
      {z | f z = 0} 2 ⊤ 0 (mem_univ 0)
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim E.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim E.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim E.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_coverMap E x f hs)
        (complexSupportInjectiveSectionCohomologyEquiv E
          (cycleComponentAnalyticClosedSupport E x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology E
            (cycleComponentAnalyticClosedSupport E x) 2)
            (cycleComponentSupportedInjectiveClass E x hx))))) =
    supportRelativeCohomologyGerm (TopCat.of (Fin (dim E.left) → ℂ))
      {z | f z = 0} 2 ⊤ 0 (mem_univ 0)
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim E.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim E.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim E.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_normalMap (dim E.left) f
        (continuous_iff_continuousAt.mpr fun z ↦ (hf z (mem_univ z)).continuousAt))
        (normalizedPointCoclass 1))) := by
  obtain ⟨τ, q, a, b, hτ, hsurj, hcoord⟩ := bh6_elliptic_coordinates_aux
  obtain ⟨x, hx, hxS⟩ := bh6_point_component_aux
  let f := bh6_theta τ ∘ q
  have ht := (bh6_theta_zeros τ hτ).1
  have hqa (p : Fin (dim E.left) → ℂ) : AnalyticAt ℂ q p :=
    q.toLinearMap.toContinuousLinearMap.analyticAt p
  have hf : AnalyticOnNhd ℂ f univ :=
    fun p _ ↦ (ht (q p) (mem_univ _)).comp (hqa p)
  have hs (p : Fin (dim E.left) → ℂ) :
      f p = 0 ↔ abelianExp E p ∈ bh4_componentSupport E x := by
    rw [hxS, Set.mem_singleton_iff]
    exact bh6_theta_kernel τ hτ q a b hsurj hcoord p
  have hz : bh6_theta τ 0 = 0 :=
    (bh6_theta_zeros τ hτ).2 0 |>.mpr ⟨0, 0, by simp⟩
  have hp : f 0 = 0 := by simpa [f] using hz
  have hd : fderiv ℂ f 0 ≠ 0 := by
    change fderiv ℂ (bh6_theta τ ∘ q) 0 ≠ 0
    rw [fderiv_comp 0 (ht (q 0) (mem_univ _)).differentiableAt
      (hqa 0).differentiableAt]
    intro h
    have hv := congrArg (fun L : (Fin (dim E.left) → ℂ) →L[ℂ] ℂ ↦ L (q.symm 1)) h
    have hqfd : fderiv ℂ q 0 = q.toLinearMap.toContinuousLinearMap :=
      q.toLinearMap.toContinuousLinearMap.hasFDerivAt.fderiv
    rw [ContinuousLinearMap.comp_apply, hqfd] at hv
    change fderiv ℂ (bh6_theta τ) (q 0) (q (q.symm 1)) = 0 at hv
    rw [q.apply_symm_apply, map_zero] at hv
    exact bh6_theta_simple_aux τ hτ 0 hz hv
  have ha : abelianExp E 0 ∈ cycleComponentSmoothSupportAmbientOpen E x := by
    rw [cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension E x
      (by simpa only [E_dim, Nat.cast_one] using hx)]
    exact mem_univ _
  exact ⟨x, hx, f, hf, hs, bh13_smooth_local_comparison E x hx f hf hs 0 hp hd ha⟩

end HodgeLean.Adapters
