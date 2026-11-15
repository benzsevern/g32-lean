import HodgeLean.Foundations.Program.SchoenCycleAnalyticGermPullback
import HodgeLean.Foundations.Program.SchoenCycleNativeSectionDifferential
import HodgeLean.Foundations.Program.SchoenCycleNativeGermComparison

/-! # Actual regular sections as analytic germs in the native chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- Actual regular sections on a neighbourhood of the point give a ring homomorphism into its native analytic germ ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
def s2e_nativeSectionGermHom
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U) :
    Γ(X.left, U) →+* AnalyticGermAt d 0 := by
  let q := fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
    (ComplexPoint.localChart X d p p + z)
  have hU : ∀ᶠ z in 𝓝 (0 : Fin d → ℂ), q z ∈ Point.overOpen U :=
    (s2e_centered_native_chart_tendsto X d p).eventually
      ((Point.isOpen_overOpen (X := X) U).mem_nhds hp)
  refine {
    toFun := fun s => ⟨Filter.Germ.ofFun (fun z => Point.evaluate U s (q z)),
      (fun z => Point.evaluate U s (q z)), s2e_native_section_analytic X d p U hp s, rfl⟩
    map_one' := ?_
    map_zero' := ?_
    map_mul' := ?_
    map_add' := ?_ }
  · apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    change (q z).underlying ∈ U at hz
    simp only [Point.evaluate, dif_pos hz, map_one]
  · intro s t
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    change (q z).underlying ∈ U at hz
    simp only [Point.evaluate, dif_pos hz, map_mul]
  · apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    change (q z).underlying ∈ U at hz
    simp only [Point.evaluate, dif_pos hz, map_zero]
  · intro s t
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    change (q z).underlying ∈ U at hz
    simp only [Point.evaluate, dif_pos hz, map_add]

/-- The native analytic germ of a regular section has its actual stalk evaluation as its central value.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeSectionGermHom_value
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)) :
    analyticGermAtValue d 0 (s2e_nativeSectionGermHom X d p U hp s) =
      p.stalkHom.hom (X.left.presheaf.germ U p.underlying hp s) := by
  change Point.evaluate U s ((ComplexPoint.localChart X d p).symm
    (ComplexPoint.localChart X d p p + 0)) = _
  rw [add_zero, (ComplexPoint.localChart X d p).left_inv
    (ComplexPoint.mem_localChart_source X d p)]
  simp only [Point.evaluate, dif_pos hp]

/-- Every denominator outside the actual affine point ideal maps to an analytic unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeSectionGermHom_primeCompl_units
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.affineOpens) (hp : p.underlying ∈ U.1)
    (y : (U.2.primeIdealOf ⟨p.underlying, hp⟩).asIdeal.primeCompl) :
    IsUnit (s2e_nativeSectionGermHom X d p U.1 hp y.val) := by
  let r : Γ(X.left, U.1) := y.val
  have hy : r ∉ (U.2.primeIdealOf ⟨p.underlying, hp⟩).asIdeal := y.property
  rw [U.2.primeIdealOf_eq_map_closedPoint ⟨p.underlying, hp⟩] at hy
  have hu : IsUnit (X.left.presheaf.germ U.1 p.underlying hp r) :=
    IsLocalRing.notMem_maximalIdeal.mp hy
  apply (s2e_analyticGermAt_isUnit_iff _).mpr
  rw [s2e_nativeSectionGermHom_value]
  exact (hu.map p.stalkHom.hom).ne_zero

/-- Restricting an actual regular section preserves its native analytic germ.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeSectionGermHom_restrict
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U V : X.left.Opens) (hpU : p.underlying ∈ U)
    (hpV : p.underlying ∈ V) (hVU : V ≤ U) (s : Γ(X.left, U)) :
    s2e_nativeSectionGermHom X d p V hpV (X.left.presheaf.map (homOfLE hVU).op s) =
      s2e_nativeSectionGermHom X d p U hpU s := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply s2e_equal_germs_native_chart_evaluate X d p V U hpV hpU
  change (X.left.presheaf.map (homOfLE hVU).op ≫
    X.left.presheaf.germ V p.underlying hpV).hom s =
      (X.left.presheaf.germ U p.underlying hpU).hom s
  rw [X.left.presheaf.germ_res]

end HodgeLean.Foundations.Program
