import HodgeLean.Foundations.Program.CompensationAssemblyDefs
import HodgeLean.RealDefs.TopDegreeRank
import HodgeLean.RealDefs.PointClassConstant
import HodgeLean.RealDefs.ComplexFundamentalClass
import HodgeLean.Foundations.Curves.CurveDegree
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cfd_top_point_isClosed {Y : Over (Spec ↧ℂ)} {d : ℕ}
    [SmoothOfRelativeDimension d Y.hom] {x : Y.left} (hx : Order.coheight x = d) :
    IsClosed ({x} : Set Y.left) := by
  have hh : Order.height x ≤ d - d :=
    SmoothOfRelativeDimension.height_le_sub_of_coheight_eq (f := Y.hom) x (p := d) hx
  have hmin : IsMin x := Order.height_eq_zero.mp (by simpa using hh)
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hyx : y ⤳ x := Scheme.le_iff_specializes.mp (hmin (Scheme.le_iff_specializes.mpr hxy))
  exact (hxy.antisymm hyx).eq.symm

/-- A rational top coordinate taking pure top cycles to their degree. -/
theorem cfd_top_integration (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : dim Y.left = d) :
    ∃ I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ, ∀ c : AlgebraicCycle Y.left ℚ,
      (∀ x, c x ≠ 0 → Order.coheight x = d) →
      I (ccm3_cycleClass Y d c) = AlgebraicCycle.degree Y.hom c := by
  classical
  letI : SmoothOfRelativeDimension d Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (X := Y.left) (f := Y.hom)
    rwa [hY] at h
  letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  letI := complexPointsPreconnected.preconnected Y
  letI := (finiteBetti_abelian Y).finite (2 * d)
  obtain ⟨x, _, hx⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := Y.left))
  have hxc : Order.coheight x = d :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := Y.hom) x hx
  let v := cycleComponentSheafClass Y x hxc
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass Y d
  have hv : v ≠ 0 := cycleComponentSheafClass_ne_zero_of_fundamentalClass Y d x hxc w hw
  have hr : Module.finrank ℚ (HQ Y (2 * d)) = 1 := j5d_finrank_HQ_top complexPointsPreconnected Y d
  let e : HQ Y (2 * d) ≃ₗ[ℚ] ℚ := LinearEquiv.ofFinrankEq (R := ℚ) (HQ Y (2 * d)) ℚ (by simpa using hr)
  have hev : e v ≠ 0 := fun h => hv (e.injective (h.trans e.map_zero.symm))
  let I := e.trans (LinearEquiv.smulOfNeZero ℚ ℚ (e v)⁻¹ (inv_ne_zero hev))
  have hIv : I v = 1 := by
    change (e v)⁻¹ * e v = 1
    exact inv_mul_cancel₀ hev
  have hpoint (z : Y.left) (hz : Order.coheight z = d) :
      I (cycleComponentSheafClass Y z hz) = 1 := by
    rw [cycleComponentSheafClass_eq_of_coheight_eq Y d z x hz hxc]
    exact hIv
  refine ⟨I, ?_⟩
  intro c hc
  have hdeg : AlgebraicCycle.degree Y.hom c = ∑ᶠ z, c z := by
    rw [AlgebraicCycle.degree_apply]
    apply finsum_congr
    intro z
    by_cases hz : c z = 0
    · simp only [hz, smul_zero]
    · rw [Curves.residueDegree_eq_one (cfd_top_point_isClosed (hc z hz)), one_smul]
  have hcoeff : (∑ᶠ z : {z : Y.left // Order.coheight z = d}, c z.1) = ∑ᶠ z, c z := by
    rw [finsum_subtype_eq_finsum_cond]
    apply finsum_congr
    intro z
    rw [finsum_eq_if]
    by_cases hz : Order.coheight z = d
    · exact if_pos hz
    · rw [if_neg hz]
      exact (not_ne_iff.mp (fun hn => hz (hc z hn))).symm
  let g : {z : Y.left // Order.coheight z = d} → HQ Y (2 * d) :=
    fun z => c z.1 • cycleComponentSheafClass Y z.1 z.2
  change I (∑ᶠ z, g z) = _
  calc
    I (∑ᶠ z, g z) = ∑ᶠ z, I (g z) := I.toAddEquiv.map_finsum g
    _ = ∑ᶠ z : {z : Y.left // Order.coheight z = d}, c z.1 := by
      apply finsum_congr
      intro z
      change I (c z.1 • (cycleComponentSheafClass Y z.1 z.2 : HQ Y (2 * d))) = c z.1
      calc
        I (c z.1 • (cycleComponentSheafClass Y z.1 z.2 : HQ Y (2 * d))) =
            c z.1 • I (cycleComponentSheafClass Y z.1 z.2) := I.map_smul _ _
        _ = c z.1 * 1 := congrArg (fun r : ℚ => c z.1 * r) (hpoint z.1 z.2)
        _ = c z.1 := mul_one _
    _ = AlgebraicCycle.degree Y.hom c := hcoeff.trans hdeg.symm

end HodgeLean.Foundations.Program
