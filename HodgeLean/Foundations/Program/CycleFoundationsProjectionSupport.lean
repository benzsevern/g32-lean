import HodgeLean.Foundations.Program.CycleFoundationsDimension
import HodgeLean.Foundations.Program.CycleFoundationsProjectionComparison
import HodgeLean.Foundations.Program.CompensationAssemblySpan2Local

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.Limits
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cfd_projection_image_support_isZero
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d) (hs : s = q + d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s)
    (himage : Order.coheight ((fst A Y).left x) ≠ q) :
    IsZero (AddCommGrpCat.of
      (H_[cycleComponentAnalyticClosedSupport A ((fst A Y).left x)]^(2 * q)(A; ℚ))) := by
  let y := (fst A Y).left x
  let a := TopologicalSpace.dim A.left
  have hsum := cq_point_height_add_coheight A a rfl y
  have hbound : Order.coheight y ≤ a := by
    calc
      Order.coheight y ≤ Order.height y + Order.coheight y := le_add_self
      _ = a := hsum
  have hfinite : Order.coheight y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top a) hbound
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hge := cfd_projection_image_coheight_ge A Y d s q hY hs x hx
  have hgt : (q : ℕ∞) < Order.coheight y := lt_of_le_of_ne hge himage.symm
  rw [← hp] at hgt
  have hpgt : q < p := by exact_mod_cast hgt
  exact cq_prime_support_isZero_of_lt A y hp.symm (2 * q) (by omega)

theorem cfd_traceProjection_prime_supported
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * q + 2 * d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s) :
    ∃ c : RelativeCohomology ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
          ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) : Set (ComplexPoint A))ᶜ))
        (2 * q),
      relativeCohomologyToAbsolute ℚ _ (2 * q) c =
        cupComparison A (2 * q) (cfd_traceProjection A Y d hY I (2 * q)
          (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx))) := by
  apply cq_relative_absolute_exists
  change cohomologyMap ℚ (2 * q)
    (TopologicalSpace.Opens.inclusion' (X := TopCat.of (ComplexPoint A))
      (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)).compl)
    (cupComparison A (2 * q) (cfd_traceProjection A Y d hY I (2 * q)
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)))) = 0
  simp only [cfd_traceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← cfd_fibreTrace_naturality]
  have hz := cq_projection_component_restriction_zero A Y x hx
  have hz' : cohomologyMap ℚ (2 * q + 2 * d)
      (cq_fibreProductMap
        (TopologicalSpace.Opens.inclusion' (X := TopCat.of (ComplexPoint A))
          (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)).compl)
        (TopCat.of (ComplexPoint Y)))
      (cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
        (2 * q + 2 * d) (cupComparison (A ⊗ Y) (2 * q + 2 * d)
          (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)))) = 0 := by
    have hc (m : ℕ) (hm : 2 * s = m) : cohomologyMap ℚ m
        (cq_fibreProductMap
          (TopologicalSpace.Opens.inclusion' (X := TopCat.of (ComplexPoint A))
            (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)).compl)
          (TopCat.of (ComplexPoint Y)))
        (cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
          m (cupComparison (A ⊗ Y) m
            (HQ.castEquiv (A ⊗ Y) hm (cycleComponentSheafClass (A ⊗ Y) x hx)))) = 0 := by
      subst m
      exact hz
    exact hc _ h
  rw [hz', map_zero]

theorem cfd_traceProjection_prime_multiple
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * q + 2 * d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s)
    (himage : Order.coheight ((fst A Y).left x) = q) :
    ∃ r : ℚ, cfd_traceProjection A Y d hY I (2 * q)
        (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)) =
      r • cycleComponentSheafClass A ((fst A Y).left x) himage := by
  obtain ⟨c, hc⟩ := cfd_traceProjection_prime_supported A Y d s q hY I h x hx
  obtain ⟨r, hr⟩ := cq_span_relative_multiple A ((fst A Y).left x) q himage c
  refine ⟨r, ?_⟩
  apply (cupComparison A (2 * q)).injective
  rw [← hc, hr, map_smul, map_smul]
  congr 1
  exact (ccm16_supportedComparison_forget A
    (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)) (2 * q)
    (cycleComponentSupportedInjectiveClass A ((fst A Y).left x) himage)).trans
      (bh11_cupComparison_eq_raw A (2 * q)
        (cycleComponentSheafClass A ((fst A Y).left x) himage)).symm

theorem cfd_traceProjection_prime_zero
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * q + 2 * d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s)
    (himage : Order.coheight ((fst A Y).left x) ≠ q) :
    cfd_traceProjection A Y d hY I (2 * q)
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)) = 0 := by
  obtain ⟨c, hc⟩ := cfd_traceProjection_prime_supported A Y d s q hY I h x hx
  have hzero := cfd_projection_image_support_isZero A Y d s q hY (by omega) x hx himage
  let S := cycleComponentAnalyticClosedSupport A ((fst A Y).left x)
  have hz := cq_support_sheaf_isZero_to_singular A S (2 * q) hzero
  letI := ModuleCat.subsingleton_of_isZero hz
  have hc0 : c = 0 := Subsingleton.elim _ _
  apply (cupComparison A (2 * q)).injective
  rw [← hc, hc0, map_zero, map_zero]

end HodgeLean.Foundations.Program
