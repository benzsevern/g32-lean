import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperDefs
import HodgeLean.Adapters.AbelianCMData
import HodgeLean.Adapters.AbelianHomPullbackDegrees

noncomputable section
set_option maxHeartbeats 40000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- A rational endomorphism has a nonzero integral multiple in the integral endomorphisms. -/
theorem end0_integral_multiple (d : AbelianEnd0 A) :
    ∃ (s : ℤ) (f : AbelianEnd A), s ≠ 0 ∧
      s • d = (1 : ℚ) ⊗ₜ[ℤ] f := by
  let j := TensorProduct.mk ℤ ℚ (AbelianEnd A) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ j).mpr
      (TensorProduct.isBaseChange ℤ (AbelianEnd A) ℚ)
  obtain ⟨⟨f, s⟩, hfs⟩ :=
    IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ) j d
  refine ⟨s, f, nonZeroDivisors.coe_ne_zero s, ?_⟩
  have h := IsLocalizedModule.mk'_cancel' j f s
  simp only [Function.uncurry_apply_pair] at hfs
  rw [hfs, Submonoid.smul_def] at h
  exact h

/-- Clearing a denominator in degree one scales the degree `n` action by its `n`th power. -/
theorem rationalPullback_integral_multiple (d : AbelianEnd0 A) (s : ℤ)
    (f : AbelianEnd A) (h : s • d = (1 : ℚ) ⊗ₜ[ℤ] f) (n : ℕ) :
    (s : ℚ) ^ n • rationalPullback A d n = homPullback f.hom n := by
  have h1 := congrArg (fun x => (abelianEnd0Action A x).unop) h
  simp only [← Int.cast_smul_eq_zsmul ℚ s, map_smul, MulOpposite.unop_smul,
    spec_g4_abelianEnd0Action_tmul, MulOpposite.unop_op, one_smul] at h1
  change (s : ℚ) • (abelianEnd0Action A d).unop = homPullback f.hom 1 at h1
  rw [spec_homPullback_eq_cupWedgeEquiv, ← h1]
  simp only [rationalPullback, exteriorPower_map_smul,
    LinearMap.smul_comp, LinearMap.comp_smul]

/-- Rational endomorphism exterior pullback preserves rational Hodge classes in every degree. -/
theorem rationalPullback_hodge (d : AbelianEnd0 A) (p : ℕ)
    (x : HQ A (2 * p)) (hx : x ∈ Hdg^p(A; ℚ)) :
    rationalPullback A d (2 * p) x ∈ Hdg^p(A; ℚ) := by
  obtain ⟨s, f, hs, hf⟩ := end0_integral_multiple A d
  have hc : (s : ℚ) ^ (2 * p) ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr hs)
  apply (Hdg^p(A; ℚ)).smul_mem_iff hc |>.mp
  have h := LinearMap.congr_fun (rationalPullback_integral_multiple A d s f hf (2*p)) x
  rw [LinearMap.smul_apply] at h
  exact (congrArg (fun v : HQ A (2*p) => v ∈ Hdg^p(A; ℚ)) h).mpr
    (spec_homPullback_hodgeClasses f.hom p x hx)

/-- An orbit span of a Hodge subspace remains in the rational Hodge classes. -/
theorem quaternionicSpan_hodge (U : Submodule ℚ (HQ A (2 * 3)))
    (hU : U ≤ Hdg^3(A; ℚ)) : quaternionicSpan A U ≤ Hdg^3(A; ℚ) := by
  apply iSup_le
  intro d
  rintro _ ⟨x, hx, rfl⟩
  exact rationalPullback_hodge A d 3 x (hU hx)


#print axioms rationalPullback_hodge
end HodgeLean.Foundations.Program.TypeIIIPaper
