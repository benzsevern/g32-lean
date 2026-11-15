import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitCycles

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.TypeIIIPaper

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- An integral multiple of a rational unit induces an injective degree-one pullback. -/
theorem unit_integral_multiple_injective (d : (AbelianEnd0 A)ˣ) (s : ℤ)
    (f : AbelianEnd A) (hs : s ≠ 0)
    (hf : s • (d : AbelianEnd0 A) = (1 : ℚ) ⊗ₜ[ℤ] f) :
    Function.Injective (homPullback f.hom 1) := by
  obtain ⟨u, hu⟩ := (d.isUnit.map (abelianEnd0Action A)).unop
  have hi : Function.Injective ((abelianEnd0Action A (d : AbelianEnd0 A)).unop) := by
    rw [← hu]
    have hl : Function.LeftInverse (↑u⁻¹ : Module.End ℚ (HQ A 1))
        (↑u : Module.End ℚ (HQ A 1)) := fun x =>
      congrArg (fun g : Module.End ℚ (HQ A 1) => g x) (Units.inv_mul u)
    exact hl.injective
  have h1 := congrArg (fun x => (abelianEnd0Action A x).unop) hf
  simp only [← Int.cast_smul_eq_zsmul ℚ s, map_smul, MulOpposite.unop_smul,
    spec_g4_abelianEnd0Action_tmul, MulOpposite.unop_op, one_smul] at h1
  change (s : ℚ) • (abelianEnd0Action A (d : AbelianEnd0 A)).unop =
    homPullback f.hom 1 at h1
  intro x y hxy
  apply hi
  rw [← h1, LinearMap.smul_apply, LinearMap.smul_apply] at hxy
  have h := congrArg (fun v : HQ A 1 => (s : ℚ)⁻¹ • v) hxy
  have hc : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h

/-- The numerator of a rational unit is a smooth endomorphism. -/
theorem unit_integral_multiple_smooth (d : (AbelianEnd0 A)ˣ) (s : ℤ)
    (f : AbelianEnd A) (hs : s ≠ 0)
    (hf : s • (d : AbelianEnd0 A) = (1 : ℚ) ⊗ₜ[ℤ] f) : Smooth f.hom.left := by
  let V : AbelianQuotient.Variety :=
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  exact ccm3_smooth_surjective_group_hom f.hom
    (AbelianQuotient.surjective_of_injective_h1
      (A := V) (B := V) ⟨f.hom, inferInstance⟩
      (unit_integral_multiple_injective A d s f hs hf))

/-- Rational units preserve algebraic cycle classes in all even degrees. -/
theorem rationalPullback_algebraic (d : (AbelianEnd0 A)ˣ) (p : ℕ)
    (x : HQ A (2*p)) (hx : x ∈ algebraicCycleClassSpan A p) :
    rationalPullback A d (2*p) x ∈ algebraicCycleClassSpan A p := by
  obtain ⟨s, f, hs, hf⟩ := end0_integral_multiple A d
  letI := unit_integral_multiple_smooth A d s f hs hf
  have hc : (s : ℚ) ^ (2*p) ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr hs)
  apply (algebraicCycleClassSpan A p).smul_mem_iff hc |>.mp
  have h := LinearMap.congr_fun (rationalPullback_integral_multiple A d s f hf (2*p)) x
  rw [LinearMap.smul_apply] at h
  exact (congrArg (fun v : HQ A (2*p) => v ∈ algebraicCycleClassSpan A p) h).mpr
    (smoothPullback_span f.hom p (Submodule.mem_map_of_mem hx))

/-- The rational unit orbit of an algebraic subspace remains algebraic. -/
theorem quaternionicSpan_algebraic (U : Submodule ℚ (HQ A (2*3)))
    (hU : U ≤ algebraicCycleClassSpan A 3) :
    quaternionicSpan A U ≤ algebraicCycleClassSpan A 3 := by
  apply iSup_le
  intro d
  rintro _ ⟨x, hx, rfl⟩
  exact rationalPullback_algebraic A d 3 x (hU hx)

#print axioms rationalPullback_algebraic
#print axioms quaternionicSpan_algebraic

end HodgeLean.Foundations.Program.TypeIIIPaper
