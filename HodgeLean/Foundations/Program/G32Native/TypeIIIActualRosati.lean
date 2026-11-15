import HodgeLean.Foundations.Program.G32Native.TypeIIIPositiveInvolution
import HodgeLean.Foundations.PositivePolarizationProofs

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The Rosati map supplied by positivity on the specified definite
endomorphism algebra is quaternion conjugation. -/
theorem typeIII_actual_rosati (b : ℚ) (hb : b < 0)
    (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A)
    (hP : p1_IsPolarization A pol) (q : ℍ[ℚ, -3, 0, b]) :
    p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP)
      (p1_adjoint_mem_range_aux A hP) (θ q) = θ (star q) := by
  let ρ := p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP)
    (p1_adjoint_mem_range_aux A hP)
  have hρ0 : ρ 0 = 0 := by
    have h := p1_rosati_smul_aux A hP 0 0
    simpa only [zero_smul] using h
  have hρ1 : ρ 1 = 1 := p1_rosati_one_aux A hP
  have hρadd (x y) : ρ (x + y) = ρ x + ρ y := p1_rosati_add_aux A hP x y
  have hρmul (x y) : ρ (x * y) = ρ y * ρ x := p1_rosati_mul_aux A hP x y
  have hρsmul (r : ℚ) (x) : ρ (r • x) = r • ρ x := p1_rosati_smul_aux A hP r x
  have hρinv (x) : ρ (ρ x) = x := p1_rosati_rosati_aux A hP x
  let R0 : AbelianEnd0 A ≃ₐ[ℚ] (AbelianEnd0 A)ᵐᵒᵖ :=
    AlgEquiv.ofBijective
      { toFun := fun x => MulOpposite.op (ρ x)
        map_one' := by rw [hρ1, MulOpposite.op_one]
        map_zero' := by rw [hρ0, MulOpposite.op_zero]
        map_add' := fun x y => by rw [hρadd, MulOpposite.op_add]
        map_mul' := fun x y => by rw [hρmul, MulOpposite.op_mul]
        commutes' := fun r => by
          rw [Algebra.algebraMap_eq_smul_one, hρsmul,
            hρ1, MulOpposite.op_smul, MulOpposite.op_one,
            ← Algebra.algebraMap_eq_smul_one] }
      (MulOpposite.opEquiv.bijective.comp
        (Function.Involutive.bijective (p1_rosati_rosati_aux A hP)))
  let R := (θ.trans R0).trans θ.symm.op
  have hR (x : ℍ[ℚ, -3, 0, b]) : (R x).unop = θ.symm (ρ (θ x)) := rfl
  have hinv : ∀ x, (R ((R x).unop)).unop = x := by
    intro x
    rw [hR, hR, θ.apply_symm_apply, hρinv, θ.symm_apply_apply]
  let τ : ℍ[ℚ, -3, 0, b] →ₗ[ℚ] ℚ :=
    { toFun := fun x => LinearMap.trace ℚ (HQ A 1) (abelianEnd0Action A (θ x)).unop
      map_add' := by intro x y; simp
      map_smul' := by intro r x; simp }
  have hpos : ∀ x, x ≠ 0 → 0 < τ (x * (R x).unop) := by
    intro x hx
    change 0 < LinearMap.trace ℚ (HQ A 1)
      (abelianEnd0Action A (θ (x * (R x).unop))).unop
    rw [map_mul, hR, θ.apply_symm_apply]
    exact p1_rosati_pos_aux A hP (fun h => hx (θ.injective (h.trans θ.map_zero.symm)))
  have h := typeIII_positive_involution b hb R hinv τ hpos q
  rw [hR] at h
  simpa only [θ.apply_symm_apply] using congrArg θ h

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_actual_rosati
