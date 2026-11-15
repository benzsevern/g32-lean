import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Adapters.AbelianHodgeDischarge
import HodgeLean.Foundations.ComplexSheafSingular
import HodgeLean.RealDefs.F1569
import HodgeLean.Adapters.AbelianEndomorphismsDefs
import Mathlib.Algebra.Quaternion

noncomputable section
open scoped Quaternion TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program.G32Native

/-- A diagonal quaternionic homology presentation of the polarized variety in
Lemma 8.1. The action is the actual rational endomorphism pullback, retained on
integral endomorphisms. The trace equation is on homology, the dual of `HQ A 1`.
No Weil-type or discriminant comparison is a field of these data.
Source: G32 v0.16, section 8, paragraph before Lemma 8.1;
Birkenhake–Lange, Complex Abelian Varieties, second edition, sections 5.2, 9.4–9.6. -/
structure TypeIIISixfoldData (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] (pol : HQ A 2) where
  b : ℚ
  b_neg : b < 0
  endomorphisms : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A
  pullback : AbelianEnd0 A →ₐ[ℚ] (Module.End ℚ (HQ A 1))ᵐᵒᵖ
  pullback_integral : ∀ f, pullback (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction A f)
  homology : Module.Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b])
  homology_action : ∀ q x i,
    homology (((pullback (endomorphisms q)).unop).dualMap x) i = q * homology x i
  l1 : Fin 3 → ℚ
  l2 : Fin 3 → ℚ
  l3 : Fin 3 → ℚ
  diagonal_nonzero : ∀ i, (-3 * l1 i ^ 2 + b * l2 i ^ 2 + 3 * b * l3 i ^ 2) ≠ 0
  nondegenerate : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol)
  positive : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) nondegenerate
  trace_eq : ∀ x y,
    y (contract (polarizationVec (torusCohomology_cupProductOf A) pol) x) =
      2 * (∑ i, homology x i *
        (⟨0, l1 i, l2 i, l3 i⟩ : ℍ[ℚ, -3, 0, b]) * star (homology y i)).re


variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

/-- A unit representing `−b disc(T)`, before passage to the norm quotient.
Source: G32 v0.16, Lemma 8.1. -/
def TypeIIISixfoldData.discriminantUnit (Q : TypeIIISixfoldData A pol) : ℚˣ :=
  -Units.mk0 Q.b (ne_of_lt Q.b_neg) *
    ∏ i, Units.mk0 ((-3 * Q.l1 i ^ 2 + Q.b * Q.l2 i ^ 2 + 3 * Q.b * Q.l3 i ^ 2))
      (Q.diagonal_nonzero i)

/-- The scalar value of the retained quaternionic discriminant representative. -/
theorem TypeIIISixfoldData.discriminantUnit_val (Q : TypeIIISixfoldData A pol) :
    (Q.discriminantUnit : ℚ) = -Q.b *
      ∏ i, (-3 * Q.l1 i ^ 2 + Q.b * Q.l2 i ^ 2 + 3 * Q.b * Q.l3 i ^ 2) := by
  simp only [TypeIIISixfoldData.discriminantUnit, Units.val_mul, Units.val_neg,
    Units.coe_prod, Units.val_mk0]

/-- Rank-three quaternionic homology has rational rank twelve, hence the
retained abelian variety has dimension six.
Source: G32 v0.16, section 8, opening paragraph. -/
theorem TypeIIISixfoldData.dim_eq_six (Q : TypeIIISixfoldData A pol) :
    TopologicalSpace.dim A.left = 6 := by
  letI := (torusCohomology_cupProductOf A).finite
  have h := Q.homology.finrank_eq
  rw [Subspace.dual_finrank_eq, (torusCohomology_cupProductOf A).finrank_eq] at h
  norm_num [Module.finrank_pi_fintype, QuaternionAlgebra.finrank_eq_four] at h
  omega

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.discriminantUnit_val

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.dim_eq_six
