import HodgeLean.Foundations.Program.G32Native.TypeIIIInducedAction

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program.G32Native

private theorem quaternion_generator_trace_skew (b : ℚ)
    (x z y : ℍ[ℚ, -3, 0, b]) :
    (((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) * x) * z * star y).re =
      -(x * z * star ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) * y)).re := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases z with ⟨z0, z1, z2, z3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  simp [QuaternionAlgebra.mk_mul_mk, Star.star,
    QuaternionAlgebra.instStarQuaternionAlgebra]
  ring

/-- The trace equation for the actual polarization gives canonical Rosati on
its Eisenstein generator, on the same retained homology presentation.
Source: G32 v0.16, Lemma 8.1, first paragraph of proof;
Birkenhake–Lange, Complex Abelian Varieties, second edition, sections 5.1 and 9.6. -/
theorem TypeIIISixfoldData.generator_rosati
    {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    {pol : HQ A 2} (Q : TypeIIISixfoldData A pol) :
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol)
      (Q.pullback (Q.endomorphisms (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop := by
  apply (isRosatiSkew_iff_skew _ _).mpr
  intro φ ψ
  rw [Q.trace_eq, Q.trace_eq]
  simp_rw [Q.homology_action]
  have hre (f : Fin 3 → ℍ[ℚ, -3, 0, Q.b]) :
      (∑ i, f i).re = ∑ i, (f i).re := by
    simp [Fin.sum_univ_succ]
  rw [hre, hre]
  simp_rw [quaternion_generator_trace_skew]
  rw [Finset.sum_neg_distrib]
  ring

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.generator_rosati
