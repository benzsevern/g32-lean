import HodgeLean.Foundations.Program.G32Native.TypeIIIActualBasis

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The actual homology trace form on the retained six basis vectors. -/
theorem TypeIIISixfoldData.trace_basis (Q : TypeIIISixfoldData A pol)
    (p q : Fin 2 × Fin 3) :
    (Q.homologyBasisVector q) (contract (polarizationVec
      (torusCohomology_cupProductOf A) pol) (Q.homologyBasisVector p)) =
      if p.2 = q.2 then 2 * (typeIIIBlockVector Q.b p.1 *
        (⟨0, Q.l1 p.2, Q.l2 p.2, Q.l3 p.2⟩ : ℍ[ℚ, -3, 0, Q.b]) *
        star (typeIIIBlockVector Q.b q.1)).re else 0 := by
  rw [Q.trace_eq]
  simp_rw [Q.homologyBasisVector_apply]
  by_cases hpq : p.2 = q.2
  · simp [← hpq]
  · simp [mul_ite, ite_mul, hpq]

/-- The generator in the second argument gives the real Hermitian entries. -/
theorem TypeIIISixfoldData.trace_basis_generator (Q : TypeIIISixfoldData A pol)
    (p q : Fin 2 × Fin 3) :
    (Q.inducedWeilAction.J.dualMap (Q.homologyBasisVector q))
      (contract (polarizationVec (torusCohomology_cupProductOf A) pol)
        (Q.homologyBasisVector p)) =
      if p.2 = q.2 then 2 * (typeIIIBlockVector Q.b p.1 *
        (⟨0, Q.l1 p.2, Q.l2 p.2, Q.l3 p.2⟩ : ℍ[ℚ, -3, 0, Q.b]) *
        star ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]) *
          typeIIIBlockVector Q.b q.1)).re else 0 := by
  rw [Q.trace_eq]
  change 2 * (∑ i, Q.homology (Q.homologyBasisVector p) i *
    (⟨0, Q.l1 i, Q.l2 i, Q.l3 i⟩ : ℍ[ℚ, -3, 0, Q.b]) *
    star (Q.homology (((Q.pullback (Q.endomorphisms
      (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop).dualMap
        (Q.homologyBasisVector q)) i)).re = _
  simp_rw [Q.homology_action, Q.homologyBasisVector_apply]
  by_cases hpq : p.2 = q.2
  · simp [← hpq]
  · simp [mul_ite, ite_mul, hpq]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.trace_basis
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.trace_basis_generator
