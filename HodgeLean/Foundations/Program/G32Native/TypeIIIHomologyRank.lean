import HodgeLean.Foundations.Program.G32Native.TypeIIIHomologyAction
import HodgeLean.Foundations.Program.G32Native.TypeIIIQuaternionDivision

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- A sixfold with the specified definite quaternion endomorphisms has an
actual equivariant rank-three homology presentation. -/
theorem typeIII_homology_rank_three (b : ℚ) (hb : b < 0)
    (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A) (hdim : dim A.left = 6) :
    ∃ e : Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b]),
      ∀ q x i, e (((abelianEnd0Action A (θ q)).unop).dualMap x) i = q * e x i := by
  letI : DivisionRing ℍ[ℚ, -3, 0, b] := typeIIIQuaternionDivisionRing b hb
  let ρ := typeIIIHomologyAction b θ
  letI : Module ℍ[ℚ, -3, 0, b] (Dual ℚ (HQ A 1)) :=
    Module.compHom _ ρ.toRingHom
  letI : IsScalarTower ℚ ℍ[ℚ, -3, 0, b] (Dual ℚ (HQ A 1)) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change ρ (algebraMap ℚ _ r) x = r • x
      rw [ρ.commutes]
      rfl
  letI : Module.Finite ℍ[ℚ, -3, 0, b] (Dual ℚ (HQ A 1)) :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hdimQ : finrank ℚ (Dual ℚ (HQ A 1)) = 12 := by
    rw [Subspace.dual_finrank_eq, (torusCohomology_cupProductOf A).finrank_eq, hdim]
  have hdimD : finrank ℍ[ℚ, -3, 0, b] (Dual ℚ (HQ A 1)) = 3 := by
    have h := Module.finrank_mul_finrank ℚ ℍ[ℚ, -3, 0, b] (Dual ℚ (HQ A 1))
    rw [QuaternionAlgebra.finrank_eq_four, hdimQ] at h
    omega
  let eD := ((Module.finBasis ℍ[ℚ, -3, 0, b] (Dual ℚ (HQ A 1))).reindex
    (finCongr hdimD)).equivFun
  refine ⟨eD.restrictScalars ℚ, ?_⟩
  intro q x i
  change eD (q • x) i = q * eD x i
  rw [map_smul]
  rfl

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_homology_rank_three
