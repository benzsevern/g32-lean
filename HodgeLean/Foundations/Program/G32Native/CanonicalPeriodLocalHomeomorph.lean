import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs

/-! # Local topology of the retained period quotient -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
namespace HodgeLean.Foundations.Program.G32Native

/-- The retained coordinate quotient as an additive map. -/
def canonicalPeriodHom (G : CanonicalAbelGeometry) :
    (Fin (G.k + 1) → ℂ) →+ b3_Jacobian (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) :=
  (QuotientAddGroup.mk' _).comp
    (quotientBasisEquiv (Module.finrank_fin_fun (n := 1) ℂ)
      (canonicalFormBasis G)).symm.toAddMonoidHom

/-- The additive coordinate quotient is the specified period quotient itself. -/
theorem canonicalPeriodHom_apply (G : CanonicalAbelGeometry) (v : Fin (G.k + 1) → ℂ) :
    canonicalPeriodHom G v = canonicalPeriodQuotient G v := rfl

/-- Coordinates on the original period vector space with its module topology. -/
def canonicalPeriodCoordinateHomeomorph (G : CanonicalAbelGeometry) :
    (Fin (G.k + 1) → ℂ) ≃ₜ b3Rest2_QJ (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) := by
  letI := b3_periodLattice_finite (C := AlgebraicGeometry.ComplexPoint G.Z)
    (Module.finrank_fin_fun (n := 1) ℂ)
  let L := quotientBasisEquiv (Module.finrank_fin_fun (n := 1) ℂ) (canonicalFormBasis G)
  exact {
    toEquiv := L.symm.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap }

/-- The original period quotient is locally a homeomorphism in the retained coordinates. -/
theorem canonicalPeriodQuotient_isLocalHomeomorph (G : CanonicalAbelGeometry) :
    IsLocalHomeomorph (canonicalPeriodQuotient G) := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := AlgebraicGeometry.ComplexPoint G.Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := AlgebraicGeometry.ComplexPoint G.Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := AlgebraicGeometry.ComplexPoint G.Z) h)
  exact (b2_isLocalHomeomorph_mk _ (b3_periodF (Fin 1 → ℂ)
    (AlgebraicGeometry.ComplexPoint G.Z))).comp
    (canonicalPeriodCoordinateHomeomorph G).isLocalHomeomorph

#print axioms canonicalPeriodHom
#print axioms canonicalPeriodHom_apply
#print axioms canonicalPeriodCoordinateHomeomorph
#print axioms canonicalPeriodQuotient_isLocalHomeomorph
end HodgeLean.Foundations.Program.G32Native
