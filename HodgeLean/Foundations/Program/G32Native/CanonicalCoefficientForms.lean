import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs
import HodgeLean.Foundations.Program.G32Native.AbelPeriodPairing

/-! # Original forms in the retained coefficient coordinates -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Original curve forms corresponding to the retained homogeneous coordinates. -/
def canonicalCoefficientForm (G : CanonicalAbelGeometry) :
    (Fin (G.k + 1) → ℂ) ≃ₗ[ℂ] b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z) :=
  (canonicalFormBasis G).equivFun.symm

/-- The coefficient pairing is literal period evaluation on the corresponding original form. -/
theorem canonicalCoefficientForm_period_pairing (G : CanonicalAbelGeometry)
    (a v : Fin (G.k + 1) → ℂ) :
    let h := Module.finrank_fin_fun (n := 1) ℂ
    letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
    periodLinear (canonicalCoefficientForm G a)
      (b2_coord (b3Rest2_QJ (Fin 1 → ℂ) (ComplexPoint G.Z))
        ((quotientBasisEquiv h (canonicalFormBasis G)).symm v)) = coefficientDual G.k v a := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
  change periodLinear ((canonicalFormBasis G).equivFun.symm a)
    (b2_coord (b3Rest2_QJ (Fin 1 → ℂ) (ComplexPoint G.Z))
      ((quotientBasisEquiv h (canonicalFormBasis G)).symm v)) = ∑ i, a i * v i
  exact periodLinear_basis_pairing h (canonicalFormBasis G) a v


/-- The retained homogeneous vector represents the original canonical projective form. -/
theorem canonicalCoefficientForm_homogeneous_point (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) :=
      Module.finite_of_finrank_pos (by rw [G.hd]; omega)
    (s2e_finiteDimensionalProjectivePointEquiv G.k G.hd).symm (Point.map G.eQ.hom x) =
      Projectivization.mk ℂ (canonicalCoefficientForm G (g32n_homogeneousLine G.k G.eQ x).rep)
        ((canonicalCoefficientForm G).map_ne_zero_iff.mpr (g32n_homogeneousLine G.k G.eQ x).rep_nonzero) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) :=
    Module.finite_of_finrank_pos (by rw [G.hd]; omega)
  let L := g32n_homogeneousLine G.k G.eQ x
  have hp : ComplexProjectiveSpace.vectorToComplexPoint L.rep L.rep_nonzero =
      Point.map G.eQ.hom x := by
    change ComplexProjectiveSpace.projectivizationToComplexPoint
      (Projectivization.mk ℂ L.rep L.rep_nonzero) = Point.map G.eQ.hom x
    rw [L.mk_rep]
    exact g32n_homogeneousLine_point G.k G.eQ x
  have he := s2e_finiteDimensionalProjectivePointEquiv_symm_vector G.k G.hd L.rep L.rep_nonzero
  rw [hp] at he
  exact he

#print axioms canonicalCoefficientForm
#print axioms canonicalCoefficientForm_period_pairing
#print axioms canonicalCoefficientForm_homogeneous_point
end HodgeLean.Foundations.Program.G32Native
