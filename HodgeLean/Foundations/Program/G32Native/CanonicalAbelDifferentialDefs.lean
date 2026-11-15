import HodgeLean.Foundations.Program.G32Native.CanonicalAbelGeometry

/-! # Actual Abel lifts and their coefficient differentials -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Connectedness of the retained smooth integral curve.
Source: HodgeConjecture, ComplexPoint.connectedSpace. -/
instance canonicalCurveConnected (G : CanonicalAbelGeometry) : ConnectedSpace (ComplexPoint G.Z) :=
  AlgebraicGeometry.ComplexPoint.connectedSpace G.Z

/-- The fixed form basis defining the canonical projective coordinates.
Source: ACGH, Geometry of Algebraic Curves I, IV.1, canonical linear system. -/
def canonicalFormBasis (G : CanonicalAbelGeometry) :
    Module.Basis (Fin (G.k + 1)) ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) :=
    Module.finite_of_finrank_pos (by rw [G.hd]; omega)
  exact Module.finBasisOfFinrankEq ℂ _ G.hd

/-- The original period quotient map in the retained form coordinates.
Source: Griffiths–Harris, Principles of Algebraic Geometry, ch. 2.7, period coordinates. -/
def canonicalPeriodQuotient (G : CanonicalAbelGeometry) (v : Fin (G.k + 1) → ℂ) :
    b3_Jacobian (Fin 1 → ℂ) (ComplexPoint G.Z) :=
  QuotientAddGroup.mk ((quotientBasisEquiv (Module.finrank_fin_fun (n := 1) ℂ)
    (canonicalFormBasis G)).symm v)

/-- Differentiate the specified local Abel lift in the original ambient chart,
then use the ordered homogeneous-coordinate pairing.
Source: ACGH, Geometry of Algebraic Curves I, IV.1–IV.3, differential of the Abel map. -/
def canonicalAbelDifferential (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q) :
    (Fin (G.k + G.k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (G.k + 1) → ℂ) :=
  (coefficientDual G.k).comp
    (fderiv ℂ (F x) (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x))).toLinearMap

/-- The actual dual conormal at the original component point.
Source: Hartshorne, Algebraic Geometry, II.8, normal-conormal duality. -/
abbrev canonicalNormalFibre (G : CanonicalAbelGeometry) :=
  normalFibreOfModule (Conormal.sheaf G.ι.left)

/-- The same analytic normal complement used in the preceding U10 modules.
Source: Griffiths–Harris, Principles of Algebraic Geometry, ch. 3.4, normal tangent quotient. -/
abbrev canonicalNormalComplement (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :=
  (closedImmersionDerivativeProjection G.W G.Q G.ι G.k (G.k + G.k) x).ker

example (G : CanonicalAbelGeometry) (i : Fin (G.k + 1)) :
    (canonicalFormBasis G).repr (canonicalFormBasis G i) = Finsupp.single i 1 :=
  (canonicalFormBasis G).repr_self i

example (G : CanonicalAbelGeometry) (v : Fin (G.k + 1) → ℂ) :
    canonicalPeriodQuotient G v =
      QuotientAddGroup.mk ((quotientBasisEquiv (Module.finrank_fin_fun (n := 1) ℂ)
        (canonicalFormBasis G)).symm v) := rfl

example (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q) : canonicalAbelDifferential G F x 0 = 0 := map_zero _

example (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    canonicalNormalFibre G x = normalFibreOfModule (Conormal.sheaf G.ι.left) x := rfl

example (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    canonicalNormalComplement G x =
      (closedImmersionDerivativeProjection G.W G.Q G.ι G.k (G.k + G.k) x).ker := rfl

#print axioms canonicalFormBasis
#print axioms canonicalPeriodQuotient
#print axioms canonicalAbelDifferential
end HodgeLean.Foundations.Program.G32Native
