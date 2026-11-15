import HodgeLean.Foundations.Program.G32Native.PELGeometricIntegralComparison
import HodgeLean.Foundations.Program.G32Native.PELMemberFromReference
import HodgeLean.Papers.WeilTransferDefs

noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Reference data in Corollary 12.1: an exact quaternionic sixfold, a fixed
full order acting by actual endomorphisms, and its compatible polarization.
The lattice used below is this variety's geometric lattice.
Source: G34 v1.5, Corollary 12.1; Birkenhake–Lange, §9.6. -/
structure PELSplitReference where
  B : wtr_Variety 3
  polarized : wtr_PolarizedWeil 3 B
  b : ℚ
  b_neg : b < 0
  end0 : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 B.X
  basis : Module.Basis (Fin 12) ℚ (HQ B.X 1)
  eisenstein : B.W.J = (abelianEnd0Action B.X (end0 ⟨0, 1, 0, 0⟩)).unop
  adjoint : ∀ d x y,
    polarizationForm (torusCohomology_cupProductOf B.X) polarized.nondegenerate
      ((abelianEnd0Action B.X (end0 d)).unop x) y =
    polarizationForm (torusCohomology_cupProductOf B.X) polarized.nondegenerate x
      ((abelianEnd0Action B.X (end0 (star d))).unop y)
  order : Subring ℍ[ℚ, -3, 0, b]
  finite : Module.Finite ℤ order
  full : Submodule.span ℚ (order : Set ℍ[ℚ, -3, 0, b]) = ⊤
  integral : order →+* AbelianEnd B.X
  integral_eq : ∀ a, (1 : ℚ) ⊗ₜ[ℤ] integral a = end0 a.val

namespace PELSplitReference
variable (R : PELSplitReference)

/-- The fixed rational polarization matrix.
Source: Birkenhake–Lange, §§5.2, 9.6. -/
def form : Matrix (Fin 12) (Fin 12) ℚ :=
  LinearMap.toMatrix₂ R.basis R.basis
    (polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate)

/-- All quaternion operators in the same reference basis.
Source: Birkenhake–Lange, §§1.2, 9.6. -/
def operator (d : ℍ[ℚ, -3, 0, R.b]) : Matrix (Fin 12) (Fin 12) ℚ :=
  LinearMap.toMatrix R.basis R.basis (abelianEnd0Action R.B.X (R.end0 d)).unop

/-- The entire fixed order acts on the original geometric integral homology.
Source: Birkenhake–Lange, Proposition 1.2.1 and §9.6. -/
def integralAction : R.order →+* Module.End ℤ (abelianPeriodLattice R.B.X) :=
  (geometricIntegralAction R.B.X).comp R.integral

/-- Exact compatibility of the full printed order with rational pullback.
There is no change of lattice or denominator multiplier.
Source: Birkenhake–Lange, Proposition 1.2.1 and §§1.2–1.3. -/
theorem integralAction_period (a : R.order) (x : HQ R.B.X 1)
    (l : abelianPeriodLattice R.B.X) :
    abelianPeriod R.B.X ((abelianEnd0Action R.B.X (R.end0 a.val)).unop x) l =
      abelianPeriod R.B.X x (R.integralAction a l) := by
  rw [← R.integral_eq a]
  have he := spec_g4_abelianEnd0Action_tmul R.B.X (1 : ℚ) (R.integral a)
  simp only [one_smul] at he
  rw [he]
  exact geometricIntegralOperator_period R.B.X (R.integral a) x l

/-- Reference sixfold data, with the same polarization and quadratic action. -/
theorem sixfold : SixfoldData R.B.X R.B.W R.B.pol :=
  ⟨R.polarized.dim_eq, R.polarized.isWeilType,
    R.polarized.nondegenerate, R.polarized.rosati⟩

#print axioms integralAction
#print axioms integralAction_period
end PELSplitReference
end HodgeLean.Foundations.Program.GeneralTypeIII
