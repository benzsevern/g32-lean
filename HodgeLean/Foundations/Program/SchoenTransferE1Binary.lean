import HodgeLean.Foundations.Singular.RationalProductCup
import HodgeLean.Foundations.ComplexPointGroup
import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.RealDefs.FiniteBettiCompact
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! The binary comparison on the actual algebraic cohomology spaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The two presentations of the binary total-degree index agree.
Source: the natural-number antidiagonal membership formula. -/
def s4_e1_binaryIndexEquiv (n : ℕ) :
    {p : ℕ × ℕ // p.1 + p.2 = n} ≃ tensorDegreeIndex n where
  toFun p := ⟨p.val, Finset.HasAntidiagonal.mem_antidiagonal.mpr p.property⟩
  invFun p := ⟨p.val, Finset.HasAntidiagonal.mem_antidiagonal.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sum of factor cohomology tensors identifies with the cohomology of the actual scheme product.
Source: Hatcher, Algebraic Topology, §3.2, field-coefficient Künneth. -/
def s4_e1_binaryEquiv
    (A B : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral (A ⊗ B).left] [Smooth (A ⊗ B).hom] [IsProjective (A ⊗ B).hom]
    (n : ℕ) :
    (⨁ p : tensorDegreeIndex n, HQ A p.val.1 ⊗[ℚ] HQ B p.val.2) ≃ₗ[ℚ] HQ (A ⊗ B) n := by
  letI (p : ℕ) : Module.Finite ℚ (HQ A p) := (finbetti_finiteBetti A).finite p
  have hf (p : ℕ) : Module.Finite ℚ
      (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint A)) p) :=
    Module.Finite.equiv (cupComparison A p)
  exact (DirectSum.congrLinearEquiv fun p : tensorDegreeIndex n =>
      TensorProduct.congr (cupComparison A p.val.1) (cupComparison B p.val.2)).trans
    ((rationalProductCohomologyEquiv _ _ hf n).trans
      ((cohomologyHomeomorphEquiv (complexPointProdHomeomorph A B) n).symm.trans
        (cupComparison (A ⊗ B) n).symm))

#print axioms s4_e1_binaryIndexEquiv
#print axioms s4_e1_binaryEquiv
end HodgeLean.Foundations.Program
