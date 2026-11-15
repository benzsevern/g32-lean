import HodgeLean.Foundations.Program.G32Native.PELIntegralEndomorphism
import HodgeLean.Foundations.Program.G32Native.PELIntegralPrecomposition

noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.GeneralTypeIII
variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Rational periods separate vectors of the actual integral homology lattice.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.1–1.3. -/
theorem geometric_lattice_ext {l m : abelianPeriodLattice X}
    (h : ∀ x : HQ X 1, abelianPeriod X x l = abelianPeriod X x m) : l = m := by
  apply integralDual_separates (abelianLatticeBasis X)
  intro f hf
  obtain ⟨x, rfl⟩ := (b60b_periodLinearEquiv X).surjective f
  have he (v : abelianPeriodLattice X) :
      b60b_periodLinearEquiv X x v = abelianPeriod X x v :=
    Classical.choose_spec (spec_abelianPeriod_equiv X) x v
  rw [he, he]
  exact h x

/-- The actual integral homology operator of an abelian endomorphism.
Source: Birkenhake–Lange, Complex Abelian Varieties, Proposition 1.2.1. -/
def geometricIntegralOperator (f : AbelianEnd X) :
    Module.End ℤ (abelianPeriodLattice X) :=
  (Classical.choose (spec_abelianEndAction_period X f)).toIntLinearMap

/-- The integral operator has the unscaled geometric period equation.
Source: Birkenhake–Lange, Complex Abelian Varieties, Proposition 1.2.1. -/
theorem geometricIntegralOperator_period (f : AbelianEnd X) (x : HQ X 1)
    (l : abelianPeriodLattice X) :
    abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x (geometricIntegralOperator X f l) :=
  Classical.choose_spec (spec_abelianEndAction_period X f) x l

/-- The full endomorphism ring acts covariantly on geometric integral homology.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
def geometricIntegralAction : AbelianEnd X →+* Module.End ℤ (abelianPeriodLattice X) where
  toFun := geometricIntegralOperator X
  map_one' := by
    apply LinearMap.ext
    intro l
    apply geometric_lattice_ext X
    intro x
    rw [← geometricIntegralOperator_period, spec_abelianEndAction_one]
    rfl
  map_zero' := by
    apply LinearMap.ext
    intro l
    apply geometric_lattice_ext X
    intro x
    rw [← geometricIntegralOperator_period, spec_abelianEndAction_zero]
    simp only [LinearMap.zero_apply, map_zero, Pi.zero_apply]
    have hh := spec_abelianPeriod_add X x 0 0
    simp only [zero_add] at hh
    linarith
  map_add' f g := by
    apply LinearMap.ext
    intro l
    apply geometric_lattice_ext X
    intro x
    rw [← geometricIntegralOperator_period, spec_abelianEndAction_add]
    simp only [LinearMap.add_apply, map_add, Pi.add_apply, geometricIntegralOperator_period]
    rw [spec_abelianPeriod_add]
  map_mul' f g := by
    apply LinearMap.ext
    intro l
    apply geometric_lattice_ext X
    intro x
    rw [← geometricIntegralOperator_period, spec_abelianEndAction_mul]
    change abelianPeriod X (abelianEndAction X g (abelianEndAction X f x)) l =
      abelianPeriod X x (geometricIntegralOperator X f (geometricIntegralOperator X g l))
    rw [geometricIntegralOperator_period, geometricIntegralOperator_period]

#print axioms geometric_lattice_ext
#print axioms geometricIntegralOperator
#print axioms geometricIntegralOperator_period
#print axioms geometricIntegralAction
end HodgeLean.Foundations.Program.GeneralTypeIII
