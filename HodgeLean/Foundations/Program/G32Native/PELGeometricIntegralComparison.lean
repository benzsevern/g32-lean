import HodgeLean.Foundations.Program.G32Native.PELGeometricIntegralAction

noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The actual integral homology action induces precisely the marked geometric
rational cohomology action, for every endomorphism of the full ring.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
theorem geometricIntegralAction_comparison
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (f : AbelianEnd X) :
    integralOrderPullback (geometricIntegralAction X) f =
      MulOpposite.op ((b60b_periodLinearEquiv X).conjAlgEquiv ℚ (abelianEndAction X f)) := by
  apply MulOpposite.unop_injective
  ext u l
  obtain ⟨x, rfl⟩ := (b60b_periodLinearEquiv X).surjective u
  change b60b_periodLinearEquiv X x (geometricIntegralOperator X f l) =
    b60b_periodLinearEquiv X
      (abelianEndAction X f ((b60b_periodLinearEquiv X).symm
        (b60b_periodLinearEquiv X x))) l
  rw [LinearEquiv.symm_apply_apply]
  have he (z : HQ X 1) (v : abelianPeriodLattice X) :
      b60b_periodLinearEquiv X z v = abelianPeriod X z v :=
    Classical.choose_spec (spec_abelianPeriod_equiv X) z v
  rw [he, he]
  exact (geometricIntegralOperator_period X f x l).symm

/-- Every actual abelian endomorphism preserves the geometric integer-period
lattice in the same marking used in the integral realization theorem.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
theorem geometricIntegralAction_preserves
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (f : AbelianEnd X) (x : HQ X 1)
    (hx : b60b_periodLinearEquiv X x ∈ integralDual _) :
    b60b_periodLinearEquiv X (abelianEndAction X f x) ∈ integralDual _ := by
  have hh := integralOrderPullback_preserves (geometricIntegralAction X) f
    (b60b_periodLinearEquiv X x) hx
  rw [geometricIntegralAction_comparison] at hh
  change b60b_periodLinearEquiv X
    (abelianEndAction X f ((b60b_periodLinearEquiv X).symm
      (b60b_periodLinearEquiv X x))) ∈ integralDual _ at hh
  simpa only [LinearEquiv.symm_apply_apply] using hh

#print axioms geometricIntegralAction_comparison
#print axioms geometricIntegralAction_preserves
end HodgeLean.Foundations.Program.GeneralTypeIII
