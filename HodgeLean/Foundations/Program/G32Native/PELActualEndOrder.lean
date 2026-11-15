import HodgeLean.Foundations.Program.G32Native.PELSplitReference

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Integral homology detects the actual endomorphism. -/
theorem geometricIntegralAction_injective : Function.Injective (geometricIntegralAction X) := by
  intro f g h
  apply spec_abelianEndAction_injective X
  ext x
  apply (b60b_periodLinearEquiv X).injective
  ext l
  have he (z : HQ X 1) : b60b_periodLinearEquiv X z l = abelianPeriod X z l :=
    Classical.choose_spec (spec_abelianPeriod_equiv X) z l
  rw [he, he, geometricIntegralOperator_period, geometricIntegralOperator_period]
  exact congrArg (fun T : Module.End ℤ (abelianPeriodLattice X) => abelianPeriod X x (T l)) h

/-- The actual endomorphism ring is finite over the integers. -/
theorem abelianEnd_finite : Module.Finite ℤ (AbelianEnd X) := by
  letI := Module.Finite.of_basis (abelianLatticeBasis X)
  exact Module.Finite.of_injective (geometricIntegralAction X).toAddMonoidHom.toIntLinearMap
    (geometricIntegralAction_injective X)

/-- The integral inclusion in rational endomorphisms is injective. -/
theorem abelianEnd_rational_injective : Function.Injective
    (Algebra.TensorProduct.includeRight : AbelianEnd X →ₐ[ℤ] AbelianEnd0 X) := by
  intro f g h
  apply spec_abelianEndAction_injective X
  have hh := congrArg (fun d => (abelianEnd0Action X d).unop) h
  simpa only [Algebra.TensorProduct.includeRight_apply,
    spec_g4_abelianEnd0Action_tmul, one_smul, MulOpposite.unop_op] using hh

variable {D : Type*} [Ring D] [Algebra ℚ D]

/-- The integral endomorphisms in a fixed rational presentation. -/
def actualEndEmbedding (e : D ≃ₐ[ℚ] AbelianEnd0 X) : AbelianEnd X →+* D :=
  e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

/-- The intersection order, in the presentation coordinates. -/
def actualEndOrder (e : D ≃ₐ[ℚ] AbelianEnd0 X) : Subring D :=
  (actualEndEmbedding X e).range

/-- The intersection order retains every integral endomorphism uniquely. -/
def actualEndOrderEquiv (e : D ≃ₐ[ℚ] AbelianEnd0 X) :
    AbelianEnd X ≃+* actualEndOrder X e :=
  RingEquiv.ofBijective (actualEndEmbedding X e).rangeRestrict
    ⟨fun _ _ h => (abelianEnd_rational_injective X) (e.symm.injective (congrArg Subtype.val h)),
      fun a => by obtain ⟨f, hf⟩ := a.property; exact ⟨f, Subtype.ext hf⟩⟩

/-- The intersection order is finite over the integers. -/
theorem actualEndOrder_finite (e : D ≃ₐ[ℚ] AbelianEnd0 X) :
    Module.Finite ℤ (actualEndOrder X e) := by
  letI := abelianEnd_finite X
  exact Module.Finite.equiv (actualEndOrderEquiv X e).toAddEquiv.toIntLinearEquiv

/-- The integral inclusion has no change of scale. -/
theorem actualEndOrder_integral_eq (e : D ≃ₐ[ℚ] AbelianEnd0 X)
    (a : actualEndOrder X e) :
    (1 : ℚ) ⊗ₜ[ℤ] (actualEndOrderEquiv X e).symm a = e a.val := by
  have h := (actualEndOrderEquiv X e).apply_symm_apply a
  have hh : actualEndEmbedding X e ((actualEndOrderEquiv X e).symm a) = a.val := by
    exact congrArg Subtype.val h
  apply e.symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact hh

/-- The intersection order spans the original rational algebra. -/
theorem actualEndOrder_full (e : D ≃ₐ[ℚ] AbelianEnd0 X) :
    Submodule.span ℚ (actualEndOrder X e : Set D) = ⊤ := by
  have hz : ∀ z : AbelianEnd0 X,
      e.symm z ∈ Submodule.span ℚ (actualEndOrder X e : Set D) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul q f =>
      have hf : e.symm ((1 : ℚ) ⊗ₜ[ℤ] f) ∈ Submodule.span ℚ (actualEndOrder X e : Set D) :=
        Submodule.subset_span ⟨f, rfl⟩
      have hh := Submodule.smul_mem (Submodule.span ℚ (actualEndOrder X e : Set D)) q hf
      simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hh
    | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw
  apply top_unique
  intro d _
  obtain ⟨z, rfl⟩ := e.symm.surjective d
  exact hz z

#print axioms actualEndOrder_finite
#print axioms actualEndOrder_integral_eq
#print axioms actualEndOrder_full
end HodgeLean.Foundations.Program.GeneralTypeIII
