import HodgeLean.Foundations.Program.UniversalFamilyB60cSignature
import HodgeLean.Foundations.Program.UniversalFamilyB60cGraph
import HodgeLean.Foundations.Program.UniversalFamilyB60cEigen

noncomputable section
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

/-- An isometry of the inverse alternating forms preserves the original bivectors. -/
theorem b60c_bivector_map_of_dualForm
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (e : V ≃ₗ[K] W) {ω : ⋀[K]^2 V} {η : ⋀[K]^2 W}
    (hω : IsNondegenerate ω) (hη : IsNondegenerate η)
    (hE : ∀ x y, dualForm hη (e x) (e y) = dualForm hω x y) :
    exteriorPower.map 2 e.toLinearMap ω = η := by
  have hm := b2a_isNondegenerate_map e hω
  have hforms : ∀ x y, dualForm hm x y = dualForm hη x y := by
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    exact (b60b_dualForm_map_equiv e hω hm x y).trans (hE x y).symm
  have hi : (contractEquiv hm).symm = (contractEquiv hη).symm := by
    ext y x
    exact hforms x y
  apply contract_injective
  exact congrArg LinearEquiv.toLinearMap (congrArg LinearEquiv.symm hi)

#print axioms b60c_bivector_map_of_dualForm

open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers
open HodgeLean.Foundations.WeilHermitian

/-- Restrict a Hermitian marking to rational cohomology. -/
def b60c_rationalMarking (P Q : g32t_Sixfold)
    (e : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0] b60c_V Q) :
    HQ P.X 1 ≃ₗ[ℚ] HQ Q.X 1 :=
  (WithJ.equiv (b60c_J P)).symm |>.trans
    ((e.restrictScalars ℚ).trans (WithJ.equiv (b60c_J Q)))

/-- The rational restriction respects the quadratic generator. -/
theorem b60c_rationalMarking_action (P Q : g32t_Sixfold)
    (e : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0] b60c_V Q) (x : HQ P.X 1) :
    b60c_rationalMarking P Q e (P.W.J x) =
      Q.W.J (b60c_rationalMarking P Q e x) := by
  have hx : (WithJ.equiv (b60c_J P)).symm (P.W.J x) =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) •
        (WithJ.equiv (b60c_J P)).symm x := by
    apply (WithJ.equiv (b60c_J P)).injective
    rw [equiv_omega_smul]
    rfl
  change WithJ.equiv (b60c_J Q) (e ((WithJ.equiv (b60c_J P)).symm (P.W.J x))) = _
  rw [hx, e.map_smul, equiv_omega_smul]
  rfl

#print axioms b60c_rationalMarking_action

/-- The imaginary coefficient of a Hermitian isometry preserves the polarization
bivector, with its given normalization. -/
theorem b60c_rationalMarking_polarization (P Q : g32t_Sixfold)
    (hP : g32t_IsMember P) (hQ : g32t_IsMember Q)
    (e : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0] b60c_V Q)
    (he : ∀ x y, b60c_H Q hQ (e x) (e y) = b60c_H P hP x y) :
    exteriorPower.map 2 (b60c_rationalMarking P Q e).toLinearMap
      (polarizationVec (torusCohomology_cupProductOf P.X) P.pol) =
      polarizationVec (torusCohomology_cupProductOf Q.X) Q.pol := by
  letI := (torusCohomology_cupProductOf P.X).finite
  letI := (torusCohomology_cupProductOf Q.X).finite
  apply b60c_bivector_map_of_dualForm _ hP.nondegenerate hQ.nondegenerate
  intro x y
  exact congrArg QuadraticAlgebra.im
    (he ((WithJ.equiv (b60c_J P)).symm x) ((WithJ.equiv (b60c_J P)).symm y))

#print axioms b60c_rationalMarking_polarization

/-- Two isometries to the fixed Hermitian model induce a rational polarized marking. -/
theorem b60c_marking_of_common_model (P Q : g32t_Sixfold)
    (hP : g32t_IsMember P) (hQ : g32t_IsMember Q)
    (eP : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0] (Fin 6 → QuadraticAlgebra ℚ (-3) 0))
    (eQ : b60c_V Q ≃ₗ[QuadraticAlgebra ℚ (-3) 0] (Fin 6 → QuadraticAlgebra ℚ (-3) 0))
    (heP : ∀ x y, b60_H (eP x) (eP y) = b60c_H P hP x y)
    (heQ : ∀ x y, b60_H (eQ x) (eQ y) = b60c_H Q hQ x y) :
    ∃ e : HQ P.X 1 ≃ₗ[ℚ] HQ Q.X 1,
      (∀ x, e (P.W.J x) = Q.W.J (e x)) ∧
      exteriorPower.map 2 e.toLinearMap
        (polarizationVec (torusCohomology_cupProductOf P.X) P.pol) =
        polarizationVec (torusCohomology_cupProductOf Q.X) Q.pol := by
  let e := eP.trans eQ.symm
  refine ⟨b60c_rationalMarking P Q e, b60c_rationalMarking_action P Q e, ?_⟩
  apply b60c_rationalMarking_polarization P Q hP hQ e
  intro x y
  rw [← heQ]
  change b60_H (eQ (eQ.symm (eP x))) (eQ (eQ.symm (eP y))) = _
  rw [eQ.apply_symm_apply, eQ.apply_symm_apply, heP]

#print axioms b60c_marking_of_common_model

end HodgeLean.Foundations.Program
