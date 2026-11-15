import HodgeLean.Foundations.Program.G32Native.PairedC3AffineSliceCoefficient
import HodgeLean.Foundations.Program.G32Native.PairedC3RatioNormalization

/-! # The variable unit normalizing a supplied pair of branch equations -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Equal Cartier branch restrictions on an integral slice supply the
normalization coefficient in the original ambient section ring. Its
restriction is a unit; its ambient value need not be one or constant.
Source: Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem pairedC3_affine_normalization_unit
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (D E : X.IdealSheafData) (heq : D.comap i = E.comap i)
    (hproper : (D.comap i).support ≠ ⊤)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (u v : Γ(X, U))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v}) :
    ∃ α : Γ(X, U), (i.app U.1).hom (v - α * u) = 0 ∧
      IsUnit ((i.app U.1).hom α) := by
  obtain ⟨α, hα⟩ := paired_c3_affine_slice_coefficient i E D heq.symm U v u hv hu
  refine ⟨α, hα, ?_⟩
  let V : Q.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  have hD := s2e_c1_affine_comap_appLE i D U V le_rfl
  have hE := s2e_c1_affine_comap_appLE i E U V le_rfl
  rw [heq] at hD
  have hspan : Ideal.span ({(i.app U.1).hom v} : Set Γ(Q, V)) =
      Ideal.span {(i.app U.1).hom u} := by
    have h := hE.symm.trans hD
    rw [hu, hv, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton] at h
    simpa only [V, Scheme.Hom.appLE_eq_app] using h
  have hreg := paired_c3_restricted_branch_regular i D hproper U u hu
  apply paired_c3_slice_coefficient_unit (i.app U.1).hom v u α hspan _ hα
  intro a b hab
  apply hreg
  simpa only [smul_eq_mul, mul_comm] using hab

/-- The same coefficient is invertible on any residual base contained
in the slice. In particular this applies to the centre–slice intersection.
Source: Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem pairedC3_affine_residual_normalization_unit
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (D E M : X.IdealSheafData) (heq : D.comap i = E.comap i)
    (hproper : (D.comap i).support ≠ ⊤) (hM : i.ker ≤ M)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (u v : Γ(X, U))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v}) :
    ∃ α : Γ(X, U), (i.app U.1).hom (v - α * u) = 0 ∧
      IsUnit ((i.app U.1).hom α) ∧ IsUnit (Ideal.Quotient.mk (M.ideal U) α) := by
  obtain ⟨α, hα, hunit⟩ := pairedC3_affine_normalization_unit i D E heq hproper U u v hu hv
  refine ⟨α, hα, hunit, ?_⟩
  apply pairedC3_quotient_unit_of_slice_unit (i.app U.1).hom
    (i.app_surjective U.1 U.2) (M.ideal U) _ α hunit
  rw [← Scheme.Hom.ker_apply]
  exact hM U

#print axioms pairedC3_affine_residual_normalization_unit
#print axioms pairedC3_affine_normalization_unit
end HodgeLean.Foundations.Program.G32Native
