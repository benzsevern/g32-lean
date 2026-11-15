import HodgeLean.Foundations.Program.G32Native.PairedC3SliceCoefficient
import HodgeLean.Foundations.Program.G32Native.PairedC3IntegralParameter
import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A branch coefficient on the actual affine slice neighbourhood -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Equal branch restrictions along a closed immersion give a coefficient
in the original ambient affine section ring, rather than only in a stalk.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5. -/
theorem paired_c3_affine_slice_coefficient
    {Q X : Scheme} (i : Q ⟶ X) [IsClosedImmersion i]
    (D E : X.IdealSheafData) (heq : D.comap i = E.comap i)
    (U : X.affineOpens) (u v : Γ(X, U))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v}) :
    ∃ a : Γ(X, U), (i.app U.1).hom (u - a * v) = 0 := by
  let V : Q.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  have hD := s2e_c1_affine_comap_appLE i D U V le_rfl
  have hE := s2e_c1_affine_comap_appLE i E U V le_rfl
  rw [heq] at hD
  have hspan : Ideal.span ({(i.app U.1).hom u} : Set Γ(Q, V)) =
      Ideal.span {(i.app U.1).hom v} := by
    have h := hD.symm.trans hE
    rw [hu, hv, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton] at h
    simpa only [V, Scheme.Hom.appLE_eq_app] using h
  obtain ⟨a, ha⟩ := paired_c3_lift_slice_coefficient (i.app U.1).hom
    (i.app_surjective U.1 U.2) u v hspan
  exact ⟨a, ha⟩

#print axioms paired_c3_affine_slice_coefficient

/-- The original branch generator restricts to a regular parameter on a
nonempty affine part of an integral slice with proper branch support.
Source: Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem paired_c3_restricted_branch_regular
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (D : X.IdealSheafData) (hproper : (D.comap i).support ≠ ⊤)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (v : Γ(X, U)) (hv : D.ideal U = Ideal.span {v}) :
    IsSMulRegular Γ(Q, i ⁻¹ᵁ U.1) ((i.app U.1).hom v) := by
  let V : Q.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  have hD := s2e_c1_affine_comap_appLE i D U V le_rfl
  rw [hv, Ideal.map_span, Set.image_singleton] at hD
  have hD' : (D.comap i).ideal V = Ideal.span {((i.app U.1).hom v)} := by
    simpa only [V, Scheme.Hom.appLE_eq_app] using hD
  exact paired_c3_integral_parameter_regular (D.comap i) hproper V _ hD'

#print axioms paired_c3_restricted_branch_regular
end HodgeLean.Foundations.Program.G32Native
