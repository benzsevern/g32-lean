import HodgeLean.Foundations.Program.G32Native.PairedC3AffineSliceCoefficient

/-! # The adapted equation and its unit coefficient on the actual slice -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The coefficient of two branch equations with equal reduced restriction
is a unit on the slice, and their adapted difference belongs to its actual
ideal. Both assertions retain the original affine section map.
Source: Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem paired_c3_affine_normalized_equation
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (D E : X.IdealSheafData) (heq : D.comap i = E.comap i)
    (hproper : (E.comap i).support ≠ ⊤)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)] (u v : Γ(X, U))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v}) :
    ∃ a : Γ(X, U), u - a * v ∈ i.ker.ideal U ∧
      IsUnit ((i.app U.1).hom a) := by
  obtain ⟨a, ha⟩ := paired_c3_affine_slice_coefficient i D E heq U u v hu hv
  have hreg := paired_c3_restricted_branch_regular i E hproper U v hv
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
  refine ⟨a, ?_, paired_c3_slice_coefficient_unit (i.app U.1).hom u v a hspan ?_ ha⟩
  · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    exact ha
  · intro b c hbc
    apply hreg
    change (i.app U.1).hom v * b = (i.app U.1).hom v * c
    simpa only [mul_comm] using hbc

end HodgeLean.Foundations.Program.G32Native
