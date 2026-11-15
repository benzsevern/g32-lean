import HodgeLean.Foundations.Program.G32Native.PairedResidualHyperplaneCriterion
import HodgeLean.Foundations.Program.SchoenCycleS3LinearPoints
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # Hyperplanes in the original projective coordinates

A linear coordinate change specifies the equation without changing the
slice or its intersection map.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The pullback of the coordinate hyperplane by the specified linear automorphism.
Source: Hartshorne, Algebraic Geometry, II.2 and II.7.1. -/
def residualLinearHyperplane (k : ℕ)
    (a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  (s2e_hyperplaneIdeal k).comap (s2e_linearProjectiveOverIso a).hom.left

example (k : ℕ) (a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  residualLinearHyperplane k a

/-- The equation of this hyperplane is a nonzero linear form.
Source: Hartshorne, Algebraic Geometry, II.7.1. -/
theorem residual_linear_hyperplane_form_ne_zero (k : ℕ)
    (a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
    (LinearMap.proj (0 : Fin (k + 1))).comp a.toLinearMap ≠ 0 := by
  intro h
  have hz := LinearMap.congr_fun h (a.symm (Pi.single 0 1))
  have : (1 : ℂ) = 0 := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
      LinearEquiv.apply_symm_apply, Pi.single_eq_same, LinearMap.zero_apply] using hz
  exact one_ne_zero this

/-- Its ideal is the reduced zero scheme of the actual nonzero linear equation.
Source: Hartshorne, Algebraic Geometry, II.2 and II.7.1. -/
theorem residual_linear_hyperplane_zero_scheme (k : ℕ)
    (a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
    residualLinearHyperplane k a = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure
        {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
          (a v) 0 = 0 ∧ p = (vectorToComplexPoint v hv).underlying}) := by
  let e := s2e_linearProjectiveOverIso a
  let es : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ≅
      ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) :=
    ⟨e.hom.left, e.inv.left, congrArg (fun f => f.left) e.hom_inv_id,
      congrArg (fun f => f.left) e.inv_hom_id⟩
  have hstandard : s2e_hyperplaneIdeal k =
      Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
        {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
          v 0 = 0 ∧ p = (vectorToComplexPoint v hv).underlying}) := by
    unfold s2e_hyperplaneIdeal
    congr 1
    apply TopologicalSpace.Closeds.ext
    exact (s2e_coordinate_hyperplane_closure k 0).symm
  change (s2e_hyperplaneIdeal k).comap es.hom = _
  rw [hstandard, s2e_vanishing_closure_comap_iso]
  congr 1
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨w, hw, hz, rfl⟩, rfl⟩
    let v := a.symm w
    have hv : v ≠ 0 := a.symm.map_ne_zero_iff.mpr hw
    have he := s2e_linearProjectiveOverIso_point a v hv
    have hev : e.inv.left (vectorToComplexPoint w hw).underlying =
        (vectorToComplexPoint v hv).underlying := by
      have he' : es.hom (vectorToComplexPoint v hv).underlying =
          (vectorToComplexPoint w hw).underlying := by
        change e.hom.left (vectorToComplexPoint v hv).underlying = _
        simpa only [v, LinearEquiv.apply_symm_apply] using he
      rw [← he']
      exact (Scheme.homeoOfIso es).symm_apply_apply _
    exact ⟨v, hv, by simpa only [v, LinearEquiv.apply_symm_apply] using hz, hev⟩
  · rintro ⟨v, hv, hz, rfl⟩
    refine ⟨(vectorToComplexPoint (a v) (a.map_ne_zero_iff.mpr hv)).underlying,
      ⟨a v, a.map_ne_zero_iff.mpr hv, hz, rfl⟩, ?_⟩
    rw [← s2e_linearProjectiveOverIso_point a v hv]
    exact (Scheme.homeoOfIso es).symm_apply_apply _

/-- The arbitrary-hyperplane intersection clause retains the original inclusion.
Source: Hartshorne, Algebraic Geometry, II.2. -/
theorem residual_intersection_any_hyperplane_iff
    {V : Over (Spec ↧ℂ)} (k : ℕ)
    (i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ V)
    [IsClosedImmersion i.left] (J : V.left.IdealSheafData) :
    (∃ a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ),
      ∃ e : (residualIntersection i J).left ≅ (residualLinearHyperplane k a).subscheme,
        e.hom ≫ (residualLinearHyperplane k a).subschemeι =
          (residualIntersectionFirst i J).left) ↔
    ∃ a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ),
      J.comap i.left = residualLinearHyperplane k a := by
  exact exists_congr fun a => residual_intersection_subscheme_iff i J _

#print axioms residual_linear_hyperplane_form_ne_zero
#print axioms residual_linear_hyperplane_zero_scheme
#print axioms residual_intersection_any_hyperplane_iff
end HodgeLean.Foundations.Program.G32Native
