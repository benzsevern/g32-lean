import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleCoefficients
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # Actual local etale coordinates on the retained curve

The dimension-one smoothness assumption supplies a one-variable etale
coordinate on an actual affine neighborhood of each point.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- A smooth integral complex curve has a one-variable etale coordinate on an affine neighborhood of every point.
Source: Hartshorne, Algebraic Geometry, III.10, etale local coordinates for smooth morphisms. -/
theorem s2v_l1a_local_curve_coordinate
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (p : Z.left) :
    ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
      ∃ z : Γ(Z.left, U.1),
        (MvPolynomial.eval₂Hom (algebraMap ℂ Γ(Z.left, U.1))
          (fun _ : Fin 1 => z)).Etale := by
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  let D := localEtaleCoordinates Z 1 p
  refine ⟨⟨D.neighborhood, D.isAffine⟩, D.mem,
    D.coordinateAlgHom (MvPolynomial.X 0), ?_⟩
  have heq : MvPolynomial.eval₂Hom (algebraMap ℂ Γ(Z.left, D.neighborhood))
      (fun _ : Fin 1 => D.coordinateAlgHom (MvPolynomial.X 0)) =
      D.coordinateAlgHom.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp
  rw [heq]
  exact D.etale

/-- The local curve coordinate is etale with the actual retained base section map as its coefficient map.
Source: Hartshorne, Algebraic Geometry, III.10, etale coordinates and coefficient-ring identification. -/
theorem s2v_l1a_local_curve_coordinate_retained_coefficients
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (p : Z.left) :
    ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
      ∃ z : Γ(Z.left, U.1),
        (MvPolynomial.eval₂Hom (Z.hom.appLE ⊤ U.1 (by simp)).hom
          (fun _ : Fin 1 => z)).Etale := by
  obtain ⟨U, hp, z, hz⟩ := s2v_l1a_local_curve_coordinate Z hdim p
  let e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  have H := s2v_l1a_etale_eval_change_coefficients e
    (algebraMap ℂ Γ(Z.left, U.1)) (fun _ : Fin 1 => z) hz
  have hc : (algebraMap ℂ Γ(Z.left, U.1)).comp e.toRingHom =
      (Z.hom.appLE ⊤ U.1 (by simp)).hom := by
    change (((Z.hom.appLE ⊤ U.1 (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom) = _
    rw [RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.hom_inv_id]
    rfl
  exact ⟨U, hp, z, by simpa only [hc] using H⟩

end HodgeLean.Foundations.Program
