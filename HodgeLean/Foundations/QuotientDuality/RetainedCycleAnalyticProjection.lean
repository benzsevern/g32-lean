import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionDomain

/-! # The continuous projection on the actual centre complement -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal projective linear projection as a continuous map on the actual algebraic centre complement.
Source: retained_projection_centre_complement_domain; retained_projective_projection_continuous.
-/
def retainedAnalyticProjection {N n : ℕ} (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ) :
    C({p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) |
      p.underlying ∉ retainedProjectionCentre ℓ},
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)))) := by
  let H := s2e_projectivePointHomeomorph N
  let L := retainedProjectionLinearMap ℓ
  let g : {p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) |
      p.underlying ∉ retainedProjectionCentre ℓ} → retained_projective_projection_domain L :=
    fun p => ⟨H.symm p.val, by
      apply (retained_projection_centre_complement_domain ℓ _).mp
      change (H (H.symm p.val)).underlying ∉ retainedProjectionCentre ℓ
      rw [Homeomorph.apply_symm_apply]
      exact p.property⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact H.symm.continuous.comp continuous_subtype_val
  exact ⟨fun p => s2e_projectivePointHomeomorph n (retained_projective_projection L (g p)),
    (s2e_projectivePointHomeomorph n).continuous.comp
      ((retained_projective_projection_continuous L).comp hg)⟩

/-- On an actual homogeneous vector, the continuous centre-complement map is the literal linear projection. -/
lemma retained_analytic_projection_vector {N n : ℕ}
    (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ) (v : CoordinateSpace N)
    (hv : v ≠ 0) (hw : ℓ.mulVec v ≠ 0)
    (h : (vectorToComplexPoint v hv).underlying ∉ retainedProjectionCentre ℓ) :
    retainedAnalyticProjection ℓ ⟨vectorToComplexPoint v hv, h⟩ =
      vectorToComplexPoint (ℓ.mulVec v) hw := by
  have he : (s2e_projectivePointHomeomorph N).symm (vectorToComplexPoint v hv) =
      Projectivization.mk ℂ v hv := by
    apply (s2e_projectivePointHomeomorph N).injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  change s2e_projectivePointHomeomorph n
    (retained_projective_projection (retainedProjectionLinearMap ℓ)
      ⟨(s2e_projectivePointHomeomorph N).symm (vectorToComplexPoint v hv), _⟩) = _
  have hq (hq : (s2e_projectivePointHomeomorph N).symm (vectorToComplexPoint v hv) ∈
      retained_projective_projection_domain (retainedProjectionLinearMap ℓ)) :
      (⟨(s2e_projectivePointHomeomorph N).symm (vectorToComplexPoint v hv), hq⟩ :
        retained_projective_projection_domain (retainedProjectionLinearMap ℓ)) =
      ⟨Projectivization.mk ℂ v hv,
        (retained_projective_projection_domain_mk (retainedProjectionLinearMap ℓ) v hv).mpr hw⟩ :=
    Subtype.ext he
  rw [hq, retained_projective_projection_mk]
  rfl

end HodgeLean.Foundations.QuotientDuality
