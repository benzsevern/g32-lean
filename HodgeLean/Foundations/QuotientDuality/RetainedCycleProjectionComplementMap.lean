import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentrePoints

/-! The actual continuous projective projection on the algebraic centre complement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The complement of the actual algebraic centre is the domain of the literal quotient projection.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_projection_line_domain_iff {N d : ℕ}
    (ℓ : Matrix (Fin (d+1)) (Fin (N+1)) ℂ)
    (p : Projectivization ℂ (CoordinateSpace N)) :
    (s2e_projectivePointHomeomorph N p).underlying ∉ retained_projection_centre ℓ ↔
      p ∈ retained_projective_projection_domain ℓ.mulVecLin.toContinuousLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
    change (vectorToComplexPoint v hv).underlying ∉ retained_projection_centre ℓ ↔ _
    rw [retained_projection_centre_vector, retained_projective_projection_domain_mk]
    rfl

/-- The actual continuous projective projection on the algebraic centre complement. -/
def retained_projection_complement_map {N d : ℕ}
    (ℓ : Matrix (Fin (d+1)) (Fin (N+1)) ℂ) :
    TopCat.of {p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) |
      p.underlying ∉ retained_projection_centre ℓ} ⟶
      a3b4_an (ProjectiveSpace.toBase (Fin (d+1)) (Spec ↧ℂ)) := by
  let eN := s2e_projectivePointHomeomorph N
  let eD := s2e_projectivePointHomeomorph d
  let L := ℓ.mulVecLin.toContinuousLinearMap
  let g : {p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) |
      p.underlying ∉ retained_projection_centre ℓ} → retained_projective_projection_domain L :=
    fun p => ⟨eN.symm p.val, (retained_projection_line_domain_iff ℓ (eN.symm p.val)).mp
      (by
        change (eN (eN.symm p.val)).underlying ∉ _
        rw [eN.apply_symm_apply]
        exact p.property)⟩
  have hg : Continuous g := (eN.symm.continuous.comp continuous_subtype_val).subtype_mk _
  exact TopCat.ofHom ⟨fun p => eD (retained_projective_projection L (g p)),
    eD.continuous.comp ((retained_projective_projection_continuous L).comp hg)⟩

/-- The continuous complement projection has the expected value on every homogeneous vector.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_projection_complement_map_vector {N d : ℕ}
    (ℓ : Matrix (Fin (d+1)) (Fin (N+1)) ℂ) (v : CoordinateSpace N) (hv : v ≠ 0)
    (h : (vectorToComplexPoint v hv).underlying ∉ retained_projection_centre ℓ) :
    retained_projection_complement_map ℓ ⟨vectorToComplexPoint v hv, h⟩ =
      vectorToComplexPoint (ℓ.mulVec v) ((not_congr (retained_projection_centre_vector ℓ v hv)).mp h) := by
  let eN := s2e_projectivePointHomeomorph N
  let eD := s2e_projectivePointHomeomorph d
  let L := ℓ.mulVecLin.toContinuousLinearMap
  have he : eN.symm (vectorToComplexPoint v hv) = Projectivization.mk ℂ v hv :=
    (congrArg eN.symm (projectivizationToComplexPoint_mk v hv)).symm.trans
      (eN.symm_apply_apply (Projectivization.mk ℂ v hv))
  change eD (retained_projective_projection L ⟨eN.symm (vectorToComplexPoint v hv), _⟩) = _
  simp only [he, retained_projective_projection_mk]
  exact projectivizationToComplexPoint_mk _ _

end HodgeLean.Foundations.QuotientDuality
