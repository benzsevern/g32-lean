import HodgeLean.Foundations.Program.SchoenTowerI1aProjectiveFinite
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Common affine charts for finite projective point sets
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- A finite set in a projective spectrum lies in one affine principal chart.
Source: Hartshorne, Algebraic Geometry, II.2, Proj and principal affine charts. -/
theorem s2v_i1alo_proj_finite_affine
    (A σ : Type) [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : Finset (Proj 𝒜)) :
    ∃ U : (Proj 𝒜).Opens, IsAffineOpen U ∧ ∀ p ∈ s, p ∈ U := by
  obtain ⟨d, hd, f, hf, havoid⟩ := s2v_i1alo_projective_finite_homogeneous A σ 𝒜 s
  exact ⟨Proj.basicOpen 𝒜 f, Proj.isAffineOpen_basicOpen 𝒜 f hf hd, havoid⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite set in complex projective space lies in one affine chart from the integral model.
Source: Hartshorne, Algebraic Geometry, II.2, Proj charts and affine base change. -/
theorem s2v_i1alo_projectiveSpace_finite_affine
    (n : ℕ) (s : Finset (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ))) :
    ∃ U : (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).Opens,
      IsAffineOpen U ∧ ∀ p ∈ s, p ∈ U := by
  classical
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift ℤ)
  let π : ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) ⟶ Proj 𝒜 :=
    Limits.pullback.snd _ _
  haveI : IsAffineHom (Limits.terminal.from (Spec ↧ℂ)) := by infer_instance
  haveI : IsAffineHom π := by
    dsimp [π]
    exact MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨A, hA, hsA⟩ := s2v_i1alo_proj_finite_affine
    (MvPolynomial (Fin (n + 1)) (ULift ℤ)) _ 𝒜 (s.image π)
  refine ⟨π ⁻¹ᵁ A, hA.preimage π, ?_⟩
  intro p hp
  exact hsA _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

end HodgeLean.Foundations.Program
