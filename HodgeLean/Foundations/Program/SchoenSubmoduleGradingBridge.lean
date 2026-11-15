import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import HodgeLean.Foundations.Program.SchoenGradedInvariants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A submodule-valued grading supplies the same degree pieces as additive subgroups. -/
def s2_submoduleGradedPieces {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) (n : ℕ) : AddSubgroup A := (𝒜 n).toAddSubgroup

/-- A submodule-valued graded ring retains its actual decomposition when viewed
through additive-subgroup degree pieces. -/
def s2_submoduleGradingAsSubgroups {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] : GradedRing (s2_submoduleGradedPieces 𝒜) where
  toGradedMonoid :=
    { one_mem := SetLike.one_mem_graded 𝒜
      mul_mem i j a b ha hb := by
        change a * b ∈ 𝒜 (i + j)
        exact SetLike.mul_mem_graded (show a ∈ 𝒜 i from ha) (show b ∈ 𝒜 j from hb) }
  toDecomposition :=
    { decompose' := DirectSum.decompose 𝒜
      left_inv := DirectSum.Decomposition.left_inv (ℳ := 𝒜)
      right_inv := DirectSum.Decomposition.right_inv (ℳ := 𝒜) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Viewing submodule degree pieces as additive subgroups preserves the actual Proj scheme. -/
def s2_submoduleGradingProjIso {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] :
    letI := s2_submoduleGradingAsSubgroups 𝒜
    AlgebraicGeometry.Proj (s2_submoduleGradedPieces 𝒜) ≅ AlgebraicGeometry.Proj 𝒜 := by
  letI := s2_submoduleGradingAsSubgroups 𝒜
  let f : 𝒜 →+*ᵍ s2_submoduleGradedPieces 𝒜 :=
    { RingHom.id A with map_mem := fun {_} {_} ha => ha }
  let g : s2_submoduleGradedPieces 𝒜 →+*ᵍ 𝒜 :=
    { RingHom.id A with map_mem := fun {_} {_} ha => ha }
  have hf : HomogeneousIdeal.irrelevant (s2_submoduleGradedPieces 𝒜) ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f := by
    change (HomogeneousIdeal.irrelevant (s2_submoduleGradedPieces 𝒜)).toIdeal ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (RingHom.id A)
    rw [Ideal.map_id]
    intro a ha
    exact ha
  have hg : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant (s2_submoduleGradedPieces 𝒜)).map g := by
    change (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      (HomogeneousIdeal.irrelevant (s2_submoduleGradedPieces 𝒜)).toIdeal.map (RingHom.id A)
    rw [Ideal.map_id]
    intro a ha
    exact ha
  refine ⟨AlgebraicGeometry.Proj.map f hf, AlgebraicGeometry.Proj.map g hg, ?_, ?_⟩
  · rw [← AlgebraicGeometry.Proj.map_comp g f hg hf]
    change AlgebraicGeometry.Proj.map (.id (s2_submoduleGradedPieces 𝒜)) _ = _
    exact AlgebraicGeometry.Proj.map_id
  · rw [← AlgebraicGeometry.Proj.map_comp f g hf hg]
    change AlgebraicGeometry.Proj.map (.id 𝒜) _ = _
    exact AlgebraicGeometry.Proj.map_id

end HodgeLean.Foundations.Program
