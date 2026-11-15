import HodgeLean.Foundations.Program.TorusAlgebraizationB54Immersion
import HodgeLean.Foundations.Program.SchoenTowerN2bGeometryHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite nonempty coordinate set embeds into a projective space with a natural-number dimension. -/
theorem n2b_finite_projective_index {κ : Type} [Fintype κ] [Nonempty κ]
    (S : Scheme.{0}) :
    ∃ (n : ℕ) (j : ProjectiveSpace κ S ⟶ ProjectiveSpace (Fin (n + 1)) S),
      IsClosedImmersion j ∧ j ≫ ProjectiveSpace.toBase (Fin (n + 1)) S =
        ProjectiveSpace.toBase κ S := by
  classical
  let n := Fintype.card κ
  let e := (Fintype.equivFin κ).symm
  let t : Fin (n + 1) → κ := Fin.cases (Classical.choice ‹Nonempty κ›) e
  have ht : Function.Surjective t := by
    intro k
    exact ⟨(Fintype.equivFin κ k).succ, e.apply_symm_apply k⟩
  let f : homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ) →+*ᵍ
      homogeneousSubmodule κ (ULift.{0} ℤ) :=
    { (rename t).toRingHom with
      map_mem := by
        intro m p hp
        rw [mem_homogeneousSubmodule] at hp ⊢
        exact hp.rename_isHomogeneous }
  have hf : Function.Surjective f := rename_surjective t ht
  let π := Proj.map f (b54_irrelevant_le_map_of_surjective f hf)
  haveI : IsClosedImmersion π := b54_proj_map_isClosedImmersion f _ hf
  let j : ProjectiveSpace κ S ⟶ ProjectiveSpace (Fin (n + 1)) S :=
    pullback.map _ _ _ _ (𝟙 S) π (𝟙 _) (by simp) (Subsingleton.elim _ _)
  haveI : IsClosedImmersion j := by
    dsimp only [j]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstanceAs (IsClosedImmersion (𝟙 S))) (inferInstanceAs (IsClosedImmersion π))
      (by simp) (Subsingleton.elim _ _)
  refine ⟨n, j, inferInstance, ?_⟩
  simp only [j, ProjectiveSpace.toBase, pullback.map, pullback.lift_fst, Category.comp_id]

end HodgeLean.Foundations.Program
