import HodgeLean.Foundations.Program.SchoenCycleBranchOffSupport

/-! # Disjoint actual marked supports for a single symmetric coordinate -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Distinct marks have disjoint actual insertion supports in the retained
one-coordinate quotient, on all scheme points. -/
theorem s2e_c1_single_coordinate_branch_supports_disjoint
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [LocallyOfFiniteType B.hom]
    (γ : g3_power Z (0 + 1) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (0 + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (0 + 1) ⟶ T),
      (∀ σ, s2_permute Z (0 + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (a b : ComplexPoint Z) (hab : a ≠ b) :
    Disjoint ((s2c_branchIdeal Z B 0 γ a).support : Set B.left)
      ((s2c_branchIdeal Z B 0 γ b).support : Set B.left) := by
  classical
  letI : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  letI : Surjective γ.left := s2e_step1_surjective_of_complexPoint_surjective _ _ γ hsurj
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints
    (show (((s2c_branchIdeal Z B 0 γ a).support : Set B.left) ∩
      (s2c_branchIdeal Z B 0 γ b).support).Nonempty from ⟨x, hxa, hxb⟩)
    (((s2c_branchIdeal Z B 0 γ a).support.isClosed.inter
      (s2c_branchIdeal Z B 0 γ b).support.isClosed).isLocallyClosed)
  let q : ComplexPoint B := Over.homMk (pointOfClosedPoint B.hom p hpc)
    (pointOfClosedPoint_comp B.hom p hpc)
  have hq : q.underlying = p := pointOfClosedPoint_apply B.hom p hpc _
  obtain ⟨v, hv⟩ := hsurj q
  have hvp : γ.left v.underlying = p := (congrArg Point.underlying hv).trans hq
  have hcoord (c : ComplexPoint Z) (hc : p ∈ (s2c_branchIdeal Z B 0 γ c).support) :
      Point.map (g3_proj Z (0 + 1) 0) v = c := by
    by_contra hn
    have hall : ∀ i : Fin (0 + 1), Point.map (g3_proj Z (0 + 1) i) v ≠ c := by
      intro i
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi]
      exact hn
    exact s2e_branch_support_excludes_unmarked_tuple Z B 0 γ hγ hquot v c hall (hvp.symm ▸ hc)
  exact hab ((hcoord a hp.1).symm.trans (hcoord b hp.2))

end HodgeLean.Foundations.Program
