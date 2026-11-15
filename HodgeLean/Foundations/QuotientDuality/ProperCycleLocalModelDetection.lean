import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicBoundaryRestriction
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicSheafPurity

/-! # Actual local supported models detected away from algebraic boundaries -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace Opposite
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Matching actual supported germs off a smaller algebraic boundary identifies local relative classes even at boundary points.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, support localization and stalk detection.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_eq_of_off_boundary_germs
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    [T2Space (ComplexPoint X)] [∀ W : Opens (ComplexPoint X), ParacompactSpace W]
    (S B : Closeds X.left) (hBS : B ≤ S)
    (d b : ℕ) (hdimS : topologicalKrullDim S ≤ d) (hdimB : topologicalKrullDim B ≤ b)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : ComplexPoint X,
      Subsingleton (orientationGroup (TopCat.of (ComplexPoint X)) j x))
    (n : ℕ) (hlow : n + 2 * d ≤ N) (hbound : (n + 1) + (2 * b + 1) ≤ N)
    (V : Opens (ComplexPoint X))
    (u v : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set (ComplexPoint X))
      (properCycle_algebraic_analytic_support X S)) n)
    (h : ∀ (x : ComplexPoint X) (hx : x ∈ V), x.underlying ∉ B →
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (properCycle_algebraic_analytic_support X S) n V x hx u =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (properCycle_algebraic_analytic_support X S) n V x hx v) : u = v := by
  let T := TopCat.of (ComplexPoint X)
  let A := properCycle_algebraic_analytic_support X S
  let C := properCycle_algebraic_analytic_support X B
  let U := V ⊓ C.compl
  have hCA : C ≤ A := fun _ hx => hBS hx
  have hH (j : ℕ) (hj : j < n) : IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj (supportRelativeCohomologySheaf T A j)) :=
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero
      (properCycle_algebraic_support_sheaf_vanishes X S d hdimS N hvan j (by omega))
  have hz : ∀ j ∈ ({n, n + 1} : Finset ℕ), IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (V : Set T) C) j) := by
    intro j hj
    have hjle : j ≤ n + 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> omega
    exact properCycle_algebraic_support_relative_vanishes X B b hdimB N hvan j (by omega) V
  letI (W : Opens V) : ParacompactSpace W := properCycle_open_paracompact_of_all_opens T V W
  apply sub_eq_zero.mp
  apply a3b4a_classRelative_eq_zero_of_boundary_restriction T A C hCA V n hz (u - v)
  apply ccm5_relativeGerms_injective_of_lowerVanishing T A U n hH
  funext x
  dsimp only
  rw [supportRelativeCohomologyGerm_restrict T A n (show U ≤ V from inf_le_left) x.val x.property]
  simp only [supportRelativeCohomologyGerm, map_sub, map_zero]
  exact sub_eq_zero.mpr (h x.val x.property.1 x.property.2)

end HodgeLean.Foundations.QuotientDuality
