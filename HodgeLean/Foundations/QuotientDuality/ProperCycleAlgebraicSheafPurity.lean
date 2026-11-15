import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicGlobalPurity

/-! # Actual supported sheaf purity for algebraic closed supports -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular Topology TopologicalSpace Opposite
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The constructed algebraic cofinal calculations annihilate the actual supported cohomology sheaf in the dimension range.
Source: Bredon, Sheaf Theory, second edition, I.6 and V.9, sheafification and stalk detection.
HC no distance; AV milestone no distance. -/
lemma properCycle_algebraic_support_sheaf_vanishes
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    [T1Space (ComplexPoint X)]
    (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : ComplexPoint X,
      Subsingleton (orientationGroup (TopCat.of (ComplexPoint X)) j x))
    (n : ℕ) (hbound : n + (2 * d + 1) ≤ N) :
    IsZero (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (properCycle_algebraic_analytic_support X S) n) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let A := properCycle_algebraic_analytic_support X S
  let P := supportRelativeCohomologyPresheaf (TopCat.of (ComplexPoint X)) A n
  have hP : IsZero (P.stalk x) := by
    apply TopCat.Presheaf.isZero_stalk_of_cofinal_sections
    intro U hxU
    obtain ⟨W, hWU, hxW, hzero⟩ :=
      properCycle_algebraic_support_cofinal_relative_vanishes X S d hdim N hvan n hbound x U hxU
    refine ⟨W, hWU, hxW, ?_⟩
    letI : Subsingleton (P.obj (op W)) := ModuleCat.subsingleton_of_isZero hzero
    exact AddCommGrpCat.isZero_of_subsingleton _
  let η := supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) A n
  letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  exact hP.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).symm

end HodgeLean.Foundations.QuotientDuality
