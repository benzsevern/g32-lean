import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicGlobalPurity

/-! # Actual supported extension across algebraic dimension-bounded boundaries -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An algebraic boundary dimension bound makes the literal supported restriction bijective, without an ambient smoothness premise.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, localization for nested supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_restrict_off_algebraic_boundary_bijective
    (Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom] [NoetherianSpace Y.left]
    [T2Space (ComplexPoint Y)] [∀ U : Opens (ComplexPoint Y), ParacompactSpace U]
    (S : Closeds (ComplexPoint Y)) (Z : Closeds Y.left)
    (hBS : properCycle_algebraic_analytic_support Y Z ≤ S)
    (d : ℕ) (hdim : topologicalKrullDim Z ≤ d)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : ComplexPoint Y,
      Subsingleton (orientationGroup (TopCat.of (ComplexPoint Y)) j x))
    (n : ℕ) (hbound : (n + 1) + (2 * d + 1) ≤ N) :
    Function.Bijective (relativeCohomologyMap ℚ n
      (a3b4_neighborhoodPairMap ((properCycle_algebraic_analytic_support Y Z).compl : Set (ComplexPoint Y))
        (S : Set (ComplexPoint Y)))) := by
  let X := TopCat.of (ComplexPoint Y)
  let B := properCycle_algebraic_analytic_support Y Z
  let r := relativeCohomologyMap ℚ n
    (neighborhoodSupportInclusionPairMap
      (show (B.compl : Set X) ⊆ Set.univ from Set.subset_univ _) (S : Set X))
  have hr : Function.Bijective r := by
    apply a3b4a_classRelative_restriction_bijective_of_boundary_vanishing X S B hBS n
    intro j hj
    have hjbound : j ≤ n + 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> omega
    exact properCycle_algebraic_support_relative_vanishes Y Z d hdim N hvan j (by omega) ⊤
  let p : TopPair.ofSubset (X := X) (S : Set X)ᶜ ≅
      neighborhoodSupportComplementPair (Set.univ : Set X) (S : Set X) :=
    TopPair.isoOfSubset (Homeomorph.Set.univ X).symm (fun _ => Iff.rfl)
  let H := (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso p.symm))
  have hp : Function.Bijective (relativeCohomologyMap ℚ n p.inv) := H.toLinearEquiv.bijective
  have hcomp : r.comp (relativeCohomologyMap ℚ n p.inv) =
      relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap (B.compl : Set X) (S : Set X)) := by
    dsimp only [r]
    rw [← relativeCohomologyMap_comp]
    rfl
  rw [← hcomp]
  exact hr.comp hp


end HodgeLean.Foundations.QuotientDuality
