import HodgeLean.Foundations.Program.SchoenTransferC1a5SingularCoproductHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeDefs
import HodgeLean.Foundations.Program.SchoenTransferC1a5CoproductHelpers
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! Unit transport for the cell coproduct chain models.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Integral simplicial chains preserve coproducts degree by degree.
Source: Mathlib sigmaConst and HomologicalComplex.preservesColimitsOfShape_of_eval. -/
instance c1a5_chains_preserves_coproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I) c1a5Chains := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape (Discrete I)
    ((evaluation _ _).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj (ModuleCat.of ℤ ℤ))
  infer_instance

/-- Realized singular integral chains preserve coproducts through their actual functor factors.
Source: Mathlib sSetTopAdj, singular coproduct transport and sigmaConst. -/
instance c1a5_singularChains_preserves_coproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I) c1a5SingularChains := by
  dsimp only [c1a5SingularChains]
  infer_instance

/-- The actual unit comparison on a finite coproduct follows from its summand comparisons.
Source: Hatcher §2.1, disjoint unions; Mathlib sigmaComparison and unit naturality. -/
lemma c1a5_unit_finite_coproduct {I : Type} [Finite I] (K : I → SSet.{0})
    (hK : ∀ i, QuasiIso (c1a5Unit (K i))) : QuasiIso (c1a5Unit (∐ K)) := by
  have w : sigmaComparison c1a5Chains K ≫ c1a5Unit (∐ K) =
      CategoryTheory.Limits.Sigma.map (fun i ↦ c1a5Unit (K i)) ≫
        sigmaComparison c1a5SingularChains K := by
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    simp only [ι_comp_sigmaComparison_assoc, CategoryTheory.Limits.Sigma.ι_map_assoc,
      Category.assoc]
    exact (c1a5Unit_naturality (CategoryTheory.Limits.Sigma.ι K i)).trans
      (congrArg (fun t ↦ c1a5Unit (K i) ≫ t)
        (ι_comp_sigmaComparison c1a5SingularChains K i).symm)
  have hsum := c1a5_finite_coproduct_comparison (fun i ↦ c1a5Unit (K i)) hK
  have hcomp : QuasiIso (sigmaComparison c1a5Chains K ≫ c1a5Unit (∐ K)) := by
    rw [w]
    infer_instance
  exact (quasiIso_iff_comp_left (sigmaComparison c1a5Chains K) (c1a5Unit (∐ K))).1 hcomp

end HodgeLean.Foundations.Program
