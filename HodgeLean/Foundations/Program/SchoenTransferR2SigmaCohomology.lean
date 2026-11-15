import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import HodgeLean.Foundations.Program.SchoenTransferC1a5SingularCoproductHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
import Mathlib.Algebra.Homology.Additive

/-! # Detection of rational cohomology on finite disjoint unions

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- A rational cohomology class on a finite topological disjoint union is zero
when its restriction to every actual summand is zero.
Source: Hatcher, Algebraic Topology, §3.1; coproduct chains and universal coefficients.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_sigma_cohomology_eq_zero
    {A : Type} [Finite A] (Q : A → TopCat.{0}) (n : ℕ)
    (u : Cohomology ℚ (TopCat.of (Σ a, Q a)) n)
    (hu : ∀ a, cohomologyMap ℚ n (TopCat.sigmaι Q a) u = 0) : u = 0 := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)) ⋙ HomologicalComplex.homologyFunctor
      (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n
  let C := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)
  let Hn := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n
  haveI : PreservesColimitsOfShape (Discrete A)
      ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro i
    change PreservesColimitsOfShape (Discrete A)
      ((evaluation _ _).obj (Opposite.op ⦋i⦌) ⋙ sigmaConst.obj (ModuleCat.of ℚ ℚ))
    infer_instance
  haveI : PreservesColimitsOfShape (Discrete A) C := by
    change PreservesColimitsOfShape (Discrete A)
      (TopCat.toSSet ⋙ (SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ))
    infer_instance
  haveI : PreservesColimitsOfShape (Discrete A) Hn := inferInstance
  haveI : PreservesColimit (Discrete.functor Q) F := by
    change PreservesColimit (Discrete.functor Q) (C ⋙ Hn)
    infer_instance
  have hc : IsColimit (F.mapCocone (TopCat.sigmaCofan Q)) :=
    isColimitOfPreserves F (TopCat.sigmaCofanIsColimit Q)
  have he : ModuleCat.ofHom (cohomologyEquivDualHomology ℚ _ n u) =
      (0 : F.obj (TopCat.of (Σ a, Q a)) ⟶ ModuleCat.of ℚ ℚ) := by
    apply hc.hom_ext
    intro a
    apply ModuleCat.hom_ext
    ext z
    change cohomologyEquivDualHomology ℚ _ n u
      (homologyMap ℚ n (TopCat.sigmaι Q a.as) z) = 0
    rw [← cohomologyEquivDualHomology_cohomologyMap, hu, map_zero]
    rfl
  apply (cohomologyEquivDualHomology ℚ _ n).injective
  rw [map_zero]
  exact congrArg ModuleCat.Hom.hom he

#print axioms s4_assembly_sigma_cohomology_eq_zero
end HodgeLean.Foundations.Program
