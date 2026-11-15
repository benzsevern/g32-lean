import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.Homology.QuasiIso

/-! Continuous contractions for realized simplex augmentations.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- The standard topological simplex contracts to its first vertex.
Source: Hatcher, Algebraic Topology, §2.1, simplex contraction. -/
def c1a5_simplex_contraction (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (StdSimplex ℝ (Fin (n + 1))))
      (ContinuousMap.const _ (StdSimplex.single 0)) where
  toFun p := convexCombPair (R := ℝ) (unitInterval.symm p.1) p.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) p.2 (StdSimplex.single 0)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights _ _).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun i ↦ ?_)
    simp only [unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- A projection from a contractible space to a point is a chain homotopy equivalence.
Source: Hatcher, Algebraic Topology, §2.1, homotopy invariance. -/
def c1a5_contractible_projection_chainEquiv {X Y : TopCat.{0}}
    [ContractibleSpace X] [Subsingleton Y] (f : X ⟶ Y) :
    HomotopyEquiv ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))
      ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)) := by
  let x := Classical.choose (id_nullhomotopic X)
  let H := Classical.choice (Classical.choose_spec (id_nullhomotopic X))
  let g : Y ⟶ X := TopCat.const x
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  refine { hom := F.map f, inv := F.map g, homotopyHomInvId := ?_, homotopyInvHomId := ?_ }
  · have H' : TopCat.Homotopy (f ≫ g) (𝟙 X) := H.symm
    have h := H'.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
    change Homotopy (F.map (f ≫ g)) (F.map (𝟙 X)) at h
    rw [F.map_comp, F.map_id] at h
    exact h
  · apply Homotopy.ofEq
    rw [← F.map_comp]
    have hg : g ≫ f = 𝟙 Y := by ext y; exact Subsingleton.elim _ _
    rw [hg, F.map_id]
    rfl

/-- The realized-singular standard simplex augmentation preserves integral homology.
Source: Hatcher, Algebraic Topology, §2.1, homotopy invariance and simplex contraction. -/
lemma c1a5_singular_augmentation (n : ℕ) :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map
      (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0))))
      (ModuleCat.of ℤ ℤ)) := by
  have : ContractibleSpace (StdSimplex ℝ (Fin (n + 1))) :=
    (contractible_iff_id_nullhomotopic _).2 ⟨_, ⟨c1a5_simplex_contraction n⟩⟩
  have : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0})) :=
    (SimplexCategory.toTopHomeo ⦋n⦌).contractibleSpace
  exact (c1a5_contractible_projection_chainEquiv
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)))).quasiIso_hom

end HodgeLean.Foundations.Program
