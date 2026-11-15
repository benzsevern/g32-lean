import HodgeLean.Foundations.Program.CompensationAssemblyPrismFaces
import HodgeLean.Foundations.Program.CompensationAssemblyCocycleNormalization

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations
open scoped Simplicial
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_normalized_pullback_simplex (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj X) (n + 1)) (k : Fin (n + 1))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ X)) (n + 1) (cq_normalizedCocycle X (n + 1) c).1
      (chainOfSimplex ℚ (cq_circlePrismSimplex X n k x)) = 0 := by
  rw [cochainMap_apply, chainOfSimplex_map, cq_circlePrismSimplex_fst]
  exact cq_normalizedCocycle_degenerate X (n + 1) c _
    ((TopCat.toSSet.obj X).σ_mem_degenerate k x)

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_normalized_pullback (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj X) (n + 1)) :
    (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ X)) (n + 1)
      (cq_normalizedCocycle X (n + 1) c).1).comp
      ((cq_circleChainHomotopy X).hom n (n + 1)).hom = 0 := by
  let p := cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
    TopCat.of (X × UnitAddCircle) ⟶ X)) (n + 1) (cq_normalizedCocycle X (n + 1) c).1
  let lhs := p.comp ((cq_circleChainHomotopy X).hom n (n + 1)).hom
  have hcat : ModuleCat.ofHom lhs = ModuleCat.ofHom (0 : Cochain ℚ (TopCat.toSSet.obj X) n) := by
    apply SSet.chainComplex_hom_ext
    intro x
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hiota : (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x a =
        a • chainOfSimplex ℚ x := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change lhs ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x a) = 0
    rw [hiota, map_smul]
    have hp : lhs (chainOfSimplex ℚ x) = 0 := by
      change p (((cq_circleLoopHomotopy X).toSSet.chainComplexMap (ModuleCat.of ℚ ℚ)).hom
        n (n + 1) (chainOfSimplex ℚ x)) = 0
      rw [cq_simplicialPrism_cochain_simplex]
      simp only [show ∀ k : Fin (n + 1), p (chainOfSimplex ℚ
          ((cq_circleLoopHomotopy X).toSSet.toSimplicialObjectHomotopy.h k x)) = 0 from
        fun k => cq_circlePrism_normalized_pullback_simplex X n c k x,
        smul_zero, Finset.sum_const_zero, neg_zero]
    rw [hp, smul_zero]
  exact congrArg ModuleCat.Hom.hom hcat

end HodgeLean.Foundations.Program
