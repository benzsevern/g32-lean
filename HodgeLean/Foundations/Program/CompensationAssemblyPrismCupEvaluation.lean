import HodgeLean.Foundations.Program.CompensationAssemblyPrismEvaluation
import HodgeLean.Foundations.Program.CompensationAssemblyPrismCircleLoop

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations HodgeLean.Adapters
open scoped Simplicial
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_cup_simplex (X : TopCat.{0}) (n : ℕ)
    (a : Cochain ℚ (TopCat.toSSet.obj X) n)
    (c : Cocycle ℚ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    Singular.cupCochain (TopCat.of (X × UnitAddCircle)) n 1
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ X)) n a)
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)) 1
            (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1)
        ((cq_circleChainHomotopy X).hom n (n + 1) (chainOfSimplex ℚ x)) =
      -((-1 : ℤ) ^ n • (a (chainOfSimplex ℚ x) *
        (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1
          (chainOfSimplex ℚ (loopSimplex (ContinuousMap.id UnitAddCircle))))) := by
  have h := cq_simplicialPrism_cochain_simplex (cq_circleLoopHomotopy X).toSSet n x
    (Singular.cupCochain (TopCat.of (X × UnitAddCircle)) n 1
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ X)) n a)
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)) 1
            (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1))
  apply h.trans
  have hs (k : Fin (n + 1)) :
      (cq_circleLoopHomotopy X).toSSet.toSimplicialObjectHomotopy.h k x =
        cq_circlePrismSimplex X n k x := rfl
  simp only [hs]
  congr 1
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [Singular.cupCochain_apply_simplex, cochainMap_apply, cochainMap_apply,
      chainOfSimplex_map, chainOfSimplex_map]
    change (-1 : ℤ) ^ n • (_ * _) = _
    rw [← frontFace_naturality, cq_circlePrismSimplex_fst, cq_frontFace_sigma_last,
      cq_circlePrism_backFace_last]
  · intro k hk hne
    rw [Singular.cupCochain_apply_simplex, cochainMap_apply, cochainMap_apply,
      chainOfSimplex_map, chainOfSimplex_map]
    rw [cq_normalizedCocycle_degenerate (TopCat.of UnitAddCircle) 1 c _
      (cq_circlePrism_backFace_nonfinal X n k hne x), mul_zero, smul_zero]
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_cup_cochain (X : TopCat.{0}) (n : ℕ)
    (a : Cochain ℚ (TopCat.toSSet.obj X) n)
    (c : Cocycle ℚ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1) :
    (Singular.cupCochain (TopCat.of (X × UnitAddCircle)) n 1
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ X)) n a)
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)) 1
            (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1)).comp
        ((cq_circleChainHomotopy X).hom n (n + 1)).hom =
      -((-1 : ℤ) ^ n •
        ((cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1
          (chainOfSimplex ℚ (loopSimplex (ContinuousMap.id UnitAddCircle))) • a)) := by
  let p := (Singular.cupCochain (TopCat.of (X × UnitAddCircle)) n 1
    (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ X)) n a)
    (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)) 1
        (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1)).comp
      ((cq_circleChainHomotopy X).hom n (n + 1)).hom
  let q := -((-1 : ℤ) ^ n •
    ((cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1
      (chainOfSimplex ℚ (loopSimplex (ContinuousMap.id UnitAddCircle))) • a))
  have hcat : ModuleCat.ofHom p = ModuleCat.ofHom q := by
    apply SSet.chainComplex_hom_ext
    intro x
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    have hiota : (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x r =
        r • chainOfSimplex ℚ x := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change p ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x r) =
      q ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x r)
    rw [hiota, map_smul, map_smul]
    congr 1
    have h := cq_circlePrism_cup_simplex X n a c x
    change p (chainOfSimplex ℚ x) = _ at h
    exact h.trans (by
      simp only [q, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [mul_comm (a (chainOfSimplex ℚ x))])
  exact congrArg ModuleCat.Hom.hom hcat

end HodgeLean.Foundations.Program
