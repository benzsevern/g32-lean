import HodgeLean.Foundations.Program.CompensationAssemblyPrismCircleFace
import HodgeLean.Foundations.Program.CompensationAssemblyLoopNormalization

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology
open HodgeLean.Adapters
open scoped Simplicial
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_circleIntervalSimplexMap_id :
    cq_circleIntervalSimplexMap.app (Opposite.op ⦋1⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
      loopSimplex (ContinuousMap.id UnitAddCircle) := by
  apply ((TopCat.of UnitAddCircle).toSSetObjEquiv _).injective
  ext t
  simp only [cq_circleIntervalSimplexMap, NatTrans.comp_app, ConcreteCategory.comp_apply,
    SSet.stdSimplex.toSSetObjI, Adjunction.homEquiv_unit]
  change (((SSet.stdSimplex.toTopObjIsoI.hom
      ((((sSetTopAdj.unit.app (Δ[1] : SSet.{0})).app (Opposite.op ⦋1⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))).down :
          SimplexCategory.toTop.obj ⦋1⦌ ⟶ SSet.toTop.obj (Δ[1] : SSet.{0})).hom (ULift.up t))).down : ℝ) :
      UnitAddCircle) = ((Convexity.StdSimplex.homeomorphI t : ℝ) : UnitAddCircle)
  rw [sSetTopAdj_unit_app_app_down]
  simp [SSet.yonedaEquiv_symm_stdSimplex_id, SSet.stdSimplex.toTopObjIsoI,
    SimplexCategory.toTopHomeo, TopCat.stdSimplexHomeomorphI]
  exact congrArg (fun z : ULift (Convexity.StdSimplex ℝ (Fin 2)) =>
    ((Convexity.StdSimplex.homeomorphI z.down : ℝ) : UnitAddCircle))
    ((SSet.toTopSimplex.app ⦋1⦌).inv_hom_id_apply (ULift.up t))

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_backFace_last (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)).app _
        (AlgebraicTopology.Simplicial.backFace (p := n) (q := 1)
          (TopCat.toSSet.obj (TopCat.of (X × UnitAddCircle)))
          (cq_circlePrismSimplex X n (Fin.last n) x)) =
      loopSimplex (ContinuousMap.id UnitAddCircle) := by
  rw [← AlgebraicTopology.Simplicial.backFace_naturality, cq_circlePrismSimplex_snd,
    AlgebraicTopology.Simplicial.backFace_naturality, cq_backFace_interval_last,
    cq_circleIntervalSimplexMap_id]

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_backFace_nonfinal (X : TopCat.{0}) (n : ℕ)
    (k : Fin (n + 1)) (hk : k ≠ Fin.last n) (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)).app _
        (AlgebraicTopology.Simplicial.backFace (p := n) (q := 1)
          (TopCat.toSSet.obj (TopCat.of (X × UnitAddCircle)))
          (cq_circlePrismSimplex X n k x)) ∈
      (TopCat.toSSet.obj (TopCat.of UnitAddCircle)).degenerate 1 := by
  rw [← AlgebraicTopology.Simplicial.backFace_naturality, cq_circlePrismSimplex_snd,
    AlgebraicTopology.Simplicial.backFace_naturality, cq_backFace_interval_nonfinal n k hk]
  change cq_circleIntervalSimplexMap.app _
    (Δ[1].map (SimplexCategory.σ (0 : Fin 1)).op (SSet.stdSimplex.objMk₁ (0 : Fin 2))) ∈ _
  rw [NatTrans.naturality_apply]
  exact (TopCat.toSSet.obj (TopCat.of UnitAddCircle)).σ_mem_degenerate 0 _

end HodgeLean.Foundations.Program
