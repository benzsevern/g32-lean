import HodgeLean.Foundations.Program.CompensationAssemblyPrismCupFaces

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology MonoidalCategory
open scoped Simplicial
namespace HodgeLean.Foundations.Program

def cq_circleIntervalMap : TopCat.I.{0} ⟶ TopCat.of UnitAddCircle :=
  TopCat.ofHom ⟨fun t => ((t.down : ℝ) : UnitAddCircle), by fun_prop⟩

def cq_circleIntervalSimplexMap : Δ[1] ⟶ TopCat.toSSet.obj (TopCat.of UnitAddCircle) :=
  SSet.stdSimplex.toSSetObjI ≫ TopCat.toSSet.map cq_circleIntervalMap

theorem cq_circleLoopSimplicial_snd (X : TopCat.{0}) :
    (cq_circleLoopHomotopy X).toSSet.h ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle) =
      CartesianMonoidalCategory.snd (TopCat.toSSet.obj X) Δ[1] ≫
        cq_circleIntervalSimplexMap := by
  have hh : (cq_circleLoopHomotopy X).h ≫
      (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
        TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle) =
      CartesianMonoidalCategory.snd X TopCat.I ≫ cq_circleIntervalMap := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  dsimp only [TopCat.Homotopy.toSSet, cq_circleIntervalSimplexMap]
  rw [Category.assoc, Category.assoc, ← TopCat.toSSet.map_comp, hh,
    TopCat.toSSet.map_comp, ← Category.assoc (Functor.LaxMonoidal.μ _ _ _),
    Functor.Monoidal.μ_snd]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrismSimplex_snd (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 1))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)).app _
        (cq_circlePrismSimplex X n k x) =
      cq_circleIntervalSimplexMap.app _ (SSet.stdSimplex.objMk₁ k.succ.castSucc) := by
  have h := ConcreteCategory.congr_hom
    (congr_app (cq_circleLoopSimplicial_snd X) (Opposite.op ⦋n + 1⦌))
    (((SSet.yonedaEquiv.symm x) ▷ Δ[1]).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv k).1)
  change (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle)).app _
        (cq_circlePrismSimplex X n k x) =
    cq_circleIntervalSimplexMap.app _ (SSet.prodStdSimplex₁.nonDegenerateEquiv k).1.2 at h
  exact h.trans (congrArg (cq_circleIntervalSimplexMap.app _)
    (SSet.prodStdSimplex₁.nonDegenerateEquiv_snd k))

set_option backward.isDefEq.respectTransparency false in
theorem cq_backFace_interval_last (n : ℕ) :
    AlgebraicTopology.Simplicial.backFace (p := n) (q := 1) Δ[1]
        (SSet.stdSimplex.objMk₁ (Fin.last n).succ.castSucc) =
      SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) := by
  apply SSet.stdSimplex.objEquiv.injective
  ext j
  change ((if n + j.val < n + 1 then (0 : Fin 2) else 1) : Fin 2).val = j.val
  fin_cases j <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem cq_backFace_interval_nonfinal (n : ℕ) (k : Fin (n + 1))
    (hk : k ≠ Fin.last n) :
    AlgebraicTopology.Simplicial.backFace (p := n) (q := 1) Δ[1]
        (SSet.stdSimplex.objMk₁ k.succ.castSucc) =
      Δ[1].σ 0 (SSet.stdSimplex.objMk₁ (0 : Fin 2)) := by
  apply SSet.stdSimplex.objEquiv.injective
  ext j
  change ((if n + j.val < k.val + 1 then (0 : Fin 2) else 1) : Fin 2).val = 1
  have hklt : k.val < n := by
    have := k.isLt
    have hne : k.val ≠ n := fun h => hk (Fin.ext h)
    omega
  rw [if_neg (by omega)]
  rfl

end HodgeLean.Foundations.Program
