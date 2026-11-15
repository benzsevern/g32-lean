import HodgeLean.Foundations.Program.CompensationAssemblyPrismSimplex

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology MonoidalCategory
open scoped Simplicial
namespace HodgeLean.Foundations.Program

def cq_circlePrismSimplex (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 1))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of (X × UnitAddCircle))) _⦋n + 1⦌ :=
  (cq_circleLoopHomotopy X).toSSet.toSimplicialObjectHomotopy.h k x

theorem cq_circleLoopSimplicial_fst (X : TopCat.{0}) :
    (cq_circleLoopHomotopy X).toSSet.h ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
          TopCat.of (X × UnitAddCircle) ⟶ X) =
      CartesianMonoidalCategory.fst (TopCat.toSSet.obj X) Δ[1] := by
  have hh : (cq_circleLoopHomotopy X).h ≫
      (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ : TopCat.of (X × UnitAddCircle) ⟶ X) =
      CartesianMonoidalCategory.fst X TopCat.I := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  dsimp only [TopCat.Homotopy.toSSet]
  rw [Category.assoc, Category.assoc, ← TopCat.toSSet.map_comp, hh,
    Functor.Monoidal.μ_fst]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrismSimplex_fst (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 1))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ X)).app _ (cq_circlePrismSimplex X n k x) =
      (TopCat.toSSet.obj X).σ k x := by
  have h := ConcreteCategory.congr_hom
    (congr_app (cq_circleLoopSimplicial_fst X) (Opposite.op ⦋n + 1⦌))
    (((SSet.yonedaEquiv.symm x) ▷ Δ[1]).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv k).1)
  change (TopCat.toSSet.map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
      TopCat.of (X × UnitAddCircle) ⟶ X)).app _ (cq_circlePrismSimplex X n k x) =
    (SSet.yonedaEquiv.symm x).app _ (SSet.prodStdSimplex₁.nonDegenerateEquiv k).1.1 at h
  apply h.trans
  rw [SSet.prodStdSimplex₁.nonDegenerateEquiv_fst,
    SSet.yonedaEquiv_symm_app_objEquiv_symm]
  rfl

end HodgeLean.Foundations.Program
