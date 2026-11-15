import HodgeLean.Foundations.Program.CompensationAssemblyPrismFaces

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Simplicial
open scoped Simplicial
namespace HodgeLean.Foundations.Program

theorem cq_frontInclusion_one (n : ℕ) :
    frontInclusion n 1 = SimplexCategory.δ (Fin.last (n + 1)) := by
  ext i
  simp [frontInclusion, SimplexCategory.δ]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem cq_frontFace_sigma_castSucc (X : SSet.{0}) (n : ℕ) (k : Fin (n + 1))
    (x : X _⦋n + 1⦌) :
    frontFace (p := n + 1) (q := 1) X (X.σ k.castSucc x) =
      X.σ k (frontFace (p := n) (q := 1) X x) := by
  have h := ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_σ_of_gt X
      (i := Fin.last (n + 1)) (j := k) (by simp)) x
  simpa only [frontFace, cq_frontInclusion_one,
    ← SimplicialObject.δ_def, Fin.succ_last, ConcreteCategory.comp_apply] using h

set_option backward.isDefEq.respectTransparency false in
theorem cq_frontFace_sigma_last (X : SSet.{0}) (n : ℕ) (x : X _⦋n⦌) :
    frontFace (p := n) (q := 1) X (X.σ (Fin.last n) x) = x := by
  have h := ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_σ_succ X (i := Fin.last n)) x
  simpa only [frontFace, cq_frontInclusion_one,
    ← SimplicialObject.δ_def, Fin.succ_last, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] using h

set_option backward.isDefEq.respectTransparency false in
theorem cq_frontFace_sigma_degenerate (X : SSet.{0}) (n : ℕ) (k : Fin (n + 1))
    (hk : k ≠ Fin.last n) (x : X _⦋n⦌) :
    frontFace (p := n) (q := 1) X (X.σ k x) ∈ X.degenerate n := by
  cases n with
  | zero => exact False.elim (hk (Fin.ext (by have := k.isLt; simp only [Fin.val_last]; omega)))
  | succ n =>
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      rw [cq_frontFace_sigma_castSucc]
      exact X.σ_mem_degenerate j _

end HodgeLean.Foundations.Program
