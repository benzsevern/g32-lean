import HodgeLean.Foundations.Program.G32Native.BlowupLocalFreeness
import HodgeLean.Foundations.Program.G32Native.PairedBranchFamily

/-! # Iteration of global blowups with retained branch ideals
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A base and its indexed branch ideals. -/
abbrev g32t5_BranchStage (S : Scheme) (r : ℕ) :=
  Σ B : Over S, Fin (2 * r) → B.left.IdealSheafData

/-- Blow up the selected pair and retain every strict-transform ideal. -/
def g32t5_nextStage {S : Scheme} {r : ℕ} (i : Fin r)
    (A : g32t5_BranchStage S r) : g32t5_BranchStage S r :=
  let K := A.2 ⟨2 * i.val, by omega⟩ ⊔ A.2 ⟨2 * i.val + 1, by omega⟩
  ⟨Over.mk (K.blowUpπ ≫ A.1.hom), fun t => s2c_strictTransform K.blowUpπ (A.2 t) K⟩

/-- The blowdown, transported along an equality of retained stages. -/
def g32t5_stageTransition {S : Scheme} {r : ℕ} (i : Fin r)
    (A C : g32t5_BranchStage S r) (h : C = g32t5_nextStage i A) : C.1 ⟶ A.1 :=
  eqToHom (congrArg Sigma.fst h) ≫
    Over.homMk (A.2 ⟨2 * i.val, by omega⟩ ⊔ A.2 ⟨2 * i.val + 1, by omega⟩).blowUpπ

/-- The transported step has the literal branch equation and both native blowup properties. -/
theorem g32t5_stageTransition_spec {S : Scheme} {r : ℕ} (i : Fin r)
    (A C : g32t5_BranchStage S r) (h : C = g32t5_nextStage i A) :
    let b := g32t5_stageTransition i A C h
    let K := A.2 ⟨2 * i.val, by omega⟩ ⊔ A.2 ⟨2 * i.val + 1, by omega⟩
    (∀ t, C.2 t = s2c_strictTransform b.left (A.2 t) K) ∧
    (∀ x : C.1.left, ∃ U : C.1.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(C.1.left, U)] Γ(C.1.left, U))) ∧
    (∀ (T : Over S) (f : T ⟶ A.1),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ C.1, u ≫ b = f) := by
  subst C
  dsimp only [g32t5_stageTransition, g32t5_nextStage, eqToHom_refl, Category.id_comp]
  exact ⟨fun _ => rfl, g32t5_blowup_over A.1 _⟩

/-- The retained sequence of bases and branches. -/
def g32t5_stages {S : Scheme} {r : ℕ} (A : g32t5_BranchStage S r) :
    Fin (r + 1) → g32t5_BranchStage S r :=
  Fin.induction A (fun i B => g32t5_nextStage i B)

/-- Successor stages use the selected pair in its original order. -/
theorem g32t5_stages_succ {S : Scheme} {r : ℕ} (A : g32t5_BranchStage S r) (i : Fin r) :
    g32t5_stages A i.succ = g32t5_nextStage i (g32t5_stages A i.castSucc) := by
  unfold g32t5_stages
  rw [Fin.induction_succ]

end HodgeLean.Foundations.Program
