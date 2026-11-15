import HodgeLean.Foundations.Program.G32Native.EulerModel.LocalOrientationCoclass
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalRealCoordinates

/-! # The actual ordered composition of real coordinate-pair exchanges -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- One actual adjacent exchange affects exactly its own coordinate pair. -/
theorem orientationPairSwap_index (k : ℕ) (a j : Fin k) (r : Fin 2) :
    Equiv.swap (⟨2 * a.val, by omega⟩ : Fin (k * 2)) ⟨2 * a.val + 1, by omega⟩
        (finProdFinEquiv (j, r)) =
      finProdFinEquiv (j, if j = a then Equiv.swap (0 : Fin 2) 1 r else r) := by
  apply Fin.ext
  fin_cases r <;> simp only [Equiv.swap_apply_def]
  all_goals split_ifs <;> simp_all [finProdFinEquiv, Fin.ext_iff] <;> omega

#print axioms orientationPairSwap_index

/-- A list of distinct specified pair exchanges changes exactly the pairs on that list. -/
theorem orientationIndexedSwapList_apply (k : ℕ) (l : List (Fin k)) (hl : l.Nodup)
    (x : Fin (k * 2) → ℝ) (j : Fin k) (r : Fin 2) :
    (TopPair.Hom.fst (orientationSwapListMap (k * 2)
      (l.map (fun a => (⟨2 * a.val, by have := a.isLt; omega⟩ : {i : ℕ // i + 1 < k * 2})))))
        x (finProdFinEquiv (j, r)) =
      x (finProdFinEquiv (j, if j ∈ l then Equiv.swap (0 : Fin 2) 1 r else r)) := by
  induction l generalizing x with
  | nil =>
    change x (finProdFinEquiv (j, r)) = _
    simp
  | cons a l ih =>
    have hn := List.nodup_cons.mp hl
    change (TopPair.Hom.fst (orientationSwapListMap (k * 2)
      (l.map (fun a => (⟨2 * a.val, by have := a.isLt; omega⟩ : {i : ℕ // i + 1 < k * 2})))))
      ((orientationAdjacentSwapMap (k * 2) (2 * a.val) (by have := a.isLt; omega)) x)
      (finProdFinEquiv (j, r)) = _
    rw [ih hn.2]
    change x (Equiv.swap (⟨2 * a.val, by omega⟩ : Fin (k * 2)) ⟨2 * a.val + 1, by omega⟩
      (finProdFinEquiv (j, if j ∈ l then Equiv.swap (0 : Fin 2) 1 r else r))) = _
    rw [orientationPairSwap_index]
    by_cases hj : j = a
    · subst j
      simp [hn.1]
    · simp [hj]

#print axioms orientationIndexedSwapList_apply

/-- The specified full exchange list swaps both real coordinates in every pair exactly once. -/
theorem orientationPairedSwaps_apply (k : ℕ) (x : Fin (k * 2) → ℝ)
    (j : Fin k) (r : Fin 2) :
    (TopPair.Hom.fst (orientationSwapListMap (k * 2) (orientationPairedSwapList k))) x
        (finProdFinEquiv (j, r)) =
      x (finProdFinEquiv (j, Equiv.swap (0 : Fin 2) 1 r)) := by
  have h := orientationIndexedSwapList_apply k (List.ofFn (fun j : Fin k => j))
    (List.nodup_ofFn.mpr Function.injective_id) x j r
  have hm : j ∈ List.ofFn (fun j : Fin k => j) := by simp
  simpa [orientationPairedSwapList, hm, Function.comp_def] using h

#print axioms orientationPairedSwaps_apply

/-- The actual real exchange composition is rotated normal conjugation in the specified real coordinates. -/
theorem orientationPairedSwaps_realCoordinates (k : ℕ) (z : Fin k → ℂ) :
    (TopPair.Hom.fst (orientationSwapListMap (k * 2) (orientationPairedSwapList k)))
        (Complex.piCoordCLE k z) =
      Complex.piCoordCLE k (fun j => Complex.I * normalConjugation k z j) := by
  funext b
  rcases finProdFinEquiv.surjective b with ⟨⟨j, r⟩, rfl⟩
  rw [orientationPairedSwaps_apply, normalRealCoordinates_rotated_conjugation]

#print axioms orientationPairedSwaps_realCoordinates
end HodgeLean.Foundations.Program.G32Native.EulerModel
