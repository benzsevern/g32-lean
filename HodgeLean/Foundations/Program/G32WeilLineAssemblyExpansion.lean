import HodgeLean.Papers.PapersG32Certificates
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def g32c_vectorRow (i : Fin 51) : G32VectorRow :=
  g32VectorTable[i.val]'(by simpa only [g32VectorTable, List.length_cons, List.length_nil] using i.isLt)

theorem g32c_vectorRow_unique : ∀ (i : Fin 51) (v : G32VectorRow), v ∈ g32VectorTable →
    v.i = i.val + 1 → v = g32c_vectorRow i := by
  decide

theorem g32c_vectorRow_list : List.ofFn g32c_vectorRow = g32VectorTable := by
  decide

theorem g32c_printed_sum (a : Fin 51 → G32CharLattice)
    (ha : ∀ i, ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧ a i = g32SparseVec v.coords) :
    ∑ i, (g32c_vectorRow i).n • a i = (Pi.single (2 : Fin 44) 1, 0) := by
  have hv (i : Fin 51) : a i = g32SparseVec (g32c_vectorRow i).coords := by
    obtain ⟨v, hv, hi, he⟩ := ha i
    rw [g32c_vectorRow_unique i v hv hi] at he
    exact he
  simp_rw [hv]
  rw [← List.sum_ofFn]
  have he : (List.ofFn fun i => (g32c_vectorRow i).n •
      g32SparseVec (g32c_vectorRow i).coords) =
      g32VectorTable.map (fun v => v.n • g32SparseVec v.coords) := by
    rw [← g32c_vectorRow_list, List.map_ofFn]
    rfl
  rw [he]
  exact papers_g32_character_identity

theorem g32c_signed_expansion {M : Type*} [AddCommGroup M] {s : ℕ}
    (n : Fin s → ℤ) (a : Fin s → M) :
    ∃ (r : ℕ) (f : Fin r → Fin s) (ε : Fin r → ℤˣ),
      ∑ j, (ε j : ℤ) • a (f j) = ∑ i, n i • a i := by
  classical
  let T := Σ i : Fin s, Fin (n i).natAbs
  let e := Fintype.equivFin T
  let f : Fin (Fintype.card T) → Fin s := fun j => (e.symm j).1
  let sign : Fin s → ℤˣ := fun i => if n i < 0 then -1 else 1
  refine ⟨Fintype.card T, f, fun j => sign (f j), ?_⟩
  have he : ∑ j, ((sign (f j) : ℤˣ) : ℤ) • a (f j) =
      ∑ t : T, ((sign t.1 : ℤˣ) : ℤ) • a t.1 := by
    exact e.symm.sum_comp (fun t : T => ((sign t.1 : ℤˣ) : ℤ) • a t.1)
  rw [he, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  by_cases hn : n i < 0
  · simp only [sign, hn, ↓reduceIte, Units.val_neg, Units.val_one, neg_one_zsmul]
    rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_neg hn, neg_smul, smul_neg, neg_neg]
  · simp only [sign, hn, ↓reduceIte, Units.val_one, one_zsmul]
    rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt hn)]

end HodgeLean.Foundations.Program
