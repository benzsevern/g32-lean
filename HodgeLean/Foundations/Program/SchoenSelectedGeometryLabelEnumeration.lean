import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Equality of all label sums gives an enumeration preserving each individual label. -/
theorem s0_label_enumeration {A B : Type} [Fintype A] [Zero B]
    (v : A → B) (l : List B) (hv : ∀ a, v a ≠ 0) (hl : ∀ b ∈ l, b ≠ 0)
    (hs : ∀ w : B → ℝ, w 0 = 0 → ∑ a, w (v a) = (l.map w).sum) :
    ∃ e : Fin l.length ≃ A, ∀ i, v (e i) = l[i] := by
  classical
  have hc (b : B) : Fintype.card {i : Fin l.length // l[i] = b} =
      Fintype.card {a : A // v a = b} := by
    by_cases hb : b = 0
    · subst b
      haveI : IsEmpty {a : A // v a = 0} := ⟨fun a ↦ hv a a.property⟩
      haveI : IsEmpty {i : Fin l.length // l[i] = 0} :=
        ⟨fun i ↦ hl _ (List.getElem_mem i.val.isLt) i.property⟩
      simp
    · have hh := hs (fun c ↦ if c = b then 1 else 0) (by simp [Ne.symm hb])
      have he : (l.map (fun c ↦ if c = b then (1 : ℝ) else 0)).sum =
          ∑ i : Fin l.length, if l[i] = b then (1 : ℝ) else 0 := by
        rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
        rfl
      rw [he] at hh
      have hh' : (Fintype.card {a : A // v a = b} : ℝ) =
          (Fintype.card {i : Fin l.length // l[i] = b} : ℝ) := by
        simpa [Fintype.card_subtype, Finset.sum_ite] using hh
      exact_mod_cast hh'.symm
  let e : ∀ b, {i : Fin l.length // l[i] = b} ≃ {a : A // v a = b} :=
    fun b ↦ Classical.choice (Fintype.card_eq.mp (hc b))
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

#print axioms s0_label_enumeration
end HodgeLean.Foundations.Program
