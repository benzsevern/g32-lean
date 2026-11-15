import HodgeLean.Foundations.Program.SchoenTowerT11bConstant
import Mathlib.Data.Fintype.EquivFin

/-! Explicit base pieces for maps with finite image.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A single polynomial describes a finite list of real values.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite point sets. -/
def s2v_t11b_valuesFormula {k : ℕ} (d : Fin k → ℝ) : s2v_t11b_Formula 1 :=
  s2v_t11b_zeroFormula (∏ i, (MvPolynomial.X 0 - MvPolynomial.C (d i)))

/-- The roots of the product are exactly the listed values.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite point sets. -/
theorem s2v_t11b_realize_valuesFormula {k : ℕ} (d : Fin k → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (s2v_t11b_valuesFormula d).realize ↔
      ∃ i, t = d i := by
  simp only [s2v_t11b_valuesFormula, s2v_t11b_realize_zeroFormula, map_prod,
    map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]

/-- Point-cell coordinates preserve the value of the original map.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, point-cell case. -/
theorem s2v_t11b_pointBaseChart_projection {X : Type*} [TopologicalSpace X]
    (S : Set X) (p : X → ℝ) (d : ℝ)
    (y : {y : X | y ∈ S ∧ WithLp.toLp 2 (fun _ : Fin 1 => p y) ∈
      (s2v_t11b_pointFormula d).realize}) :
    (s2v_t11b_pointBaseChart S p d y).2.val = p y.val := by
  exact ((s2v_t11b_realize_pointFormula d (p y.val)).mp y.property.2).symm

/-- Maps taking finitely many values have explicit point pieces and an empty-image piece.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, finite-image case. -/
theorem s2v_t11b_finite_values_triviality {X : Type*} [TopologicalSpace X]
    (S : Set X) (p : X → ℝ) {k : ℕ} (d : Fin k → ℝ)
    (hd : ∀ y ∈ S, ∃ i, p y = d i) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃ i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        {y : X | y ∈ S ∧ WithLp.toLp 2 (fun _ : Fin 1 => p y) ∈ (c i).realize} ≃ₜ
        ({y : X | y ∈ S ∧ p y = b i} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}),
        ∀ y, (e y).2.val = p y.val := by
  classical
  obtain ⟨a, ha⟩ := (Set.finite_range d).exists_notMem
  let C : Option (Fin k) → s2v_t11b_Formula 1
    | none => .compl (s2v_t11b_valuesFormula d)
    | some i => s2v_t11b_pointFormula (d i)
  let B : Option (Fin k) → ℝ
    | none => a
    | some i => d i
  let E := (Fintype.equivFin (Option (Fin k))).symm
  refine ⟨Fintype.card (Option (Fin k)), C ∘ E, B ∘ E, ?_, ?_⟩
  · intro t
    by_cases ht : ∃ j, t = d j
    · obtain ⟨j, hj⟩ := ht
      refine ⟨E.symm (some j), ?_⟩
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, C,
        s2v_t11b_realize_pointFormula] using hj
    · refine ⟨E.symm none, ?_⟩
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, C,
        s2v_t11b_Formula.realize, Set.mem_compl_iff, s2v_t11b_realize_valuesFormula] using ht
  · intro i
    change ∃ e :
      {y : X | y ∈ S ∧ WithLp.toLp 2 (fun _ : Fin 1 => p y) ∈ (C (E i)).realize} ≃ₜ
        ({y : X | y ∈ S ∧ p y = B (E i)} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (C (E i)).realize}),
      ∀ y, (e y).2.val = p y.val
    generalize E i = j
    cases j with
    | some j =>
      exact ⟨s2v_t11b_pointBaseChart S p (d j),
        s2v_t11b_pointBaseChart_projection S p (d j)⟩
    | none =>
      letI : IsEmpty {y : X | y ∈ S ∧ WithLp.toLp 2 (fun _ : Fin 1 => p y) ∈
          (C none).realize} := ⟨fun y =>
        ((s2v_t11b_realize_valuesFormula d (p y.val)).not.mp y.property.2)
          (hd y.val y.property.1)⟩
      letI : IsEmpty {y : X | y ∈ S ∧ p y = B none} := ⟨fun y => by
        obtain ⟨j, hj⟩ := hd y.val y.property.1
        exact ha ⟨j, hj.symm.trans y.property.2⟩⟩
      exact ⟨Homeomorph.empty, fun y => isEmptyElim y⟩

end HodgeLean.Foundations.Program
