import HodgeLean.Foundations.Program.SchoenTowerT11bLineDecomposition
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

def s2v_cad1_gap {n : ℕ} (d : Fin n → ℝ) (i : Fin (n + 1)) : Set ℝ :=
  {t | ∀ k, (k.val < i.val → d k < t) ∧ (i.val ≤ k.val → t < d k)}

theorem s2v_cad1_gap_shape {n : ℕ} (d : Fin n → ℝ) (hd : StrictMono d)
    (i : Fin (n + 1)) :
    s2v_cad1_gap d i = Set.univ ∨
    (∃ a, s2v_cad1_gap d i = Set.Iio a) ∨
    (∃ a, s2v_cad1_gap d i = Set.Ioi a) ∨
    (∃ a b, a < b ∧ s2v_cad1_gap d i = Set.Ioo a b) := by
  by_cases hn : n = 0
  · subst n
    exact Or.inl (by ext t; simp [s2v_cad1_gap])
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  by_cases h0 : i.val = 0
  · right; left
    refine ⟨d ⟨0, hn'⟩, ?_⟩
    ext t
    constructor
    · intro h
      exact (h ⟨0, hn'⟩).2 (by omega)
    · intro h k
      constructor
      · omega
      · intro _
        exact lt_of_lt_of_le h (hd.monotone (by change 0 ≤ k.val; omega))
  by_cases hn : i.val = n
  · right; right; left
    refine ⟨d ⟨n - 1, by omega⟩, ?_⟩
    ext t
    constructor
    · intro h
      exact (h ⟨n - 1, by omega⟩).1 (by omega)
    · intro h k
      constructor
      · intro _
        exact lt_of_le_of_lt (hd.monotone (by change k.val ≤ n - 1; omega)) h
      · omega
  · right; right; right
    let l : Fin n := ⟨i.val - 1, by omega⟩
    let u : Fin n := ⟨i.val, by omega⟩
    refine ⟨d l, d u, hd (by change i.val - 1 < i.val; omega), ?_⟩
    ext t
    constructor
    · intro h
      exact ⟨(h l).1 (by dsimp [l]; omega), (h u).2 (by rfl)⟩
    · rintro ⟨hl, hu⟩ k
      constructor
      · intro hk
        exact lt_of_le_of_lt (hd.monotone (by change k.val ≤ i.val - 1; omega)) hl
      · intro hk
        exact lt_of_lt_of_le hu (hd.monotone hk)

def s2v_cad1_coord : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).trans (Homeomorph.funUnique _ _)

theorem s2v_cad1_gap_geometry {n : ℕ} (d : Fin n → ℝ) (hd : StrictMono d)
    (i : Fin (n + 1)) :
    (s2v_cad1_gap d i).Nonempty ∧ IsOpen (s2v_cad1_gap d i) ∧
    (s2v_cad1_gap d i).OrdConnected ∧
    Nonempty (s2v_cad1_gap d i ≃ₜ Set.Ioo (-1 : ℝ) 1) := by
  let u := (orderIsoIooNegOneOne ℝ).toHomeomorph
  have ray (a : ℝ) : Nonempty (Set.Ioi a ≃ₜ Set.Ioo (-1 : ℝ) 1) := by
    let e := affineHomeomorph (1 : ℝ) a one_ne_zero
    have h : ∀ x : ℝ, x ∈ Set.Ioi 0 ↔ e x ∈ Set.Ioi a := by
      intro x
      change 0 < x ↔ a < 1 * x + a
      constructor <;> intro h <;> linarith
    exact ⟨((e.subtype h).symm.trans Real.expOrderIso.toHomeomorph.symm).trans u⟩
  rcases s2v_cad1_gap_shape d hd i with h | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, b, hab, h⟩
  · rw [h]
    exact ⟨Set.univ_nonempty, isOpen_univ, Set.ordConnected_univ,
      ⟨(Homeomorph.Set.univ ℝ).trans u⟩⟩
  · rw [h]
    let e := affineHomeomorph (-1 : ℝ) (2 * a) (by norm_num)
    have he : ∀ x : ℝ, x ∈ Set.Iio a ↔ e x ∈ Set.Ioi a := by
      intro x
      change x < a ↔ a < -1 * x + 2 * a
      constructor <;> intro h <;> linarith
    exact ⟨⟨a - 1, by simp⟩, isOpen_Iio, Set.ordConnected_Iio,
      ⟨(e.subtype he).trans (Classical.choice (ray a))⟩⟩
  · rw [h]
    exact ⟨⟨a + 1, by simp⟩, isOpen_Ioi, Set.ordConnected_Ioi, ray a⟩
  · rw [h]
    have hp : 0 < (b - a) / 2 := by linarith
    let e := affineHomeomorph ((b - a) / 2) ((a + b) / 2) hp.ne'
    have he : e '' Set.Ioo (-1 : ℝ) 1 = Set.Ioo a b := by
      rw [affineHomeomorph_image_Ioo _ _ _ _ hp]
      congr 1 <;> ring
    exact ⟨Set.nonempty_Ioo.mpr hab, isOpen_Ioo, Set.ordConnected_Ioo,
      ⟨((e.image _).trans (Homeomorph.setCongr he)).symm⟩⟩

theorem s2v_cad1_gap_formula {n : ℕ} (d : Fin n → ℝ) (i : Fin (n + 1)) :
    ∃ f : s2v_t11b_Formula 1, ∀ x, x ∈ f.realize ↔ x 0 ∈ s2v_cad1_gap d i := by
  classical
  let f : Fin n → s2v_t11b_Formula 1 := fun k =>
    if k.val < i.val then .compl (.nonneg (MvPolynomial.C (d k) - MvPolynomial.X 0))
    else .compl (.nonneg (MvPolynomial.X 0 - MvPolynomial.C (d k)))
  refine ⟨s2v_t11b_Formula.conjunction (Finset.univ.toList.map f), ?_⟩
  intro x
  rw [s2v_t11b_realize_conjunction]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  apply forall_congr'
  intro k
  by_cases hk : k.val < i.val
  · simp [f, hk, s2v_t11b_Formula.realize, s2v_cad1_gap, not_le.mpr hk]
  · simp [f, hk, s2v_t11b_Formula.realize, s2v_cad1_gap, Nat.le_of_not_gt hk]

end HodgeLean.Foundations.Program
