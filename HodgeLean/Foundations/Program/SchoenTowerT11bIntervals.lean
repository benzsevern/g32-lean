import HodgeLean.Foundations.Program.SchoenTowerT11bDefs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! Elementary interval facts used when selecting a trivialization piece.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A continuous nonvanishing real function has constant sign on a connected subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-invariant interval case. -/
theorem s2v_t11b_nonzero_sign {X : Type*} [TopologicalSpace X]
    (S : Set X) (hS : IsPreconnected S) (g : X → ℝ) (hg : ContinuousOn g S)
    (hn : ∀ t ∈ S, g t ≠ 0) (a b : X) (ha : a ∈ S) (hb : b ∈ S) :
    0 ≤ g a ↔ 0 ≤ g b := by
  have hforward : ∀ a ∈ S, ∀ b ∈ S, 0 ≤ g a → 0 ≤ g b := by
    intro a ha b hb hga
    by_contra hgb
    have hgb' : g b < 0 := lt_of_not_ge hgb
    obtain ⟨c, hc, hgc⟩ := hS.intermediate_value hb ha hg ⟨hgb'.le, hga⟩
    exact hn c hc hgc
  exact ⟨hforward a ha b hb, hforward b hb a ha⟩

/-- A nonzero real polynomial has no roots in a sufficiently short positive interval.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional cells. -/
theorem s2v_t11b_polynomial_root_free (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo (0 : ℝ) r, p.eval t ≠ 0 := by
  have hfin : ({t : ℝ | p.IsRoot t} \ {0}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).sdiff
  have hnot : (0 : ℝ) ∈ ({t : ℝ | p.IsRoot t} \ {0})ᶜ := by simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl 0 hnot
  refine ⟨r, hr, ?_⟩
  intro t ht hroot
  have htball : t ∈ Metric.ball (0 : ℝ) r := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1] using ht.2
  exact (hball htball) ⟨hroot, by simpa using ne_of_gt ht.1⟩

/-- Polynomial inequalities have constant truth value on a short positive interval.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional cells. -/
theorem s2v_t11b_polynomial_sign_interval (p : Polynomial ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ Set.Ioo (0 : ℝ) r, ∀ b ∈ Set.Ioo (0 : ℝ) r,
      (0 ≤ p.eval a ↔ 0 ≤ p.eval b) := by
  by_cases hp : p = 0
  · subst p
    exact ⟨1, zero_lt_one, by simp⟩
  obtain ⟨r, hr, hn⟩ := s2v_t11b_polynomial_root_free p hp
  exact ⟨r, hr, fun a ha b hb => s2v_t11b_nonzero_sign _ isPreconnected_Ioo
    (fun t => p.eval t) p.continuous.continuousOn hn a b ha hb⟩

/-- Diagonal substitution turns a multivariable polynomial into a univariate polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, polynomial inverse-image case. -/
theorem s2v_t11b_eval_diagonal {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (t : ℝ) :
    Polynomial.eval t (MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) p) =
      MvPolynomial.eval (fun _ => t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Polynomial.eval_add, map_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, Polynomial.eval_mul, map_mul, hp]
      simp

/-- A Boolean polynomial formula has constant membership along a short positive diagonal.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional cells. -/
theorem s2v_t11b_formula_interval {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ Set.Ioo (0 : ℝ) r, ∀ b ∈ Set.Ioo (0 : ℝ) r,
      (WithLp.toLp 2 (fun _ : Fin n => a) ∈ f.realize ↔
        WithLp.toLp 2 (fun _ : Fin n => b) ∈ f.realize) := by
  induction f with
  | nonneg p =>
    obtain ⟨r, hr, h⟩ := s2v_t11b_polynomial_sign_interval
      (MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) p)
    refine ⟨r, hr, fun a ha b hb => ?_⟩
    simpa only [s2v_t11b_eval_diagonal, s2v_t11b_Formula.realize, Set.mem_ofPred_eq]
      using h a ha b hb
  | compl f ih =>
    obtain ⟨r, hr, h⟩ := ih
    exact ⟨r, hr, fun a ha b hb => not_congr (h a ha b hb)⟩
  | inter f g ihf ihg =>
    obtain ⟨rf, hrf, hf⟩ := ihf
    obtain ⟨rg, hrg, hg⟩ := ihg
    refine ⟨min rf rg, lt_min hrf hrg, fun a ha b hb => ?_⟩
    exact and_congr
      (hf a ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
        b ⟨hb.1, hb.2.trans_le (min_le_left _ _)⟩)
      (hg a ⟨ha.1, ha.2.trans_le (min_le_right _ _)⟩
        b ⟨hb.1, hb.2.trans_le (min_le_right _ _)⟩)

/-- A finite family of Boolean polynomial formulas has a common positive membership interval.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional cells. -/
theorem s2v_t11b_formula_family_interval {n : ℕ} {ι : Type*}
    (f : ι → s2v_t11b_Formula n) (s : Finset ι) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ a ∈ Set.Ioo (0 : ℝ) r, ∀ b ∈ Set.Ioo (0 : ℝ) r,
      (WithLp.toLp 2 (fun _ : Fin n => a) ∈ (f i).realize ↔
        WithLp.toLp 2 (fun _ : Fin n => b) ∈ (f i).realize) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨ri, hri, hfi⟩ := s2v_t11b_formula_interval (f i)
    obtain ⟨rs, hrs, hfs⟩ := ih
    refine ⟨min ri rs, lt_min hri hrs, fun j hj a ha b hb => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hfi a ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
        b ⟨hb.1, hb.2.trans_le (min_le_left _ _)⟩
    · exact hfs j hj a ⟨ha.1, ha.2.trans_le (min_le_right _ _)⟩
        b ⟨hb.1, hb.2.trans_le (min_le_right _ _)⟩

/-- One piece of a finite Boolean polynomial cover contains an initial positive interval.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.3 and 1.17, base-interval selection. -/
theorem s2v_t11b_cover_contains_interval {ι : Type*} (f : ι → s2v_t11b_Formula 1)
    (s : Finset ι)
    (hcover : ∀ t : ℝ, 0 < t → ∃ i ∈ s,
      WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (f i).realize) :
    ∃ r : ℝ, 0 < r ∧ ∃ i ∈ s, ∀ t ∈ Set.Ioo (0 : ℝ) r,
      WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (f i).realize := by
  obtain ⟨r, hr, h⟩ := s2v_t11b_formula_family_interval f s
  have hsample : r / 2 ∈ Set.Ioo (0 : ℝ) r := ⟨half_pos hr, half_lt_self hr⟩
  obtain ⟨i, hi, hfi⟩ := hcover (r / 2) hsample.1
  exact ⟨r, hr, i, hi, fun t ht => (h i hi (r / 2) hsample t ht).mp hfi⟩

end HodgeLean.Foundations.Program
