import HodgeLean.Foundations.Program.SchoenTowerT11bDerivativeFormulaPieces
import HodgeLean.Foundations.Program.SchoenTowerT11bFormulaSubregionCharts
import HodgeLean.Foundations.Program.SchoenTowerT11bRealImageFormula

/-! Boolean interval fibers and their cylindrical lifts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Coordinate substitution in Boolean polynomial syntax.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, coordinate step. -/
def s2v_hardt1_rename {n k : ℕ} (r : Fin n → Fin k) :
    s2v_t11b_Formula n → s2v_t11b_Formula k
  | .nonneg p => .nonneg (MvPolynomial.rename r p)
  | .compl f => .compl (s2v_hardt1_rename r f)
  | .inter f g => .inter (s2v_hardt1_rename r f) (s2v_hardt1_rename r g)

/-- Coordinate substitution retains the actual membership equation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, coordinate step. -/
theorem s2v_hardt1_realize_rename {n k : ℕ} (r : Fin n → Fin k)
    (f : s2v_t11b_Formula n) (x : EuclideanSpace ℝ (Fin k)) :
    x ∈ (s2v_hardt1_rename r f).realize ↔
      WithLp.toLp 2 (fun i => x (r i)) ∈ f.realize := by
  induction f with
  | nonneg p => exact Iff.of_eq (congrArg (fun t : ℝ => 0 ≤ t) (MvPolynomial.eval_rename _ _ _))
  | compl f ih => exact not_congr ih
  | inter f g ihf ihg => exact and_congr ihf ihg

/-- A Boolean formula has a finite Boolean cover whose spatial fibers are intervals.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, derivative interval refinement step. -/
theorem s2v_hardt1_interval_formula_cover {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ m : ℕ, ∃ g : Fin m → s2v_t11b_Formula (n + 1),
      (∀ i, (g i).realize ⊆ f.realize) ∧
      (∀ x ∈ f.realize, ∃ i, x ∈ (g i).realize) ∧
      ∀ i (a : EuclideanSpace ℝ (Fin n)), Set.OrdConnected {t : ℝ |
        WithLp.toLp 2 (Fin.cons t (fun v => a v)) ∈ (g i).realize} := by
  classical
  obtain ⟨k, Q, C, hC⟩ := s2v_t11b_formula_truth_table f
  obtain ⟨l, A, j, hj, hA⟩ := s2v_t11b_derivative_atom_refinement Q
  let E := Fintype.equivFin (Fin l → Bool)
  let g := fun i => s2v_t11b_Formula.inter f (s2v_t11b_refinementFormula A (E.symm i))
  have hconstant : ∀ s x y,
      x ∈ (s2v_t11b_refinementFormula A s).realize →
      y ∈ (s2v_t11b_refinementFormula A s).realize →
      (x ∈ f.realize ↔ y ∈ f.realize) := by
    intro s x y hx hy
    apply (hC x).trans
    apply Iff.trans _ (hC y).symm
    have he : (fun i => decide (0 ≤ MvPolynomial.eval (fun v => x v) (Q i))) =
        (fun i => decide (0 ≤ MvPolynomial.eval (fun v => y v) (Q i))) := by
      funext i
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      have hx' := (s2v_t11b_realize_refinementFormula A s x).mp hx (j i)
      have hy' := (s2v_t11b_realize_refinementFormula A s y).mp hy (j i)
      rw [hj i] at hx' hy'
      exact hx'.symm.trans hy'
    rw [he]
  refine ⟨_, g, fun i x hx => hx.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, _⟩ := s2v_t11b_refinement_partition A x
    refine ⟨E s, hx, ?_⟩
    change x ∈ (s2v_t11b_refinementFormula A (E.symm (E s))).realize
    rwa [E.symm_apply_apply]
  · intro i a
    refine ⟨?_⟩
    intro x hx y hy z hz
    have hzA := (hA (E.symm i) a).out hx.2 hy.2 hz
    exact ⟨(hconstant _ _ _ hx.2 hzA).mp hx.1, hzA⟩

/-- An interval-fiber chart over a preconnected base has preconnected total space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical lifting step. -/
theorem s2v_hardt1_interval_lift {n : ℕ} (f : s2v_t11b_Formula (n + 1))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K)
    (hinterval : ∀ a : K, Set.OrdConnected {t : ℝ |
      WithLp.toLp 2 (Fin.cons t (fun v => a.val v)) ∈ f.realize})
    (hchart : ∀ a : K, Nonempty
      (({t : ℝ | WithLp.toLp 2 (Fin.cons t (fun v => a.val v)) ∈ f.realize} × K) ≃ₜ
        {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun v => z.1.val v)) ∈ f.realize})) :
    IsPreconnected {y : EuclideanSpace ℝ (Fin (n + 1)) |
      y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K} := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨F⟩ := hchart ⟨a, ha⟩
    let e := F.trans (s2v_t11b_euclideanSetBaseChart f.realize K).symm
    haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
    haveI : PreconnectedSpace {t : ℝ |
        WithLp.toLp 2 (Fin.cons t (fun v => a v)) ∈ f.realize} :=
      isPreconnected_iff_preconnectedSpace.mp (hinterval ⟨a, ha⟩).isPreconnected
    have H := isPreconnected_range (continuous_subtype_val.comp e.continuous)
    have he : Set.range (fun z => (e z).val) = {y : EuclideanSpace ℝ (Fin (n + 1)) |
        y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K} := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact (e z).property
      · intro hy
        exact ⟨e.symm ⟨y, hy⟩, congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩
    change IsPreconnected (Set.range (fun z => (e z).val)) at H
    rwa [he] at H
  · have he : {y : EuclideanSpace ℝ (Fin (n + 1)) |
        y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hne ⟨_, hy.2⟩
    rw [he]
    exact isPreconnected_empty

end HodgeLean.Foundations.Program
