import HodgeLean.Foundations.Program.SchoenTowerT11bFormulaTruthTable
import HodgeLean.Foundations.Program.SchoenTowerT11bEuclideanCylindricalCoordinates

/-! Finite parameter covers with actual formula charts on connected subregions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every actual Boolean formula has a finite Boolean parameter cover giving actual-fiber cylindrical charts on each connected subregion of a piece.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, actual simultaneous cylindrical formula step. -/
theorem s2v_t11b_formula_finite_subregion_charts {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ (c i).realize) ∧
      ∀ i (K : Set (EuclideanSpace ℝ (Fin n))), K ⊆ (c i).realize → IsPreconnected K → ∀ a : K,
      ∃ F : ({x : ℝ | WithLp.toLp 2 (Fin.cons x (fun v => a.val v)) ∈ f.realize} × K) ≃ₜ
        {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun v => z.1.val v)) ∈ f.realize},
        ∀ y, (F y).val.1 = y.2 := by
  classical
  obtain ⟨k, Q, C, hformula⟩ := s2v_t11b_formula_truth_table f
  let P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ) := fun j => MvPolynomial.finSuccEquiv ℝ n (Q j)
  have hvalue : ∀ t : EuclideanSpace ℝ (Fin n), ∀ x : ℝ,
      C (fun j => decide (0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => t v)) x)) = true ↔
        WithLp.toLp 2 (Fin.cons x (fun v => t v)) ∈ f.realize := by
    intro t x
    simpa only [P, s2v_t11b_finSucc_family_eval] using
      (hformula (WithLp.toLp 2 (Fin.cons x (fun v => t v)))).symm
  obtain ⟨m, c, hcover, hcharts⟩ := s2v_t11b_boolean_finite_connected_subregion_charts P C
  refine ⟨m, c, hcover, ?_⟩
  intro i K hsub hK a
  obtain ⟨F, hF⟩ := hcharts i K hsub hK a
  have hsource : {x : ℝ | C (fun j => decide (0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) x)) = true} =
      {x : ℝ | WithLp.toLp 2 (Fin.cons x (fun v => a.val v)) ∈ f.realize} := by
    ext x
    exact hvalue a.val x
  have htarget : {z : K × ℝ | C (fun j => decide (0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => z.1.val v)) z.2)) = true} =
      {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun v => z.1.val v)) ∈ f.realize} := by
    ext z
    exact hvalue z.1.val z.2
  let A := Homeomorph.setCongr hsource
  refine ⟨(A.symm.prodCongr (Homeomorph.refl K)).trans (F.trans (Homeomorph.setCongr htarget)), ?_⟩
  intro y
  exact hF (A.symm y.1, y.2)


/-- The original Euclidean projection has actual-fiber charts on every connected subregion of a constructed finite Boolean parameter cover.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, actual Euclidean cylindrical refinement step. -/
theorem s2v_t11b_euclidean_finite_subregion_charts {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ (c i).realize) ∧
      ∀ i (K : Set (EuclideanSpace ℝ (Fin n))), K ⊆ (c i).realize → IsPreconnected K → ∀ a : K,
      ∃ e : {y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K} ≃ₜ
        ({y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) = a.val} × K),
        ∀ y, (e y).2.val = WithLp.toLp 2 (fun v => y.val v.succ) := by
  obtain ⟨m, c, hcover, hcharts⟩ := s2v_t11b_formula_finite_subregion_charts f
  refine ⟨m, c, hcover, ?_⟩
  intro i K hsub hK a
  obtain ⟨e, he⟩ := hcharts i K hsub hK a
  let A := s2v_t11b_euclideanSetBaseChart f.realize K
  let B := s2v_t11b_euclideanSetFiberChart f.realize a.val
  let E := (A.trans e.symm).trans (B.symm.prodCongr (Homeomorph.refl K))
  refine ⟨E, ?_⟩
  intro y
  have h := he (e.symm (A y))
  rw [e.apply_symm_apply] at h
  exact (congrArg Subtype.val h).symm

end HodgeLean.Foundations.Program
