import HodgeLean.Foundations.Program.SchoenTowerT11bPlaneCoordinates
import HodgeLean.Foundations.Program.SchoenTowerT11bResultantTriviality
import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteValues

/-! Finite last-coordinate charts retaining exceptional degree-drop fibers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Plane zero sets with nonzero derivative resultant have finite actual-fiber projection charts.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, plane zero-set case without monicity. -/
theorem s2v_t11b_coordinate_projection_triviality_of_resultant
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) (hdegree : P.natDegree ≠ 0)
    (hres : P.resultant P.derivative ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃! i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        {y : EuclideanSpace ℝ (Fin 2) |
          P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧
            WithLp.toLp 2 (fun _ : Fin 1 => y 1) ∈ (c i).realize} ≃ₜ
        ({y : EuclideanSpace ℝ (Fin 2) |
          P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧ y 1 = b i} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}),
        ∀ y, (e y).2.val = y.val 1 := by
  obtain ⟨m, c, b, hcover, hcharts⟩ := s2v_t11b_finite_base_triviality_of_resultant P hP hdegree hres
  refine ⟨m, c, b, hcover, ?_⟩
  intro i
  obtain ⟨e, he⟩ := hcharts i
  let F := fun t x => P.eval₂ (Polynomial.evalRingHom t) x
  let K : Set ℝ := {t | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}
  let A := s2v_t11b_planeFamilyBaseChart F K
  let B := s2v_t11b_planeFamilyFiberChart F (b i)
  let E := (A.trans e.symm).trans (B.symm.prodCongr (Homeomorph.refl K))
  refine ⟨E, ?_⟩
  intro y
  change (e.symm (A y)).2.val = y.val 1
  have h := he (e.symm (A y))
  rw [e.apply_symm_apply] at h
  exact (congrArg Subtype.val h).symm

/-- Including constant spatial polynomials, a nonzero derivative resultant gives finite projection charts.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, plane zero-set case without monicity. -/
theorem s2v_t11b_polynomial_projection_triviality_of_resultant
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    (hres : P.resultant P.derivative ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃ i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        {y : EuclideanSpace ℝ (Fin 2) |
          P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧
            WithLp.toLp 2 (fun _ : Fin 1 => y 1) ∈ (c i).realize} ≃ₜ
        ({y : EuclideanSpace ℝ (Fin 2) |
          P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧ y 1 = b i} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}),
        ∀ y, (e y).2.val = y.val 1 := by
  classical
  by_cases hdegree : P.natDegree ≠ 0
  · obtain ⟨m, c, b, hcover, he⟩ :=
      s2v_t11b_coordinate_projection_triviality_of_resultant P hP hdegree hres
    exact ⟨m, c, b, fun t => (hcover t).exists, he⟩
  · have hzero : P.natDegree = 0 := not_ne_iff.mp hdegree
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hzero
    let q := P.coeff 0
    have hq : q ≠ 0 := by
      intro hq
      apply hP
      rw [hC, show P.coeff 0 = 0 from hq, Polynomial.C_0]
    let R := {t : ℝ // t ∈ q.roots.toFinset}
    let D : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
    apply s2v_t11b_finite_values_triviality
      {y : EuclideanSpace ℝ (Fin 2) | P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0}
      (fun y => y 1) (fun i => (D i).val)
    intro y hy
    have hqy : q.eval (y 1) = 0 := by
      have h := congrArg (fun Q : Polynomial (Polynomial ℝ) =>
        Q.eval₂ (Polynomial.evalRingHom (y 1)) (y 0)) hC
      rw [Polynomial.eval₂_C] at h
      exact h.symm.trans hy
    let r : R := ⟨y 1, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hqy)⟩
    exact ⟨D.symm r, (congrArg Subtype.val (D.apply_symm_apply r)).symm⟩

end HodgeLean.Foundations.Program
