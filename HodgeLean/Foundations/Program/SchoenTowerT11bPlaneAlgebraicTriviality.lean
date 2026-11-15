import HodgeLean.Foundations.Program.SchoenTowerT11bRadicalResultants

/-! Finite projection charts for plane equations with arbitrary factor multiplicities.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every nonzero plane polynomial equation has finite Boolean actual-fiber projection charts.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, plane zero-set case without monicity. -/
theorem s2v_t11b_plane_polynomial_projection_triviality
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) :
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
  obtain ⟨m, c, b, hcover, hcharts⟩ :=
    s2v_t11b_polynomial_projection_triviality_of_resultant
      (UniqueFactorizationMonoid.radical P) UniqueFactorizationMonoid.radical_ne_zero
      (s2v_t11b_radical_derivative_resultant P)
  refine ⟨m, c, b, hcover, ?_⟩
  intro i
  obtain ⟨e, he⟩ := hcharts i
  let K : Set ℝ := {t | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}
  have hs : {y : EuclideanSpace ℝ (Fin 2) |
      P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧ y 1 ∈ K} =
      {y : EuclideanSpace ℝ (Fin 2) |
        (UniqueFactorizationMonoid.radical P).eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧
          y 1 ∈ K} := by
    ext y
    exact and_congr (s2v_t11b_radical_family_zero_iff P hP (y 1) (y 0)).symm Iff.rfl
  have hf : {y : EuclideanSpace ℝ (Fin 2) |
      P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧ y 1 = b i} =
      {y : EuclideanSpace ℝ (Fin 2) |
        (UniqueFactorizationMonoid.radical P).eval₂ (Polynomial.evalRingHom (y 1)) (y 0) = 0 ∧
          y 1 = b i} := by
    ext y
    exact and_congr (s2v_t11b_radical_family_zero_iff P hP (y 1) (y 0)).symm Iff.rfl
  let A := Homeomorph.setCongr hs
  let B := Homeomorph.setCongr hf
  let E := (A.trans e).trans (B.symm.prodCongr (Homeomorph.refl K))
  exact ⟨E, fun y => he (A y)⟩

end HodgeLean.Foundations.Program
