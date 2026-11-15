import HodgeLean.Foundations.Program.SchoenTowerT11bRootCuts
import HodgeLean.Foundations.Program.SchoenTowerT11bDegreeStableTriviality

/-! Finite Boolean base pieces including degree drops and multiple fibers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A polynomial family with nonzero derivative resultant has finitely many Boolean base charts.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, plane zero-set case without monicity. -/
theorem s2v_t11b_finite_base_triviality_of_resultant
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) (hdegree : P.natDegree ≠ 0)
    (hres : P.resultant P.derivative ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃! i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        ({x : ℝ | P.eval₂ (Polynomial.evalRingHom (b i)) x = 0} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}) ≃ₜ
        {z : {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize} × ℝ |
          P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
        ∀ y, (e y).val.1 = y.2 := by
  classical
  let H := (P.resultant P.derivative) * P.leadingCoeff
  have hH : H ≠ 0 := mul_ne_zero hres (Polynomial.leadingCoeff_ne_zero.mpr hP)
  let R := {t : ℝ // t ∈ H.roots.toFinset}
  let k := Fintype.card R
  let D : Fin k ≃ R := (Fintype.equivFin R).symm
  let d : Fin k → ℝ := fun i => (D i).val
  let C := fun s : Fin (k + k) → Bool =>
    s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s
  have hcharts : ∀ s : Fin (k + k) → Bool, ∃ b : ℝ, ∃ e :
      ({x : ℝ | P.eval₂ (Polynomial.evalRingHom b) x = 0} ×
        {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (C s).realize}) ≃ₜ
      {z : {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (C s).realize} × ℝ |
        P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
      ∀ y, (e y).val.1 = y.2 := by
    intro s
    let K : Set ℝ := {t | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (C s).realize}
    by_cases hK : K.Nonempty
    · obtain ⟨a, ha⟩ := hK
      by_cases hex : ∃ j, d j ∈ K
      · obtain ⟨j, hj⟩ := hex
        have hsingle : ∀ t ∈ K, t = a := by
          intro t ht
          exact (s2v_t11b_root_cut_piece_at_cut d s j hj t ht).trans
            (s2v_t11b_root_cut_piece_at_cut d s j hj a ha).symm
        exact ⟨a, s2v_t11b_singleton_family_chart
          (fun t x => P.eval₂ (Polynomial.evalRingHom t) x) K a hsingle, fun _ => rfl⟩
      · have hnonzero : ∀ t ∈ K, H.eval t ≠ 0 := by
          intro t ht hz
          let r : R := ⟨t, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hH).mpr hz)⟩
          have hd : d (D.symm r) = t := congrArg Subtype.val (D.apply_symm_apply r)
          exact hex ⟨D.symm r, hd.symm ▸ ht⟩
        have hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0 := by
          intro t ht hz
          apply hnonzero t ht
          simp only [H, Polynomial.eval_mul, hz, mul_zero]
        have hsimple : ∀ t ∈ K, ∀ x : ℝ,
            P.eval₂ (Polynomial.evalRingHom t) x = 0 →
              (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0 := by
          intro t ht
          apply s2v_t11b_simple_roots_of_resultant_ne_zero P hdegree t
          intro hz
          apply hnonzero t ht
          simp only [H, Polynomial.eval_mul, hz, zero_mul]
        obtain ⟨e, he⟩ := s2v_t11b_simple_connected_triviality_of_leadingCoeff P K
          (s2v_t11b_root_cut_piece_preconnected d s) ⟨a, ha⟩ hlead hsimple
        exact ⟨a, e, he⟩
    · haveI : IsEmpty K := ⟨fun t => hK ⟨t.val, t.property⟩⟩
      haveI : IsEmpty {z : K × ℝ |
          P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0} :=
        ⟨fun z => isEmptyElim z.val.1⟩
      exact ⟨0, Homeomorph.empty, fun y => isEmptyElim y.2⟩
  choose b e he using hcharts
  let E := (Fintype.equivFin (Fin (k + k) → Bool)).symm
  refine ⟨Fintype.card (Fin (k + k) → Bool), C ∘ E, b ∘ E, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs, huniq⟩ := s2v_t11b_refinement_partition (s2v_t11b_rootCutTests d)
      (WithLp.toLp 2 (fun _ : Fin 1 => t))
    refine ⟨E.symm s, ?_, ?_⟩
    · simpa only [Function.comp_apply, E.apply_symm_apply] using hs
    · intro j hj
      apply E.injective
      simpa only [E.apply_symm_apply] using huniq (E j) hj
  · intro i
    exact ⟨e (E i), he (E i)⟩

end HodgeLean.Foundations.Program
