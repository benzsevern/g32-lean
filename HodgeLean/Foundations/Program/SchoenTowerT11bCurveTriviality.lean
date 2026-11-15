import HodgeLean.Foundations.Program.SchoenTowerT11bRootCuts
import HodgeLean.Foundations.Program.SchoenTowerT11bRootSigns

/-! Finite Boolean base pieces for inequalities on polynomial curves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A polynomial inequality on a curve has finite base charts away from identically shared components.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, sign-restricted plane curve case. -/
theorem s2v_t11b_nonneg_curve_finite_base_triviality
    (P Q : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) (hdegree : P.natDegree ≠ 0)
    (hres : P.resultant P.derivative ≠ 0) (hcompat : P.resultant Q ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃! i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        ({x : ℝ | P.eval₂ (Polynomial.evalRingHom (b i)) x = 0 ∧
          0 ≤ Q.eval₂ (Polynomial.evalRingHom (b i)) x} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}) ≃ₜ
        {z : {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize} × ℝ |
          P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
          0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2},
        ∀ y, (e y).val.1 = y.2 := by
  classical
  let H := ((P.resultant P.derivative) * P.leadingCoeff) * (P.resultant Q)
  have hH : H ≠ 0 := mul_ne_zero (mul_ne_zero hres (Polynomial.leadingCoeff_ne_zero.mpr hP)) hcompat
  let R := {t : ℝ // t ∈ H.roots.toFinset}
  let k := Fintype.card R
  let D : Fin k ≃ R := (Fintype.equivFin R).symm
  let d : Fin k → ℝ := fun i => (D i).val
  let C := fun s : Fin (k + k) → Bool =>
    s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s
  have hcharts : ∀ s : Fin (k + k) → Bool, ∃ b : ℝ, ∃ e :
      ({x : ℝ | P.eval₂ (Polynomial.evalRingHom b) x = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom b) x} ×
        {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (C s).realize}) ≃ₜ
      {z : {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (C s).realize} × ℝ |
        P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
          0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2},
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
        let e : ({x : ℝ | P.eval₂ (Polynomial.evalRingHom a) x = 0 ∧
            0 ≤ Q.eval₂ (Polynomial.evalRingHom a) x} × K) ≃ₜ
            {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
              0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2} :=
          { toFun := fun y => ⟨(y.2, y.1.val), by
              change P.eval₂ (Polynomial.evalRingHom y.2.val) y.1.val = 0 ∧
                0 ≤ Q.eval₂ (Polynomial.evalRingHom y.2.val) y.1.val
              simpa only [Set.mem_ofPred_eq, hsingle y.2.val y.2.property] using y.1.property⟩
            invFun := fun z => (⟨z.val.2, by
              simpa only [Set.mem_ofPred_eq, hsingle z.val.1.val z.val.1.property] using z.property⟩, z.val.1)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            continuous_toFun := by
              apply Continuous.subtype_mk
              exact continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
            continuous_invFun := by
              apply Continuous.prodMk
              · apply Continuous.subtype_mk
                exact continuous_snd.comp continuous_subtype_val
              · exact continuous_fst.comp continuous_subtype_val }
        exact ⟨a, e, fun _ => rfl⟩
      · have hnonzero : ∀ t ∈ K, H.eval t ≠ 0 := by
          intro t ht hz
          let r : R := ⟨t, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hH).mpr hz)⟩
          have hd : d (D.symm r) = t := congrArg Subtype.val (D.apply_symm_apply r)
          exact hex ⟨D.symm r, hd.symm ▸ ht⟩
        have hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0 := by
          intro t ht hz
          apply hnonzero t ht
          simp only [H, Polynomial.eval_mul, hz, mul_zero, zero_mul]
        have hsimple : ∀ t ∈ K, ∀ x : ℝ,
            P.eval₂ (Polynomial.evalRingHom t) x = 0 →
              (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0 := by
          intro t ht
          apply s2v_t11b_simple_roots_of_resultant_ne_zero P hdegree t
          intro hz
          apply hnonzero t ht
          simp only [H, Polynomial.eval_mul, hz, zero_mul, mul_zero]
        have hQ : ∀ t ∈ K, (P.resultant Q).eval t ≠ 0 := by
          intro t ht hz
          apply hnonzero t ht
          simp only [H, Polynomial.eval_mul, hz, mul_zero]
        obtain ⟨e, he⟩ := s2v_t11b_simple_curve_nonneg_triviality P Q hdegree K
          (s2v_t11b_root_cut_piece_preconnected d s) ⟨a, ha⟩ hlead hsimple hQ
        exact ⟨a, e, he⟩
    · haveI : IsEmpty K := ⟨fun t => hK ⟨t.val, t.property⟩⟩
      haveI : IsEmpty {z : K × ℝ |
          P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
          0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2} :=
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
