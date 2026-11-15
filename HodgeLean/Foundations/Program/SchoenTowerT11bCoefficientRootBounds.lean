import HodgeLean.Foundations.Program.SchoenTowerT11bSmoothCoefficientRoots
import Mathlib.Analysis.Polynomial.CauchyBound

/-! Root confinement for continuous coefficient families over arbitrary parameter spaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped NNReal Topology

/-- Continuous coefficient functions give continuous joint evaluation over any topological parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter root-confinement step. -/
theorem s2v_t11b_continuous_coefficient_family_eval {X : Type*} [TopologicalSpace X]
    (P : Polynomial (X → ℝ)) (hP : ∀ i, Continuous (P.coeff i)) :
    Continuous (fun z : X × ℝ => P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) z.1) z.2) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply continuous_finset_sum
  intro i hi
  exact ((hP i).comp continuous_fst).mul (continuous_snd.pow i)

/-- A compact real region with no roots at a parameter remains root-free on a neighborhood of that parameter.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter root-confinement step. -/
theorem s2v_t11b_continuous_coefficient_compact_exclusion {X : Type*} [TopologicalSpace X]
    (P : Polynomial (X → ℝ)) (hP : ∀ i, Continuous (P.coeff i))
    (a : X) (K : Set ℝ) (hK : IsCompact K)
    (hno : ∀ x ∈ K, P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) a) x ≠ 0) :
    ∀ᶠ t in 𝓝 a, ∀ x ∈ K, P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) t) x ≠ 0 := by
  let U : Set (X × ℝ) := {z | P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) z.1) z.2 ≠ 0}
  have hU : IsOpen U := isOpen_compl_singleton.preimage (s2v_t11b_continuous_coefficient_family_eval P hP)
  have hprod : ({a} : Set X) ×ˢ K ⊆ U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact hno x hx
  obtain ⟨V, W, hV, _, haV, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hprod
  filter_upwards [hV.mem_nhds (haV (Set.mem_singleton a))] with t ht
  intro x hx
  exact (show (t, x) ∈ U from hVW ⟨ht, hKW hx⟩)

/-- A nonzero leading coefficient at a parameter excludes the zero specialized polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter degree-preservation step. -/
theorem s2v_t11b_coefficient_specialization_ne_zero {X : Type*}
    (P : Polynomial (X → ℝ)) (a : X) (hlead : P.leadingCoeff a ≠ 0) :
    P.map (Pi.evalRingHom (fun _ : X => ℝ) a) ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  rw [P.leadingCoeff_map_of_leadingCoeff_ne_zero (Pi.evalRingHom (fun _ : X => ℝ) a) hlead]
  exact hlead

/-- A nonzero leading coefficient gives a uniform local root bound without compactness of the parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter root-confinement step. -/
theorem s2v_t11b_continuous_coefficient_local_root_bound {X : Type*} [TopologicalSpace X]
    (P : Polynomial (X → ℝ)) (hP : ∀ i, Continuous (P.coeff i))
    (a : X) (hlead : P.leadingCoeff a ≠ 0) :
    ∃ B : ℝ≥0, 0 < B ∧ ∀ᶠ t in 𝓝 a, P.leadingCoeff t ≠ 0 ∧
      ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) t) x = 0 → ‖x‖₊ < B := by
  classical
  have hlc : Continuous P.leadingCoeff := hP P.natDegree
  let M : Fin P.natDegree → ℝ≥0 := fun i => ‖P.coeff i.val a / P.leadingCoeff a‖₊ + 1
  have hM : ∀ᶠ t in 𝓝 a, ∀ i : Fin P.natDegree,
      ‖P.coeff i.val t / P.leadingCoeff t‖₊ ≤ M i := by
    apply eventually_all.mpr
    intro i
    have hc := ((hP i.val).continuousAt.div hlc.continuousAt hlead).nnnorm
    exact (hc.eventually_lt continuousAt_const (lt_add_one _)).mono (fun _ h => h.le)
  have hn : ∀ᶠ t in 𝓝 a, P.leadingCoeff t ≠ 0 :=
    (hlc.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hlead
  let B : ℝ≥0 := Finset.univ.sup M + 1
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  filter_upwards [hn, hM] with t ht hMt
  refine ⟨ht, ?_⟩
  intro x hx
  have hlt : 0 < ‖P.leadingCoeff t‖₊ := nnnorm_pos.mpr ht
  have hdeg := P.natDegree_map_of_leadingCoeff_ne_zero (Pi.evalRingHom (fun _ : X => ℝ) t) ht
  have hl := P.leadingCoeff_map_of_leadingCoeff_ne_zero (Pi.evalRingHom (fun _ : X => ℝ) t) ht
  have hbound : (P.map (Pi.evalRingHom (fun _ : X => ℝ) t)).cauchyBound ≤ B := by
    rw [Polynomial.cauchyBound, hdeg, hl]
    apply add_le_add ?_ le_rfl
    apply (div_le_iff₀ hlt).mpr
    apply Finset.sup_le
    intro i hi
    rw [Polynomial.coeff_map]
    have hm := (hMt ⟨i, Finset.mem_range.mp hi⟩).trans
      (Finset.le_sup (f := M) (Finset.mem_univ _))
    rw [nnnorm_div] at hm
    exact (div_le_iff₀ hlt).mp hm
  have hroot : (P.map (Pi.evalRingHom (fun _ : X => ℝ) t)).IsRoot x := by
    simpa only [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map] using hx
  exact (hroot.norm_lt_cauchyBound (s2v_t11b_coefficient_specialization_ne_zero P t ht)).trans_le hbound

/-- Nearby roots stay in any prescribed open neighborhood of the initial roots when the degree does not drop.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter root-confinement step. -/
theorem s2v_t11b_continuous_coefficient_roots_stay_in {X : Type*} [TopologicalSpace X]
    (P : Polynomial (X → ℝ)) (hP : ∀ i, Continuous (P.coeff i))
    (a : X) (hlead : P.leadingCoeff a ≠ 0) (U : Set ℝ) (hU : IsOpen U)
    (hroots : ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) a) x = 0 → x ∈ U) :
    ∀ᶠ t in 𝓝 a, ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : X => ℝ) t) x = 0 → x ∈ U := by
  obtain ⟨B, _, hB⟩ := s2v_t11b_continuous_coefficient_local_root_bound P hP a hlead
  let K : Set ℝ := Metric.closedBall 0 (B : ℝ) \ U
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) (B : ℝ)).diff hU
  have hno := s2v_t11b_continuous_coefficient_compact_exclusion P hP a K hK
    (fun x hx hzero => hx.2 (hroots x hzero))
  filter_upwards [hB, hno] with t ht hnt
  intro x hx
  have hxB : x ∈ Metric.closedBall 0 (B : ℝ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖x‖ < (B : ℝ) from ht.2 x hx).le
  by_contra hxU
  exact hnt x ⟨hxB, hxU⟩ hx

end HodgeLean.Foundations.Program
