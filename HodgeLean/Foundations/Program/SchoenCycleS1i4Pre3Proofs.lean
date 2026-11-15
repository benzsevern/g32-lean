import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import HodgeLean.Foundations.Program.SchoenCycleS1i4ShiftHelpers
import HodgeLean.Foundations.Program.SchoenCycleS1i4MonomialHelpers
import HodgeLean.Foundations.Program.SchoenCycleS1i4Pre4Proofs
import HodgeLean.Foundations.Program.SchoenCycleS1i4SliceHelpers
import HodgeLean.Foundations.Program.SchoenCycleS1i4RegularHelpers
import HodgeLean.Foundations.Program.SchoenCycleS1i4NormalizationHelpers
import HodgeLean.Foundations.Program.SchoenCycleMonomialUniqueness
import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticCoordinates


/-! # Third native analytic comparison split
Implications from explicit coefficient summability and analytic representatives.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program
/-- Weighted convolution and pure-power error contraction.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_weighted_contraction_aux
    (d k : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (e f : MvPowerSeries (Fin (d + 1)) ℂ)
    (he : Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a))
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a (e * f)‖ * s2e_divWeight d r a) ∧
    s2e_divNorm d r (e * f) ≤ s2e_divNorm d r e * s2e_divNorm d r f ∧
    Summable (fun a => ‖MvPowerSeries.coeff a (s2e_divError d k e f)‖ *
      s2e_divWeight d r a) ∧
    s2e_divNorm d r (s2e_divError d k e f) ≤
      (s2e_divNorm d r e / r (Fin.last d) ^ k) * s2e_divNorm d r f := by
  obtain ⟨hm, hmn⟩ := s2e_weighted_mul_summable d r (fun i => (hr i).le) e f he hf
  obtain ⟨hs, hsn⟩ := s2e_shift_summable_bound d k r hr f hf
  obtain ⟨ht, htn⟩ := s2e_weighted_mul_summable d r (fun i => (hr i).le)
    e (s2e_divShift d k f) he hs
  have heq (a : Fin (d + 1) →₀ ℕ) :
      ‖MvPowerSeries.coeff a (s2e_divError d k e f)‖ =
      ‖MvPowerSeries.coeff a (e * s2e_divShift d k f)‖ := by
    simp only [s2e_divError, map_neg, norm_neg]
  refine ⟨hm, hmn, ?_, ?_⟩
  · simpa only [heq] using ht
  · unfold s2e_divNorm at htn ⊢
    simp only [heq]
    change s2e_divNorm d r (e * s2e_divShift d k f) ≤ _
    calc
      _ ≤ s2e_divNorm d r e * s2e_divNorm d r (s2e_divShift d k f) := htn
      _ ≤ s2e_divNorm d r e * (s2e_divNorm d r f / r (Fin.last d) ^ k) :=
        mul_le_mul_of_nonneg_left hsn (tsum_nonneg fun a =>
          mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r (fun i => (hr i).le) a))
      _ = _ := by unfold s2e_divNorm; ring

/-- Absolutely summable weighted coefficients give an analytic monomial sum.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_series_realization_aux
    (d : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a)) :
    AnalyticAt ℂ (s2e_divSeries (d + 1) F) 0 ∧
    ∀ᶠ z in nhds (0 : Fin (d + 1) → ℂ),
      HasSum (fun a => MvPowerSeries.coeff a F * ∏ i, z i ^ a i)
        (s2e_divSeries (d + 1) F z) := by
  obtain ⟨p, ρ, hp, _, hs⟩ := s2e_s1i4_monomial_multilinear_aux d r hr F hF
  exact ⟨hp.analyticAt, hs⟩

/-- An analytic representative has absolutely summable coefficients at small radii.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_analytic_coefficients_aux
    (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : Fin (d + 1) → ℝ, ∃ F : MvPowerSeries (Fin (d + 1)) ℂ,
      (∀ i, 0 < r i ∧ r i < ε) ∧
      Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a) ∧
      f =ᶠ[nhds 0] s2e_divSeries (d + 1) F := by
  obtain ⟨p, ρ, hp⟩ := hf
  obtain ⟨F, r, hr, hF, _, _, he⟩ := s2e_s1i4_multilinear_coefficients_aux d f p ρ hp ε hε
  exact ⟨r, F, hr, hF, he⟩

/-- Analytic monomial realizations determine their coefficients.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_coefficient_uniqueness_aux
    (d : ℕ) (r s : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (F G : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a))
    (hG : Summable (fun a => ‖MvPowerSeries.coeff a G‖ * s2e_divWeight d s a))
    (hFG : s2e_divSeries (d + 1) F =ᶠ[nhds 0] s2e_divSeries (d + 1) G) : F = G := by
  exact s2e_monomial_germ_injective d r s hr hs F G hF hG hFG

/-- A last-axis regular divisor has a small normalized error at anisotropic radii.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_normalized_smallness_aux
    (d k : ℕ) (g : (Fin (d + 1) → ℂ) → ℂ) (hg : AnalyticAt ℂ g 0)
    (hzero : ∀ j < k, iteratedDeriv j (fun t : ℂ => g (Pi.single (Fin.last d) t)) 0 = 0)
    (hlead : iteratedDeriv k (fun t : ℂ => g (Pi.single (Fin.last d) t)) 0 ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℂ, ∃ r : Fin (d + 1) → ℝ, ∃ e : MvPowerSeries (Fin (d + 1)) ℂ,
      c ≠ 0 ∧ (∀ i, 0 < r i ∧ r i < ε) ∧
      Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a) ∧
      s2e_divNorm d r e < r (Fin.last d) ^ k ∧
      (fun z => c * g z) =ᶠ[nhds 0]
        s2e_divSeries (d + 1) (MvPowerSeries.X (Fin.last d) ^ k + e) := by
  classical
  obtain ⟨p, ρ, hp⟩ := hg
  obtain ⟨F, R, hR, hF, _, hder, hgF⟩ :=
    s2e_s1i4_multilinear_coefficients_aux d g p ρ hp ε hε
  let a := MvPowerSeries.coeff (Finsupp.single (Fin.last d) k) F
  have ha : a ≠ 0 := by
    intro h
    apply hlead
    rw [hder k]
    change (k.factorial : ℂ) * a = 0
    rw [h, mul_zero]
  let c := a⁻¹
  let e := c • F - MvPowerSeries.X (Fin.last d) ^ k
  have hc : c ≠ 0 := inv_ne_zero ha
  have hE := s2e_weighted_sub_summable d R (fun i => (hR i).1) (c • F)
    (MvPowerSeries.X (Fin.last d) ^ k) (s2e_weighted_smul_summable d R F hF c)
    (s2e_weighted_X_pow_summable d k R)
  have haxis : ∀ j ≤ k, MvPowerSeries.coeff (Finsupp.single (Fin.last d) j) e = 0 := by
    intro j hj
    have hs : (Finsupp.single (Fin.last d) j : Fin (d + 1) →₀ ℕ) =
        Finsupp.single (Fin.last d) k ↔ j = k := by
      constructor
      · intro h
        simpa using congrArg (fun x : Fin (d + 1) →₀ ℕ => x (Fin.last d)) h
      · rintro rfl
        rfl
    change MvPowerSeries.coeff _ (c • F - MvPowerSeries.X (Fin.last d) ^ k) = 0
    rw [map_sub, map_smul, smul_eq_mul, MvPowerSeries.coeff_X_pow]
    by_cases hjk : j = k
    · subst j
      rw [if_pos rfl]
      change a⁻¹ * a - 1 = 0
      rw [inv_mul_cancel₀ ha, sub_self]
    · have hjlt : j < k := lt_of_le_of_ne hj hjk
      have hfact : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
      have hcoeff : MvPowerSeries.coeff (Finsupp.single (Fin.last d) j) F = 0 := by
        have hd := hder j
        rw [hzero j hjlt] at hd
        exact (mul_eq_zero.mp hd.symm).resolve_left hfact
      rw [hcoeff, mul_zero, if_neg (fun h => hjk (hs.mp h)), sub_zero]
  obtain ⟨r, hr, he, hn⟩ := s2e_s1i4_anisotropic_majorant_aux d k R
    (fun i => (hR i).1) e hE haxis ε 1 hε zero_lt_one
  refine ⟨c, r, e, hc, fun i => ⟨(hr i).1, (hr i).2.trans_le (min_le_right _ _)⟩,
    he, by simpa only [one_mul] using hn, ?_⟩
  have hid : MvPowerSeries.X (Fin.last d) ^ k + e = c • F := by dsimp [e]; abel
  filter_upwards [hgF] with z hz
  change c * g z = _
  rw [hid, s2e_divSeries_smul, hz]

/-- A truncated convergent series has analytic lower-dimensional coefficients.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_remainder_realization_aux
    (d k : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (B : MvPowerSeries (Fin (d + 1)) ℂ)
    (hB : Summable (fun a => ‖MvPowerSeries.coeff a B‖ * s2e_divWeight d r a))
    (hdegree : ∀ a, k ≤ a (Fin.last d) → MvPowerSeries.coeff a B = 0) :
    ∃ b : Fin k → (Fin d → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (b i) 0) ∧
      s2e_divSeries (d + 1) B =ᶠ[nhds 0]
        (fun z => ∑ i : Fin k, b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ)) := by
  let b := fun j : Fin k => s2e_divSeries d (s2e_coefficientSlice d j B)
  refine ⟨b, ?_, ?_⟩
  · intro j
    apply s2e_series_analytic_all_dimensions d (fun i => r i.castSucc)
      (fun i => hr i.castSucc)
    simpa only [s2e_coefficientSlice_coeff] using s2e_slice_summable d j r hr B hB
  · filter_upwards [s2e_eventually_polydisc d r hr] with z hz
    exact s2e_slice_realization_at d k r hr B hB hdegree z hz

/-- Formal multiplication and addition transport to analytic monomial realizations.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_analytic_transport_aux
    (d : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (F G Q B : MvPowerSeries (Fin (d + 1)) ℂ)
    (hG : Summable (fun a => ‖MvPowerSeries.coeff a G‖ * s2e_divWeight d r a))
    (hQ : Summable (fun a => ‖MvPowerSeries.coeff a Q‖ * s2e_divWeight d r a))
    (hB : Summable (fun a => ‖MvPowerSeries.coeff a B‖ * s2e_divWeight d r a))
    (hidentity : F = G * Q + B) :
    s2e_divSeries (d + 1) F =ᶠ[nhds 0]
      (fun z => s2e_divSeries (d + 1) G z * s2e_divSeries (d + 1) Q z +
        s2e_divSeries (d + 1) B z) := by
  obtain ⟨hGQ, _⟩ := s2e_weighted_mul_summable d r (fun i => (hr i).le) G Q hG hQ
  filter_upwards [s2e_eventually_polydisc d r hr] with z hz
  have hg := s2e_monomial_norm_summable d r G hG z hz
  have hq := s2e_monomial_norm_summable d r Q hQ z hz
  have hb := s2e_monomial_norm_summable d r B hB z hz
  have hp := s2e_monomial_norm_summable d r (G * Q) hGQ z hz
  rw [hidentity, s2e_divSeries_add_at _ _ _ _ hp.of_norm hb.of_norm,
    s2e_divSeries_mul_at _ _ _ _ hg hq]

/-- A nonzero analytic germ becomes last-axis regular after a linear substitution.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Weierstrass division construction. -/
theorem s2e_s1i4_linear_regularization_aux
    (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hne : ¬ f =ᶠ[nhds 0] 0) :
    ∃ L : (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ), ∃ k : ℕ,
      (∀ j < k, iteratedDeriv j (fun t : ℂ => f (L (Pi.single (Fin.last d) t))) 0 = 0) ∧
      iteratedDeriv k (fun t : ℂ => f (L (Pi.single (Fin.last d) t))) 0 ≠ 0 := by
  classical
  obtain ⟨p, ρ, hp⟩ := hf
  have hex := s2e_nonzero_homogeneous_term (d + 1) f p ρ hp hne
  let k := Nat.find hex
  have hk : s2e_multilinearPolynomial (d + 1) k (p k) ≠ 0 := Nat.find_spec hex
  obtain ⟨v, hv, hPv⟩ := s2e_s1i4_homogeneous_direction_aux d k _ hk
    (s2e_multilinearPolynomial_homogeneous _ _ _)
  obtain ⟨L, hL⟩ := s2e_s1i4_direction_basis_aux d v hv
  let u : ℂ →L[ℂ] (Fin (d + 1) → ℂ) :=
    L.toContinuousLinearMap.comp ((ContinuousLinearMap.id ℂ ℂ).smulRight (Pi.single (Fin.last d) 1))
  have hu (t : ℂ) : u t = L (Pi.single (Fin.last d) t) := by
    change L (t • Pi.single (Fin.last d) 1) = _
    congr 1
    ext i
    by_cases hi : i = Fin.last d <;> simp [Pi.single_apply, hi, eq_comm]
  have hu1 : u 1 = v := by rw [hu, hL]
  refine ⟨L, k, ?_, ?_⟩
  · intro j hj
    have hj0 : s2e_multilinearPolynomial (d + 1) j (p j) = 0 :=
      not_not.mp (Nat.find_min hex hj)
    have hd := s2e_line_iteratedDeriv (d + 1) f p ρ hp u j
    simpa only [hu, hu1, s2e_multilinear_diagonal_expansion, hj0, map_zero, mul_zero] using hd
  · have hd := s2e_line_iteratedDeriv (d + 1) f p ρ hp u k
    rw [hu1, s2e_multilinear_diagonal_expansion] at hd
    have hfact : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hne' : iteratedDeriv k (fun t => f (u t)) 0 ≠ 0 := by
      rw [hd]
      exact mul_ne_zero hfact hPv
    simpa only [hu] using hne'

/-- Remainders lying in an ideal have finitely many module generators.
Source: Grauert–Remmert, Coherent Analytic Sheaves, Chapter II, "Local Weierstrass Theory", Noetherianity via Weierstrass division; Mathlib, IsNoetherian.noetherian. -/
theorem s2e_s1i4_finite_remainder_module_aux
    (d k : ℕ) (hprev : IsNoetherianRing (s2e_nativeAnalyticGermRing d))
    (ι : s2e_nativeAnalyticGermRing d →+* s2e_nativeAnalyticGermRing (d + 1))
    (I : Ideal (s2e_nativeAnalyticGermRing (d + 1))) :
    ∃ n : ℕ, ∃ b : Fin n → Fin k → s2e_nativeAnalyticGermRing d,
      (∀ j, (∑ i : Fin k, ι (b j i) * s2e_nativeAnalytic_coordinate (d + 1)
        (Fin.last d) ^ (i : ℕ)) ∈ I) ∧
      ∀ v : Fin k → s2e_nativeAnalyticGermRing d,
        (∑ i : Fin k, ι (v i) * s2e_nativeAnalytic_coordinate (d + 1)
          (Fin.last d) ^ (i : ℕ)) ∈ I →
        ∃ c : Fin n → s2e_nativeAnalyticGermRing d,
          v = ∑ j : Fin n, c j • b j := by
  let R := s2e_nativeAnalyticGermRing d
  let S := s2e_nativeAnalyticGermRing (d + 1)
  let x : S := s2e_nativeAnalytic_coordinate (d + 1) (Fin.last d)
  let N : Submodule R (Fin k → R) :=
    { carrier := {v | (∑ i : Fin k, ι (v i) * x ^ (i : ℕ)) ∈ I}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        change (∑ i : Fin k, ι ((v + w) i) * x ^ (i : ℕ)) ∈ I
        simpa only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] using
          I.add_mem hv hw
      smul_mem' := by
        intro c v hv
        change (∑ i : Fin k, ι ((c • v) i) * x ^ (i : ℕ)) ∈ I
        simpa only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc,
          ← Finset.mul_sum] using I.mul_mem_left (ι c) hv }
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian N)
  refine ⟨n, b, ?_, ?_⟩
  · intro j
    change b j ∈ N
    rw [← hb]
    exact Submodule.subset_span (Set.mem_range_self j)
  · intro v hv
    have hv' : v ∈ Submodule.span R (Set.range b) := hb.symm ▸ hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hv'
    exact ⟨c, hc.symm⟩

/-- Evaluation identifies the dimension-zero analytic germ ring with the scalars.
Source: Mathlib, Filter.Germ.coe_eq and Fin.elim0; Gunning–Rossi, Chapter II, §B, analytic local rings. -/
theorem s2e_s1i4_dimension_zero_aux
    : Function.Bijective (s2e_nativeAnalyticGerm_value 0) := by
  constructor
  · intro a b hab
    obtain ⟨f, hf, he⟩ := a.property
    obtain ⟨g, hg, hge⟩ := b.property
    have hv : f 0 = g 0 := by
      change Filter.Germ.liftOn a.val _ _ = Filter.Germ.liftOn b.val _ _ at hab
      rw [← he, ← hge] at hab
      exact hab
    apply Subtype.ext
    rw [← he, ← hge]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun x => by
      have hx : x = 0 := Subsingleton.elim _ _
      simpa only [hx] using hv
  · intro c
    exact ⟨⟨Filter.Germ.ofFun (fun _ => c), ⟨_, analyticAt_const, rfl⟩⟩, rfl⟩

end HodgeLean.Foundations.Program
