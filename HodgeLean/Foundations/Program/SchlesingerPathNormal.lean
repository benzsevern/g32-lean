import HodgeLean.Foundations.Program.SchlesingerPathFixed
import HodgeLean.Foundations.Program.RigidStartingSystemPullbackMonodromy

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_regularPart_analyticAt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) (p : ι)
    (s : ℂ) (hs : ∀ q, q ≠ p → s ≠ t q) :
    AnalyticAt ℂ (b65p_regularPart E t A p) s := by
  unfold b65p_regularPart
  apply Finset.analyticAt_fun_sum
  intro q _
  by_cases hq : q = p
  · simp only [hq, ite_true]
    exact analyticAt_const
  · simp only [hq, ite_false]
    exact ((analyticAt_id.sub analyticAt_const).inv
      (sub_ne_zero.mpr (hs q hq))).smul analyticAt_const

theorem b65p_branch_residue (k : Fin 4) :
    ((b65r_branchOrders k : ℕ) : ℂ) • b65r_operator (b65r_residues (b65r_branchIndices k)) =
      b65p_initialResidue (Sum.inl k) := by
  rw [← b65r_operator_smul]
  fin_cases k <;>
    simp [b65p_initialResidue, b65p_fixedResidue, b65r_residues, b65r_branchIndices,
      b65r_branchOrders]

theorem b65p_branch_centre (k : Fin 4) : b65r_branchCentres k = b65p_fixedPole k := by
  fin_cases k <;> rfl

theorem b65p_base_normal_form_of (p : Fin 12 → ℂ)
    (hinj : Function.Injective (b65p_poles p 0))
    (hreg : ∀ s : ℂ, s ∈ b65s_regular ↔ ∀ q, s ≠ b65p_poles p 0 q)
    (hcoeff : ∀ s ∈ b65s_regular,
      b65p_coefficient (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue s = b65r_pullback s)
    (k : Fin 4) (P₀ : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (hP₀ : IsUnit P₀)
    (hΛ : b65p_initialResidue (Sum.inl k) * P₀ = P₀ * b65p_exponent k) :
    ∃ d : ℝ, 0 < d ∧ ∃ H₀ : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      AnalyticOnNhd ℂ H₀ (ball (b65p_fixedPole k) d) ∧ H₀ (b65p_fixedPole k) = 1 ∧
      ∀ s ∈ ball (b65p_fixedPole k) d,
        (s - b65p_fixedPole k) • deriv H₀ s =
          b65p_exponent k * H₀ s - H₀ s * b65p_exponent k +
            (s - b65p_fixedPole k) • ((Ring.inverse P₀ *
              b65p_regularPart (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue (Sum.inl k) s *
                P₀) * H₀ s) := by
  obtain ⟨d0, hd0, hB⟩ :=
    (b65r_regularPart_analyticAt (b65r_branchIndices k)).exists_ball_analyticOnNhd
  obtain ⟨r, hr, K, -, hKa, hKu, hgauge⟩ := b65r_ramified_local_gauge (Fin 4 → ℂ)
    (b65r_operator (b65r_residues (b65r_branchIndices k)))
    (b65r_regularPart (b65r_branchIndices k)) d0 hd0 hB (b65r_residues_nonresonance _)
    (b65r_branchMaps k) (b65r_branchFactors k) (b65r_branchCentres k) (b65r_branchOrders k)
    (b65r_branch_order_pos k) (b65r_branch_map_analytic k) (b65r_branch_factor_analytic k)
    (b65r_branch_factor_ne k) (b65r_branch_factor k)
  have hpb := b65r_branch_coefficient k (b65p_fixedPole k)
  rw [b65p_branch_centre, b65p_branch_residue] at hgauge
  rw [b65p_branch_centre] at hKa hKu
  set c := b65p_fixedPole k with hcdef
  set Ac := b65p_initialResidue (Sum.inl k) with hAc
  set R := b65p_regularPart (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue (Sum.inl k)
    with hRdef
  set Λ := b65p_exponent k with hΛdef
  have hpk : b65p_poles p 0 (Sum.inl k) = c := rfl
  have hne : ∀ q, q ≠ Sum.inl k → c ≠ b65p_poles p 0 q :=
    fun q hq h ↦ hq (@hinj (Sum.inl k) q h).symm
  have hregev : ∀ᶠ z in 𝓝[≠] c, z ∈ b65s_regular := by
    have h : ∀ q, ∀ᶠ z in 𝓝[≠] c, z ≠ b65p_poles p 0 q := by
      intro q
      by_cases hq : q = Sum.inl k
      · subst hq
        exact self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds (eventually_ne_nhds (hne q hq))
    filter_upwards [Filter.eventually_all.mpr h] with z hz
    exact (hreg z).mpr hz
  have hball : ∀ᶠ z in 𝓝[≠] c, z ∈ ball c r := mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hr)
  have hev := hball.and (hregev.and hpb)
  obtain ⟨d1, hd1, hd1s⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  let d := min r d1
  have hd : 0 < d := lt_min hr hd1
  have hdr : ball c d ⊆ ball c r := ball_subset_ball (min_le_left _ _)
  have hdd1 : ball c d ⊆ ball c d1 := ball_subset_ball (min_le_right _ _)
  have hKeq : ∀ z ∈ ball c d, z ≠ c →
      (z - c) • deriv K z = Ac * K z - K z * Ac + (z - c) • (R z * K z) := by
    intro z hz hzc
    obtain ⟨_, hzreg, hzpb⟩ := hd1s (hdd1 hz) hzc
    have hw : z - c ≠ 0 := sub_ne_zero.mpr hzc
    have h1 := hgauge z ⟨hdr hz, hzc⟩
    have hzpb' := hzpb
    simp only at hzpb'
    rw [← hzpb', ← hcoeff z hzreg, b65p_coefficient_split _ _ _ (Sum.inl k) z, hpk] at h1
    rw [h1]
    simp only [add_mul, smul_add, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hw, one_smul]
    abel
  have hRa : AnalyticAt ℂ R c :=
    b65p_regularPart_analyticAt _ _ _ _ c (fun q hq ↦ hne q hq)
  have hcr : c ∈ ball c r := mem_ball_self hr
  have hKc : Ac * K c = K c * Ac := by
    let g : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) := fun z ↦
      Ac * K z - K z * Ac - (z - c) • (deriv K z - R z * K z)
    have hK1 := (hKa c hcr).continuousAt
    have hK2 := (hKa c hcr).deriv.continuousAt
    have hgc : ContinuousAt g c :=
      ((continuousAt_const.mul hK1).sub (hK1.mul continuousAt_const)).sub
        ((continuousAt_id.sub continuousAt_const).smul (hK2.sub (hRa.continuousAt.mul hK1)))
    have hg0 : ∀ᶠ z in 𝓝[≠] c, g z = 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hd), self_mem_nhdsWithin]
        with z hz hzc
      simp only [g, smul_sub, hKeq z hz hzc]
      abel
    have hlim : Tendsto g (𝓝[≠] c) (𝓝 0) :=
      tendsto_const_nhds.congr' (EventuallyEq.symm hg0)
    have hgc0 := tendsto_nhds_unique (hgc.tendsto.mono_left nhdsWithin_le_nhds) hlim
    simp only [g, sub_self, zero_smul, sub_zero] at hgc0
    exact sub_eq_zero.mp hgc0
  have hAinv : Ac * (Ring.inverse (K c) * P₀) = Ring.inverse (K c) * (P₀ * Λ) := by
    obtain ⟨u, hu⟩ := hKu c hcr
    rw [← hu] at hKc ⊢
    rw [Ring.inverse_unit, ← mul_assoc, (Commute.units_inv_right hKc).eq, mul_assoc, hΛ]
  have hKt : ∀ z ∈ ball c d, z ≠ c →
      (z - c) • (deriv K z * (Ring.inverse (K c) * P₀)) =
        Ac * (K z * (Ring.inverse (K c) * P₀)) - K z * (Ring.inverse (K c) * P₀) * Λ +
          (z - c) • (R z * (K z * (Ring.inverse (K c) * P₀))) := by
    intro z hz hzc
    rw [← smul_mul_assoc, hKeq z hz hzc]
    simp only [add_mul, sub_mul, smul_mul_assoc, mul_assoc, hAinv]
  refine ⟨d, hd, fun z ↦ Ring.inverse P₀ * (K z * (Ring.inverse (K c) * P₀)), ?_, ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul ((hKa z (hdr hz)).mul analyticAt_const)
  · simp only
    rw [Ring.mul_inverse_cancel_left _ _ (hKu c hcr), Ring.inverse_mul_cancel _ hP₀]
  · intro s hs
    by_cases hsc : s = c
    · subst hsc
      simp only [sub_self, zero_smul, add_zero]
      rw [Ring.mul_inverse_cancel_left _ _ (hKu _ hcr), Ring.inverse_mul_cancel _ hP₀,
        mul_one, one_mul, sub_self]
    have hder : HasDerivAt (fun z ↦ Ring.inverse P₀ * (K z * (Ring.inverse (K c) * P₀)))
        (Ring.inverse P₀ * (deriv K s * (Ring.inverse (K c) * P₀))) s :=
      (((hKa s (hdr hs)).differentiableAt.hasDerivAt).mul_const _).const_mul _
    rw [hder.deriv]
    exact b65p_fixed_conj_algebra _ (s - c) Λ Ac P₀ (R s) _ _ hP₀ hΛ (hKt s hs hsc)

end HodgeLean.Foundations.Program
