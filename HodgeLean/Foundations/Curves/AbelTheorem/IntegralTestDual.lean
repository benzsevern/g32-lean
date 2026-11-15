import HodgeLean.Foundations.Curves.AbelTheorem.AvoidingDual

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem exists_dual_with_integral_test_paths (h : Module.finrank ℂ E = 1)
    {P : ℝ → C} (K : b3Rest_Cover E P)
    (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P) (hper : Function.Periodic P 1)
    {ι : Type} [Fintype ι] (δ : ι → ℝ → C)
    (hδ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (δ j))
    (T : Set C) (hT : IsClosed T) (S : Set C) (hST : S ⊆ T)
    (hK : ∀ k, (chartAt E (K.x k)).symm ''
      ball (chartAt E (K.x k) (K.x k)) (K.r k) ⊆ Sᶜ)
    (hw : ∀ k : ℤ, P (k / K.N) ∉ T) (hδT : ∀ j s, δ j s ∈ T)
    (hend : ∀ j t, P t ≠ δ j 0 ∧ P t ≠ δ j 1)
    (hfin : ∀ (i : Fin K.N) j, {q : ℝ × ℝ | q.1 ∈ Icc ((i : ℝ) / K.N)
      ((i + 1 : ℝ) / K.N) ∧ q.2 ∈ Icc (0 : ℝ) 1 ∧ P q.1 = δ j q.2}.Finite)
    (htr : ∀ j t s, P t = δ j s →
      b3_orient E (b3_velocity E C P t) (b3_velocity E C (δ j) s) ≠ 0) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      (∀ x ∈ S, η =ᶠ[𝓝 x] 0) ∧
      (∀ y, (∀ k : ℤ, y ∉ (chartAt E (K.x k)).symm ''
        ball (chartAt E (K.x k) (K.x k)) (K.r k)) → η y = 0) ∧
      (∀ j, ∃ n : ℤ, b3Forms_lineIntegral η (δ j) 0 1 = (n : ℝ)) ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α →
        ∀ f : ℤ → E → ℝ, (∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
          HasFDerivAt (f k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u) →
        b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α P 0 1 := by
  classical
  let Y (i : Fin K.N) (j : ι) := {q : ℝ × ℝ | q.1 ∈ Icc ((i : ℝ) / K.N)
      ((i + 1 : ℝ) / K.N) ∧ q.2 ∈ Icc (0 : ℝ) 1 ∧ P q.1 = δ j q.2}
  have hdeg : ∀ (i : Fin K.N) j, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      b3Forms_lineIntegral (b3Rest2_arcPiece h K ε i) (δ j) 0 1 =
        (∫ z, b3Rest_rho ε z) * ∑ᶠ q ∈ Y i j,
          (SignType.sign (b3_orient E (b3_velocity E C P q.1)
            (b3_velocity E C (δ j) q.2)) : ℝ) := by
    intro i j
    refine b3Rest2_arc_degree h (K.x i) hP (hδ j) (b3Rest2_cover_le K) zero_le_one
      (fun t ht => (b3Rest2_cover_mem K ht).1)
      (fun s => ⟨fun he => hw i (he ▸ hδT j s), fun he => ?_⟩)
      (hend j) (hfin i j) ?_
    · apply hw ((i : ℤ) + 1)
      have he' : δ j s = P ((((i : ℤ) : ℝ) + 1) / K.N) := he
      convert he' ▸ hδT j s using 1 <;> push_cast <;> rfl
    · intro t s he
      simpa only [b3Forms_velocity_eq_b3] using htr j t s he
  choose ε₁ hε₁ hdeg' using hdeg
  obtain ⟨εm, hεm, hεmlt⟩ := b3Rest_exists_pos_lt
    (Finset.univ : Finset (Fin K.N × ι)) (fun q => ε₁ q.1 q.2)
    (fun q _ => hε₁ q.1 q.2)
  obtain ⟨ε₀, hε₀, hdual⟩ := exists_arc_dual_of_local_primitives h K hP hper hT hw
  let ε := min (ε₀ / 2) εm
  have hε : 0 < ε := lt_min (half_pos hε₀) hεm
  have hεε₀ : ε < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hε₀)
  have hεε₁ (i : Fin K.N) (j : ι) : ε < ε₁ i j :=
    (min_le_right _ _).trans_lt (hεmlt (i, j) (Finset.mem_univ _))
  obtain ⟨κ, hσ, hσt, hκ, hκsupport, hκT, hη, hpair⟩ := hdual ε hε hεε₀
  let m := ∫ z, b3Rest_rho ε z
  have hm : 0 < m := b3Rest_integral_rho_pos hε
  refine ⟨_, hη, ?_, ?_, ?_, hpair⟩
  · intro x hx
    have ha : ∀ᶠ y in 𝓝 x, ∀ i : Fin K.N,
        b3Rest2_arcPiece h K ε i y = 0 := by
      rw [Filter.eventually_all]
      intro i
      have hn : x ∉ tsupport (b3Rest2_arcPiece h K ε i) :=
        fun hi => hK i (hσt i hi) hx
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      exact hy
    have hb : ∀ᶠ y in 𝓝 x, ∀ i : Fin K.N, κ i y = 0 := by
      rw [Filter.eventually_all]
      intro i
      have hn : x ∉ tsupport (κ i) := fun hi => hκT i x hi (hST hx)
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      exact hy
    filter_upwards [ha, hb] with y hy hz
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, hy, hz, add_zero,
      Finset.sum_const_zero, smul_zero, Pi.zero_apply]
  · intro y hy
    have ha (i : Fin K.N) : b3Rest2_arcPiece h K ε i y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hi => hy i (hσt i hi)
    have hb (i : Fin K.N) : κ i y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hi => hy i (hκsupport i hi)
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, ha, hb, add_zero,
      Finset.sum_const_zero, smul_zero]
  · intro j
    let sg (q : ℝ × ℝ) : ℤ :=
      (SignType.sign (b3_orient E (b3_velocity E C P q.1)
        (b3_velocity E C (δ j) q.2)) : ℤ)
    refine ⟨∑ i : Fin K.N, ∑ᶠ q ∈ Y i j, sg q, ?_⟩
    have hκ0 (i : Fin K.N) : b3Forms_lineIntegral (κ i) (δ j) 0 1 = 0 := by
      unfold b3Forms_lineIntegral
      refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s _ => ?_).trans
        intervalIntegral.integral_zero
      have hz : κ i (δ j s) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hi => hκT i _ hi (hδT j s)
      rw [hz]
      rfl
    rw [b3Forms_lineIntegral_smul,
      b3Rest2_lineIntegral_sum _ (fun i _ => (hσ i).add (hκ i)) (hδ j)]
    simp only [b3Forms_lineIntegral_add (hσ _) (hκ _) (hδ j), hκ0, add_zero]
    rw [Finset.sum_congr rfl (fun i _ => hdeg' i j ε hε (hεε₁ i j)),
      ← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hc := (Int.castAddHom ℝ).map_finsum_mem sg (hfin i j)
    simpa only [Int.coe_castAddHom, sg, SignType.intCast_cast] using hc.symm

end HodgeLean.Foundations.Curves.AbelTheorem
