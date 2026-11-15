import HodgeLean.Foundations.Program.PrymVariationFramesDefs

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The loop `τ ↦ (t, c τ)` in the fibre at `t`, for a continuous `1`-periodic `c`. -/
def b63e_fibreLoop (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] (t : b6t_polydisc b)
    {c : ℝ → C} (hc : Continuous c) (hper : Function.Periodic c 1) :
    C(UnitAddCircle, b6m_Fibre b C t) :=
  ⟨fun z ↦ (b6m_coordinate b C t).symm (hper.lift z), by
    refine (b6m_coordinate b C t).symm.continuous.comp ?_
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact hc⟩

/-- The integral class of the loop `τ ↦ (t, c τ)`. -/
def b63e_fibreLoopClass (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] (t : b6t_polydisc b)
    {c : ℝ → C} (hc : Continuous c) (hper : Function.Periodic c 1) :
    b6m_H1 (b6m_Fibre b C t) :=
  ((SingularChainComplex ℤ (TopCat.of (b6m_Fibre b C t))).sc 1).moduleCatHomologyClass
    (loopCycle ℤ (b63e_fibreLoop b C t hc hper))

theorem b63e_fibreLoopClass_congr (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) {c d : ℝ → C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (hd : Continuous d) (hdp : Function.Periodic d 1) (h : ∀ τ, c τ = d τ) :
    b63e_fibreLoopClass b C t hc hcp = b63e_fibreLoopClass b C t hd hdp := by
  have : c = d := funext h
  subst this
  rfl

theorem b63e_fibreLoopClass_homotopy (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) (K : unitInterval × ℝ → C) (hK : Continuous K)
    (hKp : ∀ l, Function.Periodic (fun τ ↦ K (l, τ)) 1) :
    b63e_fibreLoopClass b C t (hK.comp (continuous_const.prodMk continuous_id)) (hKp 0) =
      b63e_fibreLoopClass b C t (hK.comp (continuous_const.prodMk continuous_id)) (hKp 1) := by
  let Hc : unitInterval × UnitAddCircle → b6m_Fibre b C t :=
    fun z ↦ (b6m_coordinate b C t).symm ((hKp z.1).lift z.2)
  have hHc : Continuous Hc := by
    refine (b6m_coordinate b C t).symm.continuous.comp ?_
    rw [← (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
    exact hK
  let H : ContinuousMap.Homotopy (b63e_fibreLoop b C t
      (hK.comp (continuous_const.prodMk continuous_id)) (hKp 0))
      (b63e_fibreLoop b C t (hK.comp (continuous_const.prodMk continuous_id)) (hKp 1)) :=
    { toFun := Hc
      continuous_toFun := hHc
      map_zero_left := fun z ↦ by
        obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective z
        rfl
      map_one_left := fun z ↦ by
        obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective z
        rfl }
  exact b6m_integral_loopClass_homotopy H

theorem b63e_fibreLoopClass_homotopy' (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) (K : unitInterval × ℝ → C) (hK : Continuous K)
    (hKp : ∀ l, Function.Periodic (fun τ ↦ K (l, τ)) 1) {c d : ℝ → C}
    (hc : Continuous c) (hcp : Function.Periodic c 1) (hd : Continuous d)
    (hdp : Function.Periodic d 1) (h0 : ∀ τ, K (0, τ) = c τ) (h1 : ∀ τ, K (1, τ) = d τ) :
    b63e_fibreLoopClass b C t hc hcp = b63e_fibreLoopClass b C t hd hdp :=
  ((b63e_fibreLoopClass_congr b C t hc hcp _ (hKp 0) (fun τ ↦ (h0 τ).symm)).trans
    (b63e_fibreLoopClass_homotopy b C t K hK hKp)).trans
    (b63e_fibreLoopClass_congr b C t _ (hKp 1) hd hdp h1)

theorem b63e_fibreLoopClass_transport (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (s t : b6t_polydisc b) {c : ℝ → C} (hc : Continuous c) (hper : Function.Periodic c 1) :
    b6m_H1Equiv (b6m_transport b C s t) (b63e_fibreLoopClass b C s hc hper) =
      b63e_fibreLoopClass b C t hc hper := by
  change homologyMap ℤ 1 (TopCat.ofHom ⟨_, (b6m_transport b C s t).continuous⟩)
    (b63e_fibreLoopClass b C s hc hper) = _
  rw [b63e_fibreLoopClass, b6m_homologyMap_loopCycle]
  rfl

theorem b63e_loopClass_eq_fibreLoopClass (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) [ChartedSpace ℂ (b6m_Fibre b C t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b6m_Fibre b C t)] (γ : b3_SmoothLoop ℂ (b6m_Fibre b C t)) :
    b6m_loopClass _ γ = b63e_fibreLoopClass b C t
      (continuous_snd.comp (continuous_subtype_val.comp γ.2.2.continuous))
      (fun τ ↦ by
        change (γ.1 (τ + 1)).val.2 = (γ.1 τ).val.2
        rw [γ.2.1 τ]) := by
  unfold b6m_loopClass b63e_fibreLoopClass
  congr 2
  ext z
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective z
  change (γ.1 τ) = (b6m_coordinate b C t).symm ((γ.1 τ).val.2)
  exact ((b6m_coordinate b C t).left_inv _).symm

theorem b63e_loopClass_eq_fibreLoopClass_param (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)] (t : V)
    (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)) :
    b6m_loopClass _ γ = b63e_fibreLoopClass b C ⟨t.val, hV t.property⟩
      (continuous_snd.comp (continuous_subtype_val.comp γ.2.2.continuous))
      (fun τ ↦ by
        change (γ.1 (τ + 1)).val.2 = (γ.1 τ).val.2
        rw [γ.2.1 τ]) := by
  unfold b6m_loopClass b63e_fibreLoopClass
  congr 2
  ext z
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective z
  change (γ.1 τ) = (b6m_coordinate b C _).symm ((γ.1 τ).val.2)
  exact ((b6m_coordinate b C _).left_inv _).symm

section Floor

open Filter Topology Set

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem b63e_floorPath_eventually_const (γ : ℤ → ℝ → M) (z : ℤ → M)
    (hγ : ∀ k, b3A_IsGoodPath (E := E) (γ k) (z k) (z (k + 1))) (n : ℤ) :
    ∀ᶠ v in 𝓝 (n : ℝ), γ ⌊v⌋ (Int.fract v) = z n := by
  have h0 : ∀ᶠ v in 𝓝 (n : ℝ), γ n (v - n) = z n := by
    have ht : Tendsto (fun v : ℝ ↦ v - n) (𝓝 (n : ℝ)) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    exact ht.eventually (hγ n).2.1
  have h1 : ∀ᶠ v in 𝓝 (n : ℝ), γ (n - 1) (v - (n - 1)) = z n := by
    have ht : Tendsto (fun v : ℝ ↦ v - (n - 1)) (𝓝 (n : ℝ)) (𝓝 1) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    have := ht.eventually (hγ (n - 1)).2.2
    simpa only [sub_add_cancel] using this
  have h2 : Ioo ((n : ℝ) - 1) (n + 1) ∈ 𝓝 (n : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [h0, h1, h2] with v hv0 hv1 hv2
  rcases le_or_gt (n : ℝ) v with hle | hlt
  · have hfl : ⌊v⌋ = n := by rw [Int.floor_eq_iff]; exact ⟨hle, hv2.2⟩
    rw [Int.fract, hfl, hv0]
  · have hfl : ⌊v⌋ = n - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hv2.1]
    rw [Int.fract, hfl]
    push_cast
    exact hv1

variable [IsManifold 𝓘(ℂ, E) ω M]

theorem b63e_floorLoop_pathIntegral {θ : TangentBundle 𝓘(ℂ, E) M → ℂ}
    (hθ : θ ∈ b3_HolForm E M) (N : ℕ) (γ : ℤ → ℝ → M) (z : ℤ → M)
    (hγ : ∀ k, b3A_IsGoodPath (E := E) (γ k) (z k) (z (k + 1))) :
    b3_pathIntegral E M (fun t ↦ γ ⌊(N : ℝ) * t⌋ (Int.fract ((N : ℝ) * t))) θ =
      ∑ k ∈ Finset.range N, b3_pathIntegral E M (γ k) θ := by
  set L : ℝ → M := fun u ↦ γ ⌊u⌋ (Int.fract u)
  have hL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 L := b3Rest_floorPath_contMDiff γ z hγ
  have hσ : ContDiff ℝ 1 (fun t : ℝ ↦ (N : ℝ) * t) := contDiff_const.mul contDiff_id
  have h1 := b3A_integral_reparam hθ L hL (fun t : ℝ ↦ (N : ℝ) * t) hσ 0 1
  simp only [mul_zero, mul_one] at h1
  unfold b3_pathIntegral
  change ∫ t in (0 : ℝ)..1, b3A_integrand θ (L ∘ fun t ↦ (N : ℝ) * t) t = _
  rw [h1]
  have hint : ∀ k : ℕ, IntervalIntegrable (b3A_integrand θ L) MeasureTheory.volume k (k + 1) :=
    fun k ↦ (b3A_continuous_integrand L hL ⟨θ, hθ⟩).intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ (k : ℝ)) (f := b3A_integrand θ L) (μ := MeasureTheory.volume) (n := N)
    (fun k _ ↦ by push_cast; exact hint k)
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : ∀ t ∈ uIcc (k : ℝ) (k + 1), b3A_integrand θ L t =
      b3A_integrand θ (γ k ∘ fun t ↦ t - k) t := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    refine b3A_integrand_congr θ ?_
    rcases ht.1.lt_or_eq with h0 | h0
    · rcases ht.2.lt_or_eq with h1 | h1
      · filter_upwards [Ioo_mem_nhds h0 h1] with v hv
        have hfl : ⌊v⌋ = (k : ℤ) := by
          rw [Int.floor_eq_iff]; push_cast; exact ⟨hv.1.le, hv.2⟩
        simp only [L, Function.comp_apply, Int.fract, hfl]
        push_cast
        rfl
      · subst h1
        have he := b63e_floorPath_eventually_const γ z hγ ((k : ℤ) + 1)
        have ht : Tendsto (fun v : ℝ ↦ v - k) (𝓝 ((k : ℝ) + 1)) (𝓝 1) :=
          (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
        push_cast at he
        filter_upwards [he, ht.eventually (hγ k).2.2] with v h1 h2
        exact h1.trans h2.symm
    · subst h0
      have he := b63e_floorPath_eventually_const γ z hγ (k : ℤ)
      have ht : Tendsto (fun v : ℝ ↦ v - k) (𝓝 (k : ℝ)) (𝓝 0) :=
        (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
      push_cast at he
      filter_upwards [he, ht.eventually (hγ k).2.1] with v h1 h2
      exact h1.trans h2.symm
  push_cast
  rw [intervalIntegral.integral_congr hk,
    b3A_integral_reparam hθ (γ k) (hγ k).1 (fun t ↦ t - k) (contDiff_id.sub contDiff_const)]
  simp only [sub_self, add_sub_cancel_left]
  rfl

end Floor

end HodgeLean.Foundations.Program
