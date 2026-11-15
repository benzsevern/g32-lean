import HodgeLean.Foundations.Program.GaussManinToriDefs

/-!
# The differential of the D2 chart period map and the Kodaira--Spencer map

Helper lemmas for the Track D2 differential statements: the graph projection of the D1 chart on
its domain, the derivative of the chart period map computed from the frame identity
`π_b (P_b φ) = P_b φ`, and the comparison between `mfderiv` and the derivative in the extended
chart.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff Matrix Topology

namespace HodgeLean.Foundations.Program

open HodgeBlocks

section Linear

theorem d2k_finrank_map_of_disjoint {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (f : V →ₗ[K] V') (p : Submodule K V)
    (h : Disjoint (LinearMap.ker f) p) :
    Module.finrank K (p.map f) = Module.finrank K p := by
  have hinj : Function.Injective (f.domRestrict p) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (x : V) ∈ LinearMap.ker f ⊓ p := ⟨hx, x.2⟩
    rw [h.eq_bot] at hx'
    exact Subtype.ext hx'
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem d2k_graphProjection_spec (G₀ G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (h : IsCompl (G 1) ((G₀ 1).map (sigmaQ V))) :
    (∀ x, d1_graphProjection 1 G₀ G 1 x = x ↔ x ∈ G 1) ∧
      ∀ x ∈ (G₀ 1).map (sigmaQ V), d1_graphProjection 1 G₀ G 1 x = 0 := by
  have e : (1 : ℤ) - 1 + 1 = 1 := by norm_num
  have h' : IsCompl (G 1) ((G₀ (1 - 1 + 1)).map (sigmaQ V)) := by rw [e]; exact h
  unfold d1_graphProjection
  rw [dite_eq_left h']
  refine ⟨fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩, fun x hx ↦ ?_⟩
  · rw [← hx]; exact Submodule.coe_mem _
  · rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left h' hx]; rfl
  · have : x ∈ (G₀ (1 - 1 + 1)).map (sigmaQ V) := by rw [e]; exact hx
    rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right h' this]; rfl

end Linear

/-- The action of the single matrix of a chart point on coordinate vectors, `(M, v) ↦ M₀ v`, as a
continuous bilinear map.
Source: Mathlib `Matrix.toLin'` and `LinearMap.toContinuousLinearMap`. -/
def d2k_act (n : ℕ) : (Fin 1 → Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).toLinearMap ∘ₗ
      (Matrix.toLin' : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] _).toLinearMap ∘ₗ
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ Fin n → Fin n → ℂ) 0)

theorem d2k_act_apply {n : ℕ} (M : Fin 1 → Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    d2k_act n M v = M 0 *ᵥ v := rfl

example : d2k_act 1 0 = 0 := map_zero _

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem d2k_fderiv_eq_zero_iff {n : ℕ} {Mat D Hs : Type*} [NormedAddCommGroup Mat]
    [NormedSpace ℂ Mat] [FiniteDimensional ℂ Mat] [AddCommGroup D] [Module ℂ D]
    [AddCommGroup Hs] [Module ℂ Hs] (c : Hs ≃ₗ[ℂ] (Fin n → ℂ))
    (Φ : E → Fin 1 → Fin n → Fin n → ℂ) (P : E → Mat) (z₀ : E)
    (hΦ : DifferentiableAt ℂ Φ z₀) (hP : DifferentiableAt ℂ P z₀)
    (ev : Mat →ₗ[ℂ] D →ₗ[ℂ] Hs) (F W : Submodule ℂ Hs)
    (hF : F = LinearMap.range (ev (P z₀))) (hFW : F ⊔ W = ⊤)
    (h1 : ∀ᶠ z in 𝓝 z₀, ∀ φ, d2k_act n (Φ z) (c (ev (P z) φ)) = c (ev (P z) φ))
    (h2 : ∀ᶠ z in 𝓝 z₀, ∀ w ∈ W, d2k_act n (Φ z) (c w) = 0)
    (h3 : ∀ y, d2k_act n (Φ z₀) (c y) = c y ↔ y ∈ F) (u : E) :
    fderiv ℂ Φ z₀ u = 0 ↔ ∀ φ, ev (fderiv ℂ P z₀ u) φ ∈ F := by
  set Φ' := fderiv ℂ Φ z₀
  set P' := fderiv ℂ P z₀
  have hA : HasFDerivAt (fun z ↦ d2k_act n (Φ z)) ((d2k_act n).comp Φ') z₀ :=
    (d2k_act n).hasFDerivAt.comp z₀ hΦ.hasFDerivAt
  -- the frame identity, differentiated
  have key1 : ∀ φ, d2k_act n (Φ' u) (c (ev (P z₀) φ)) + d2k_act n (Φ z₀) (c (ev (P' u) φ)) =
      c (ev (P' u) φ) := by
    intro φ
    let S : Mat →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (c.toLinearMap ∘ₗ ev.flip φ)
    have hS : HasFDerivAt (fun z ↦ S (P z)) (S.comp P') z₀ := S.hasFDerivAt.comp z₀ hP.hasFDerivAt
    have h1' := hA.clm_apply hS
    have h1'' : HasFDerivAt (fun z ↦ S (P z)) _ z₀ := h1'.congr_of_eventuallyEq
      (h1.mono fun z hz ↦ (hz φ).symm)
    have := congrArg (fun L ↦ L u) (hS.unique h1'')
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at this
    change c (ev (P' u) φ) = d2k_act n (Φ z₀) (c (ev (P' u) φ)) +
      d2k_act n (Φ' u) (c (ev (P z₀) φ)) at this
    exact (this.trans (add_comm _ _)).symm
  have key2 : ∀ w ∈ W, d2k_act n (Φ' u) (c w) = 0 := by
    intro w hw
    have h0 : HasFDerivAt (fun z ↦ d2k_act n (Φ z) (c w)) _ z₀ :=
      hA.clm_apply (hasFDerivAt_const (c w) z₀)
    have h0' : HasFDerivAt (fun z ↦ d2k_act n (Φ z) (c w)) (0 : E →L[ℂ] (Fin n → ℂ)) z₀ :=
      (hasFDerivAt_const (0 : Fin n → ℂ) z₀).congr_of_eventuallyEq
        (h2.mono fun z hz ↦ hz w hw)
    have := congrArg (fun L ↦ L u) (h0.unique h0')
    simpa using this
  constructor
  · intro h φ
    have := key1 φ
    rw [h, map_zero, zero_apply, zero_add] at this
    exact (h3 _).1 this
  · intro h
    have hall : ∀ y, d2k_act n (Φ' u) (c y) = 0 := by
      intro y
      have hy : y ∈ F ⊔ W := hFW ▸ Submodule.mem_top
      obtain ⟨f, hf, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, map_add, key2 w hw, add_zero]
      rw [hF] at hf
      obtain ⟨φ, rfl⟩ := hf
      have := key1 φ
      rw [(h3 _).2 (h φ), add_eq_right] at this
      exact this
    funext i j k
    fin_cases i
    have := congrFun (hall (c.symm (Pi.single k 1))) j
    rw [LinearEquiv.apply_symm_apply, d2k_act_apply] at this
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this


/-- A map with injective strict derivative at a point of a finite-dimensional space is injective
near that point. -/
theorem d2k_injOn_of_hasStrictFDerivAt [FiniteDimensional ℂ E] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] {f : E → G} {f' : E →L[ℂ] G} {z₀ : E}
    (hf : HasStrictFDerivAt f f' z₀) (hinj : Function.Injective f') :
    ∃ s ∈ 𝓝 z₀, Set.InjOn f s := by
  obtain ⟨K, hK0, hK⟩ := (f' : E →ₗ[ℂ] G).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨s, hs, hap⟩ := hf.approximates_deriv_on_nhds (c := (2 * K)⁻¹)
    (Or.inr (by positivity))
  refine ⟨s, hs, fun x hx y hy hxy ↦ ?_⟩
  have h1 := hap x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 := hK.le_mul_dist (x - y) 0
  rw [dist_zero_right, map_zero, dist_zero_right] at h2
  change ‖x - y‖ ≤ K * ‖f' (x - y)‖ at h2
  have hK0' : (0 : ℝ) < K := hK0
  have h3 : ‖x - y‖ ≤ ‖x - y‖ / 2 := by
    calc ‖x - y‖ ≤ K * ‖f' (x - y)‖ := h2
      _ ≤ K * (((2 * K)⁻¹ : NNReal) * ‖x - y‖) := by gcongr
      _ = ‖x - y‖ / 2 := by
        push_cast
        field_simp
  have : ‖x - y‖ = 0 := by linarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end Calculus

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

theorem d2k_differentiableAt_chart {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : B → G} {b : B} (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, G) f b) :
    DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ, E) b).symm) (extChartAt 𝓘(ℂ, E) b b) := by
  have := hf.differentiableWithinAt_writtenInExtChartAt
  simp only [modelWithCornersSelf_coe, Set.range_id, differentiableWithinAt_univ] at this
  simpa [writtenInExtChartAt, extChartAt_model_space_eq_id] using this

theorem d2k_mfderiv_eq_fderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : B → G} {b : B} (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, G) f b) :
    (show E →L[ℂ] G from mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f b) =
      fderiv ℂ (f ∘ (extChartAt 𝓘(ℂ, E) b).symm) (extChartAt 𝓘(ℂ, E) b b) := by
  rw [hf.mfderiv_abuse]
  simp [writtenInExtChartAt, fderivWithin_univ]

theorem d2k_contDiffAt_chart {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {n : WithTop ℕ∞} {f : B → G} {b : B} (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, G) n f b) :
    ContDiffAt ℂ n (f ∘ (extChartAt 𝓘(ℂ, E) b).symm) (extChartAt 𝓘(ℂ, E) b b) := by
  have := (contMDiffAt_iff.1 hf).2
  simp only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] at this
  simpa [extChartAt_model_space_eq_id] using this

end Manifold

section Opens

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem d2k_opens_symm (W : TopologicalSpace.Opens F) (b : W) :
    extChartAt 𝓘(ℂ, F) b b = b ∧
      ∀ᶠ t in 𝓝 (b : F), ((extChartAt 𝓘(ℂ, F) b).symm t : F) = t := by
  refine ⟨rfl, ?_⟩
  have := W.chartAt_subtype_val_symm_eventuallyEq (H := F) (x := b)
  rw [chartAt_self_eq] at this
  filter_upwards [this] with t ht
  exact ht.symm

omit [NormedAddCommGroup G] [NormedSpace ℂ G] in
theorem d2k_opens_eventuallyEq (W : TopologicalSpace.Opens F) (b : W) (f : W → G) (f' : F → G)
    (hf' : ∀ᶠ t in 𝓝 (b : F), ∀ h : t ∈ W, f ⟨t, h⟩ = f' t) :
    f ∘ (extChartAt 𝓘(ℂ, F) b).symm =ᶠ[𝓝 (extChartAt 𝓘(ℂ, F) b b)] f' := by
  rw [(d2k_opens_symm W b).1]
  filter_upwards [(d2k_opens_symm W b).2, hf'] with t ht ht'
  rw [Function.comp_apply, ← ht' (ht ▸ ((extChartAt 𝓘(ℂ, F) b).symm t).2)]
  congr 1
  exact Subtype.ext ht

theorem d2k_mfderiv_opens (W : TopologicalSpace.Opens F) {f : W → G} {b : W}
    (hf : MDifferentiableAt 𝓘(ℂ, F) 𝓘(ℂ, G) f b) (f' : F → G)
    (hf' : ∀ᶠ t in 𝓝 (b : F), ∀ h : t ∈ W, f ⟨t, h⟩ = f' t) :
    DifferentiableAt ℂ f' b ∧
      (show F →L[ℂ] G from mfderiv 𝓘(ℂ, F) 𝓘(ℂ, G) f b) = fderiv ℂ f' b := by
  have he := d2k_opens_eventuallyEq W b f f' hf'
  have h1 := d2k_differentiableAt_chart hf
  rw [(d2k_opens_symm W b).1] at he h1
  refine ⟨h1.congr_of_eventuallyEq he.symm, ?_⟩
  rw [d2k_mfderiv_eq_fderiv hf, (d2k_opens_symm W b).1, he.fderiv_eq]

theorem d2k_contDiffAt_opens (W : TopologicalSpace.Opens F) {n : WithTop ℕ∞} {f : W → G} {b : W}
    (hf : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, G) n f b) (f' : F → G)
    (hf' : ∀ᶠ t in 𝓝 (b : F), ∀ h : t ∈ W, f ⟨t, h⟩ = f' t) :
    ContDiffAt ℂ n f' b := by
  have he := d2k_opens_eventuallyEq W b f f' hf'
  have h1 := d2k_contDiffAt_chart hf
  rw [(d2k_opens_symm W b).1] at he h1
  exact h1.congr_of_eventuallyEq he.symm

end Opens

section Period

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {g : ℕ}

theorem d2k_filtration_one (P : Fin g → Fin (2 * g) → ℂ) : d2_filtration P 1 = d2_hodgeOne P := by
  simp [d2_filtration]

theorem d2k_isCompl (X : d2_MarkedPeriodFamily E B g) {b₀ b : B}
    (hb : b ∈ d2_chartDomain X b₀) :
    IsCompl (d2_filtration (X.period b) 1)
      ((d2_filtration (X.period b₀) 1).map (sigmaQ (Fin (2 * g) → ℚ))) := by
  have h : b ∈ {b | d2_filtration (X.period b) ∈
      d1_chartDomainSet 1 (d2_filtration (X.period b₀)) 1 1} := interior_subset hb
  have := h 0
  norm_num at this
  exact this

theorem d2k_act_chartPeriod (X : d2_MarkedPeriodFamily E B g) (b₀ b : B)
    (x : ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) :
    d2k_act _ (d2_chartPeriod X b₀ b) ((Module.finBasis ℂ _).equivFun x) =
      (Module.finBasis ℂ _).equivFun
        (d1_graphProjection 1 (d2_filtration (X.period b₀)) (d2_filtration (X.period b)) 1 x) := by
  have h : d2_chartPeriod X b₀ b 0 = LinearMap.toMatrix (Module.finBasis ℂ _)
      (Module.finBasis ℂ _)
      (d1_graphProjection 1 (d2_filtration (X.period b₀)) (d2_filtration (X.period b)) 1) := by
    funext j k
    simp [d2_chartPeriod, d1_chartCoord]
  rw [d2k_act_apply, h, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

theorem d2k_ker_mfderiv (X : d2_MarkedPeriodFamily E B g) (b₀ b : B)
    (hb : b ∈ d2_chartDomain X b₀)
    (hΦ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b) :
    LinearMap.ker (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap =
      LinearMap.ker (d2_kodairaSpencer X b) := by
  set e := extChartAt 𝓘(ℂ, E) b
  set c := (Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))).equivFun
  set W := (d2_filtration (X.period b₀) 1).map (sigmaQ (Fin (2 * g) → ℚ))
  have hP : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ) X.period b :=
    X.holomorphic.mdifferentiableAt (by simp)
  have hev : ∀ᶠ z in 𝓝 (e b), e.symm z ∈ d2_chartDomain X b₀ := by
    apply continuousAt_extChartAt_symm b
    rw [extChartAt_to_inv]
    exact isOpen_interior.mem_nhds hb
  have hspec : ∀ {b'}, b' ∈ d2_chartDomain X b₀ →
      (∀ x, d2k_act _ (d2_chartPeriod X b₀ b') (c x) = c x ↔ x ∈ d2_hodgeOne (X.period b')) ∧
        ∀ w ∈ W, d2k_act _ (d2_chartPeriod X b₀ b') (c w) = 0 := by
    intro b' hb'
    have hs := d2k_graphProjection_spec _ _ (d2k_isCompl X hb')
    rw [d2k_filtration_one] at hs
    refine ⟨fun x ↦ ?_, fun w hw ↦ ?_⟩
    · rw [d2k_act_chartPeriod, c.injective.eq_iff]
      exact hs.1 x
    · rw [d2k_act_chartPeriod, hs.2 w hw, map_zero]
  have key := d2k_fderiv_eq_zero_iff c (d2_chartPeriod X b₀ ∘ e.symm) (X.period ∘ e.symm) (e b)
    (d2k_differentiableAt_chart hΦ) (d2k_differentiableAt_chart hP) d2_evalBilin
    (d2_hodgeOne (X.period b)) W (by simp [e, d2_hodgeOne])
    (by rw [← d2k_filtration_one]; exact (d2k_isCompl X hb).sup_eq_top)
    (hev.mono fun z hz φ ↦ ((hspec hz).1 _).2 (LinearMap.mem_range_self _ φ))
    (hev.mono fun z hz w hw ↦ (hspec hz).2 w hw)
    (by simp only [Function.comp_apply, e, extChartAt_to_inv]; exact (hspec hb).1)
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, d2k_mfderiv_eq_fderiv hΦ,
    key, ← d2k_mfderiv_eq_fderiv hP, LinearMap.ext_iff]
  simp only [d2_kodairaSpencer, LinearMap.comp_apply, LinearMap.compr₂_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.zero_apply]
  rfl

end Period

end HodgeLean.Foundations.Program
