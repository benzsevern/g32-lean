import HodgeLean.Foundations.Program.HurwitzPrymCovRot
import HodgeLean.Foundations.Program.HurwitzPrymCovNormalForm

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: local degree and constancy of the fibre degree

The chart expression of `f` at `x`, transported to a function `ℂ → ℂ` vanishing at `0`, has
analytic order `b4_ramIndex f x`. The normal form `t ↦ t^e` then shows that near `x` every value
`y' ≠ f x` near `f x` has exactly `e_x` preimages, each unramified. With finiteness and
compactness this makes the fibre degree locally constant, hence constant on connected `Y`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology Metric
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Transport

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- A continuous multilinear map on a complex line vanishes iff it vanishes on the diagonal of
a nonzero vector. -/
theorem b4cov_multilinear_eq_zero_iff (hE : Module.finrank ℂ E = 1) {k : ℕ}
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin k ↦ E) E') :
    M = 0 ↔ M (fun _ ↦ b4cov_lineEquiv hE 1) = 0 := by
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  ext m
  have hm : m = fun i ↦ (b4cov_lineEquiv hE).symm (m i) • b4cov_lineEquiv hE 1 := by
    funext i
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  rw [hm, M.map_smul_univ, h, smul_zero]
  rfl

/-- The transported chart function `t ↦ L'⁻¹ (g (z₀ + L t)) - L'⁻¹ (g z₀)`. -/
def b4cov_transport (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (g : E → E') (z₀ : E) : ℂ → ℂ :=
  fun t ↦ (b4cov_lineEquiv hE').symm (g (z₀ + b4cov_lineEquiv hE t)) -
    (b4cov_lineEquiv hE').symm (g z₀)

theorem b4cov_transport_analyticAt (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1) {g : E → E'} {z₀ : E} (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (b4cov_transport hE hE' g z₀) 0 := by
  have hA : AnalyticAt ℂ (fun t : ℂ ↦ z₀ + b4cov_lineEquiv hE t) 0 :=
    analyticAt_const.add ((b4cov_lineEquiv hE).toContinuousLinearMap.analyticAt 0)
  have hg' : AnalyticAt ℂ g ((fun t : ℂ ↦ z₀ + b4cov_lineEquiv hE t) 0) := by simpa using hg
  exact (((b4cov_lineEquiv hE').symm.toContinuousLinearMap.analyticAt _).comp
    (AnalyticAt.comp (g := g) (f := fun t : ℂ ↦ z₀ + b4cov_lineEquiv hE t) hg' hA)).sub
    analyticAt_const

theorem b4cov_transport_zero (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (g : E → E') (z₀ : E) : b4cov_transport hE hE' g z₀ 0 = 0 := by
  simp [b4cov_transport]

/-- Iterated derivatives of the transported function. -/
theorem b4cov_transport_iteratedDeriv (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1) {g : E → E'} {z₀ : E} (hg : AnalyticAt ℂ g z₀) {k : ℕ}
    (hk : k ≠ 0) :
    iteratedDeriv k (b4cov_transport hE hE' g z₀) 0 =
      (b4cov_lineEquiv hE').symm (iteratedFDeriv ℂ k g z₀ (fun _ ↦ b4cov_lineEquiv hE 1)) := by
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  have hA : AnalyticAt ℂ (fun t : ℂ ↦ L'.symm (g (z₀ + L t))) 0 := by
    have hA : AnalyticAt ℂ (fun t : ℂ ↦ z₀ + L t) 0 :=
      analyticAt_const.add (L.toContinuousLinearMap.analyticAt 0)
    have hg' : AnalyticAt ℂ g ((fun t : ℂ ↦ z₀ + L t) 0) := by simpa using hg
    exact (L'.symm.toContinuousLinearMap.analyticAt _).comp
      (AnalyticAt.comp (g := g) (f := fun t : ℂ ↦ z₀ + L t) hg' hA)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℂ k ((fun t : ℂ ↦ L'.symm (g (z₀ + L t))) - fun _ ↦ L'.symm (g z₀)) 0
    (fun _ ↦ 1) = _
  rw [iteratedFDeriv_sub_apply hA.contDiffAt contDiffAt_const, iteratedFDeriv_const_of_ne hk,
    Pi.zero_apply, sub_zero]
  have h1 : (fun t : ℂ ↦ L'.symm (g (z₀ + L t))) = L'.symm ∘ ((fun z ↦ g (z + z₀)) ∘ L) := by
    funext t; simp [add_comm]
  rw [h1, ContinuousLinearEquiv.iteratedFDeriv_comp_left, ← iteratedFDerivWithin_univ,
    show (univ : Set ℂ) = L ⁻¹' univ from rfl,
    L.iteratedFDerivWithin_comp_right _ uniqueDiffOn_univ (mem_univ _), iteratedFDerivWithin_univ,
    iteratedFDeriv_comp_add_right, map_zero, zero_add]
  rfl

/-- **The analytic order of the transported function** is the index of the first nonvanishing
iterated derivative. -/
theorem b4cov_analyticOrderAt_transport (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1) {g : E → E'} {z₀ : E} (hg : AnalyticAt ℂ g z₀) {n : ℕ}
    (hn : 1 ≤ n) (hlow : ∀ k, 1 ≤ k → k < n → iteratedFDeriv ℂ k g z₀ = 0)
    (hne : iteratedFDeriv ℂ n g z₀ ≠ 0) :
    analyticOrderAt (b4cov_transport hE hE' g z₀) 0 = n := by
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (b4cov_transport_analyticAt hE hE' hg)]
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [iteratedDeriv_zero, b4cov_transport_zero]
    · rw [b4cov_transport_iteratedDeriv hE hE' hg hk0.ne', hlow k hk0 hk,
        ContinuousMultilinearMap.zero_apply, map_zero]
  · rw [b4cov_transport_iteratedDeriv hE hE' hg (by omega)]
    intro h
    apply hne
    rw [b4cov_multilinear_eq_zero_iff hE]
    exact (b4cov_lineEquiv hE').symm.injective (h.trans (map_zero _).symm)

/-- The derivative of the transported function. -/
theorem b4cov_transport_deriv (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    {g : E → E'} {z₀ : E} (t : ℂ) (hg : DifferentiableAt ℂ g (z₀ + b4cov_lineEquiv hE t)) :
    deriv (b4cov_transport hE hE' g z₀) t =
      (b4cov_lineEquiv hE').symm (fderiv ℂ g (z₀ + b4cov_lineEquiv hE t) (b4cov_lineEquiv hE 1)) := by
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  have hA : HasDerivAt (fun s : ℂ ↦ z₀ + L s) (L 1) t := by
    have := (L.toContinuousLinearMap.hasFDerivAt (x := t)).hasDerivAt.const_add z₀
    simpa using this
  have h1 := (L'.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hg.hasFDerivAt.comp_hasDerivAt t hA)).sub_const (L'.symm (g z₀))
  exact h1.deriv

end Transport

section Surface

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
/-- Simple points are the points with nonzero derivative. -/
theorem b4cov_ramIndex_eq_one_iff (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x : C) :
    b4_ramIndex E E' f x = 1 ↔ mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 := by
  let s := {n : ℕ | 1 ≤ n ∧ iteratedFDeriv ℂ n
    (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) ≠ 0}
  have hd : iteratedFDeriv ℂ 1
      (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) ≠ 0 ↔
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 := by
    rw [(hf.mdifferentiableAt (by simp)).mfderiv]
    simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
    change iteratedFDeriv ℂ 1 _ _ ≠ 0 ↔ fderiv ℂ _ _ ≠ 0
    rw [← norm_ne_zero_iff, norm_iteratedFDeriv_one, norm_ne_zero_iff]
    exact Iff.rfl
  change sInf s = 1 ↔ _
  constructor
  · intro hs
    have hne : s.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h] at hs
      simp at hs
    have hm := Nat.sInf_mem hne
    rw [hs] at hm
    exact hd.mp hm.2
  · intro h
    have hm : 1 ∈ s := ⟨le_rfl, hd.mpr h⟩
    exact le_antisymm (Nat.sInf_le hm) (le_csInf ⟨1, hm⟩ fun _ hn ↦ hn.1)

/-- The defining properties of the ramification index of a non-constant map. -/
theorem b4cov_ramIndex_spec [ConnectedSpace C] [CompleteSpace E'] (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (x : C) :
    1 ≤ b4_ramIndex E E' f x ∧
      iteratedFDeriv ℂ (b4_ramIndex E E' f x) (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
        (extChartAt 𝓘(ℂ, E) x x) ≠ 0 ∧
      ∀ k, 1 ≤ k → k < b4_ramIndex E E' f x → iteratedFDeriv ℂ k
        (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) = 0 := by
  have hpos := b4cov_ramIndex_pos f hf hnc x
  have hne : {n : ℕ | 1 ≤ n ∧ iteratedFDeriv ℂ n (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f)
      (extChartAt 𝓘(ℂ, E) x x) ≠ 0}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : b4_ramIndex E E' f x = 0 := by rw [b4_ramIndex, h, Nat.sInf_empty]
    omega
  have hm := Nat.sInf_mem hne
  refine ⟨hpos, hm.2, fun k hk hlt ↦ ?_⟩
  have := Nat.notMem_of_lt_sInf hlt
  by_contra h
  exact this ⟨hk, h⟩

/-- **Local degree**: near `x`, every value `y' ≠ f x` near `f x` has exactly `e_x`
preimages, all unramified, and `f x` has only `x`; the neighborhood can be taken inside any given
neighborhood of `x`. -/
theorem b4cov_local_degree [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1) (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (hnc : ∃ x x', f x ≠ f x') (x : C) (N : Set C) (hN : N ∈ 𝓝 x) :
    ∃ U ⊆ N, IsOpen U ∧ x ∈ U ∧ ∃ V ∈ 𝓝 (f x), (∀ x' ∈ U, f x' = f x → x' = x) ∧
      ∀ y' ∈ V, y' ≠ f x → (f ⁻¹' {y'} ∩ U).ncard = b4_ramIndex E E' f x ∧
        ∀ x' ∈ U, f x' = y' → b4_ramIndex E E' f x' = 1 := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  obtain ⟨he1, hne, hlow⟩ := b4cov_ramIndex_spec f hf hnc x
  set φ := extChartAt 𝓘(ℂ, E) x with hφdef
  set ψ := extChartAt 𝓘(ℂ, E') (f x) with hψdef
  set g := writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f with hgdef
  set z₀ := φ x
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  set e := b4_ramIndex E E' f x
  have han := b4cov_analyticOnNhd f hf x
  have hgan : AnalyticAt ℂ g z₀ := han _ (b4cov_mem_good (E' := E') f x)
  set h := b4cov_transport hE hE' g z₀
  have hord : analyticOrderAt h 0 = e := b4cov_analyticOrderAt_transport hE hE' hgan he1 hlow hne
  let O : Set E := b4cov_good E E' f x ∩ (φ.target ∩ φ.symm ⁻¹' interior N)
  have hOo : IsOpen O := (b4cov_good_isOpen f hf.continuous x).inter
    ((continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      isOpen_interior)
  have hz₀O : z₀ ∈ O := by
    refine ⟨b4cov_mem_good f x, mem_extChartAt_target x, ?_⟩
    rw [mem_preimage, extChartAt_to_inv]
    exact mem_interior_iff_mem_nhds.2 hN
  let A : ℂ → E := fun t ↦ z₀ + L t
  have hAc : Continuous A := continuous_const.add L.continuous
  have hA0 : A 0 = z₀ := by simp [A]
  obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.isOpen_iff.1 (hOo.preimage hAc) 0 (by rw [mem_preimage, hA0]; exact hz₀O)
  obtain ⟨r, hr, hrr₀, ρ, hρ, hzero, hcount⟩ :=
    b4cov_count (b4cov_transport_analyticAt hE hE' hgan) he1 hord r₀ hr₀
  let τ : C → ℂ := fun y ↦ L.symm (φ y - z₀)
  have hτA : ∀ y, A (τ y) = φ y := fun y ↦ by simp [A, τ]
  have hτc : ContinuousOn τ φ.source :=
    L.symm.continuous.comp_continuousOn ((continuousOn_extChartAt x).sub continuousOn_const)
  let U : Set C := φ.source ∩ τ ⁻¹' ball 0 r
  have hUo : IsOpen U := hτc.isOpen_inter_preimage (isOpen_extChartAt_source x) isOpen_ball
  have hK1 : ∀ y ∈ U, φ y ∈ O := fun y hy ↦ by
    rw [← hτA]; exact hr₀O (ball_subset_ball hrr₀ hy.2)
  have hK2 : ∀ t ∈ ball (0 : ℂ) r, φ.symm (A t) ∈ U ∧ τ (φ.symm (A t)) = t := by
    intro t ht
    have hAt : A t ∈ O := hr₀O (ball_subset_ball hrr₀ ht)
    have h1 : φ (φ.symm (A t)) = A t := φ.right_inv hAt.2.1
    have h2 : τ (φ.symm (A t)) = t := by simp [τ, h1, A]
    exact ⟨⟨φ.map_target hAt.2.1, by rw [mem_preimage, h2]; exact ht⟩, h2⟩
  have hfU : ∀ y ∈ U, f y ∈ ψ.source := fun y hy ↦ by
    have := (hK1 y hy).1.2
    rwa [mem_preimage, mem_preimage, φ.left_inv hy.1] at this
  have hR : ∀ y ∈ U, h (τ y) = L'.symm (ψ (f y) - ψ (f x)) := by
    intro y hy
    simp only [h, b4cov_transport, map_sub]
    rw [show z₀ + L (τ y) = φ y from hτA y, hgdef, b4cov_written_apply, b4cov_written_apply,
      φ.left_inv hy.1, extChartAt_to_inv]
  refine ⟨U, fun y hy ↦ ?_, hUo, ⟨mem_extChartAt_source x, by simp [τ, z₀]; exact hr⟩, ?_⟩
  · have := (hK1 y hy).2.2
    rw [mem_preimage, φ.left_inv hy.1] at this
    exact interior_subset this
  let σ : Y → ℂ := fun y' ↦ L'.symm (ψ y' - ψ (f x))
  have hσc : ContinuousAt σ (f x) :=
    L'.symm.continuous.continuousAt.comp ((continuousAt_extChartAt (f x)).sub continuousAt_const)
  have hσ0 : σ (f x) = 0 := by simp [σ]
  let V : Set Y := ψ.source ∩ σ ⁻¹' ball 0 ρ
  have hV : V ∈ 𝓝 (f x) := inter_mem (extChartAt_source_mem_nhds (f x))
    (hσc.preimage_mem_nhds (by rw [hσ0]; exact ball_mem_nhds 0 hρ))
  have hτinj : InjOn τ U := by
    intro a ha b hb hab
    have : φ a = φ b := by
      have := congrArg L hab
      simp only [τ, ContinuousLinearEquiv.apply_symm_apply] at this
      exact sub_left_injective this
    exact φ.injOn ha.1 hb.1 this
  refine ⟨V, hV, fun y hy hyx ↦ ?_, fun y' hy' hy'x ↦ ?_⟩
  · have h0 : h (τ y) = 0 := by rw [hR y hy, hyx, sub_self, map_zero]
    have ht := hzero _ hy.2 h0
    have hx0 : τ x = 0 := by simp [τ, z₀]
    exact hτinj hy ⟨mem_extChartAt_source x, by rw [mem_preimage, hx0]; exact mem_ball_self hr⟩
      (ht.trans hx0.symm)
  · have hw0 : σ y' ≠ 0 := by
      intro h0
      apply hy'x
      have : ψ y' = ψ (f x) := by
        have := congrArg L' h0
        simp only [σ, ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
        exact sub_eq_zero.1 this
      exact ψ.injOn hy'.1 (mem_extChartAt_source (f x)) this
    have hwρ : ‖σ y'‖ < ρ := mem_ball_zero_iff.1 hy'.2
    obtain ⟨hcard, hder⟩ := hcount (σ y') hw0 hwρ
    have hfib : ∀ y ∈ U, f y = y' ↔ h (τ y) = σ y' := by
      intro y hy
      rw [hR y hy]
      constructor
      · rintro rfl; rfl
      · intro heq
        have : ψ (f y) = ψ y' := by
          have := congrArg L' heq
          simp only [σ, ContinuousLinearEquiv.apply_symm_apply] at this
          exact sub_left_injective this
        exact ψ.injOn (hfU y hy) hy'.1 this
    have himg : τ '' (f ⁻¹' {y'} ∩ U) = {t ∈ ball (0 : ℂ) r | h t = σ y'} := by
      ext t
      constructor
      · rintro ⟨y, ⟨hyf, hyU⟩, rfl⟩
        exact ⟨hyU.2, (hfib y hyU).1 hyf⟩
      · rintro ⟨ht, htw⟩
        obtain ⟨hU, hτ⟩ := hK2 t ht
        refine ⟨φ.symm (A t), ⟨(hfib _ hU).2 (by rw [hτ]; exact htw), hU⟩, hτ⟩
    refine ⟨?_, fun y hy hyf ↦ ?_⟩
    · rw [← hτinj.mono inter_subset_right |>.ncard_image, himg, hcard]
    · have hdt := hder (τ y) hy.2 ((hfib y hy).1 hyf)
      rw [b4cov_ramIndex_eq_one_iff f hf y]
      intro hm
      rw [b4cov_mfderiv_eq_zero_iff f hf x y hy.1 (hfU y hy)] at hm
      apply hdt
      have hτA' : z₀ + b4cov_lineEquiv hE (τ y) = φ y := hτA y
      rw [b4cov_transport_deriv hE hE' (τ y)
        (by rw [hτA']; exact (han _ (hK1 y hy).1).differentiableAt), hτA', hm]
      simp

/-- **The fibre degree is locally constant.** -/
theorem b4cov_fiberDegree_eventually [T2Space C] [CompactSpace C] [ConnectedSpace C] [T2Space Y]
    (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y : Y) :
    ∀ᶠ y' in 𝓝 y, b4_fiberDegree E E' f y' = b4_fiberDegree E E' f y := by
  classical
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  set F := f ⁻¹' {y}
  have hF : F.Finite := b4cov_fiber_finite hE f hf hnc y
  obtain ⟨S, hS, hSdisj⟩ := hF.t2_separation
  choose U hUS hUo hxU V hV hzero hcount using fun x ↦
    b4cov_local_degree hE hE' f hf hnc x (S x) ((hS x).2.mem_nhds (hS x).1)
  let W : Set C := ⋃ x ∈ F, U x
  have hWo : IsOpen W := isOpen_biUnion fun x _ ↦ hUo x
  let K : Set Y := f '' Wᶜ
  have hKc : IsClosed K := (hWo.isClosed_compl.isCompact.image hf.continuous).isClosed
  have hyK : y ∉ K := by
    rintro ⟨z, hz, hzy⟩
    exact hz (mem_biUnion (show z ∈ F from hzy) (hxU z))
  have hVall : (⋂ x ∈ F, V x) ∈ 𝓝 y := (Filter.biInter_mem hF).2 fun x hx ↦ by
    have := hV x
    rwa [show f x = y from hx] at this
  filter_upwards [hKc.isOpen_compl.mem_nhds hyK, hVall] with y' hy'K hy'V
  by_cases hyy : y' = y
  · rw [hyy]
  have hsub : f ⁻¹' {y'} = ⋃ x ∈ F, (f ⁻¹' {y'} ∩ U x) := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, exists_and_left, exists_prop]
    constructor
    · intro hz
      by_contra hno
      apply hy'K
      refine ⟨z, fun hzW ↦ ?_, hz⟩
      obtain ⟨x, hxF, hzx⟩ := mem_iUnion₂.1 hzW
      exact hno ⟨hz, x, hxF, hzx⟩
    · exact fun h ↦ h.1
  have hdisj : F.PairwiseDisjoint fun x ↦ f ⁻¹' {y'} ∩ U x :=
    fun a ha b hb hab ↦ ((hSdisj ha hb hab).mono (inter_subset_right.trans (hUS a))
      (inter_subset_right.trans (hUS b)))
  have hfin : ∀ x ∈ F, (f ⁻¹' {y'} ∩ U x).Finite := fun x _ ↦
    (b4cov_fiber_finite hE f hf hnc y').subset inter_subset_left
  rw [b4_fiberDegree, hsub, finsum_mem_biUnion hdisj hF hfin, b4_fiberDegree]
  refine finsum_mem_congr rfl fun x hx ↦ ?_
  have hfx : f x = y := hx
  have hy'Vx : y' ∈ V x := mem_iInter₂.1 hy'V x hx
  have hne : y' ≠ f x := hfx ▸ hyy
  obtain ⟨hcard, hram⟩ := hcount x y' hy'Vx hne
  rw [← hcard, ← finsum_one]
  exact finsum_mem_congr rfl fun z hz ↦ hram z hz.2 hz.1

/-- **The fibre degree is constant** on a connected target. -/
theorem b4cov_fiberDegree_eq [T2Space C] [CompactSpace C] [ConnectedSpace C] [T2Space Y]
    [ConnectedSpace Y] (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y y' : Y) :
    b4_fiberDegree E E' f y = b4_fiberDegree E E' f y' := by
  have hlc : IsLocallyConstant (b4_fiberDegree E E' f) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun y ↦
      b4cov_fiberDegree_eventually hE hE' f hf hnc y
  exact hlc.apply_eq_of_preconnectedSpace y y'

end Surface

end HodgeLean.Foundations.Program
