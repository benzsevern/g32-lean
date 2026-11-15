import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian12
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.TietzeExtension

/-! # Singular restriction: local analytic and geometric primitives

Implications from reduced local factorization and from explicit continuous or
smooth map data. These are intermediate constructions for the critical cover
and complement filling. The global cover and cohomological endpoints require
further work. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped ContDiff
open Set Filter Topology TopologicalSpace CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- On the regular part of a factor, critical zeros are precisely intersections
with the residual factor, which cannot vanish on the whole factor germ.
Source: `bh12_no_critical_hypersurface`, the analytic product rule, and
Gunning--Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem bh14_factor_intersection_aux (n : ℕ) (p : Fin n → ℂ)
    (f g h : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hi : IsIrreducibleAt g p) (hd : fderiv ℂ g p ≠ 0)
    (heq : f =ᶠ[𝓝 p] fun z ↦ g z * h z) :
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, g z = 0 → (f z = 0 ∧ fderiv ℂ f z = 0 ↔ h z = 0)) ∧
    ¬ (∀ᶠ z in 𝓝 p, g z = 0 → h z = 0) := by
  have hmain : ∀ᶠ z in 𝓝 p,
      g z = 0 → (f z = 0 ∧ fderiv ℂ f z = 0 ↔ h z = 0) := by
    filter_upwards [heq.eventuallyEq_nhds, hg.eventually_analyticAt,
      hh.eventually_analyticAt, hg.fderiv.continuousAt.eventually_ne hd]
      with z heqz hgz hhz hdz
    intro hgz0
    have hval : f z = g z * h z := heqz.self_of_nhds
    have hder : fderiv ℂ f z =
        g z • fderiv ℂ h z + h z • fderiv ℂ g z := by
      rw [heqz.fderiv_eq (𝕜 := ℂ)]
      exact fderiv_fun_mul hgz.differentiableAt hhz.differentiableAt
    constructor
    · rintro ⟨_, hz⟩
      have hsmul : h z • fderiv ℂ g z = 0 := by
        rw [hder] at hz
        rw [hgz0] at hz
        have hzero : (0 : ℂ) • fderiv ℂ h z = 0 := by
          ext v
          simp
        rwa [hzero, zero_add] at hz
      by_contra hhn
      exact (smul_ne_zero hhn hdz) hsmul
    · intro hz
      constructor
      · simpa [hval, hgz0]
      · rw [hder]
        ext v
        simp [hgz0, hz]
  constructor
  · obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.mp hmain
    exact ⟨W, hWo, hpW, fun z hz ↦ hWsub hz⟩
  · intro hhzero
    apply bh12_no_critical_hypersurface n p f g hf hg hred hi
    filter_upwards [hmain, hhzero] with z hz hh0
    intro hgz0
    exact (hz hgz0).mpr (hh0 hgz0)

/-- Approximate prescribed continuous sphere data by a globally smooth vector-valued map.
Source: `ContinuousMap.exists_restrict_eq`, coordinatewise Tietze extension, and
`Continuous.exists_contDiff_approx`. -/
theorem bh14_sphere_approximation_aux (n k : ℕ)
    (u : (Fin (k + 1) → ℝ) → (Fin n → ℂ))
    (hu : ContinuousOn u (Metric.sphere 0 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ), ContDiff ℝ ∞ v ∧
      ∀ z ∈ Metric.sphere 0 1, dist (v z) (u z) < ε := by
  let s : Set (Fin (k + 1) → ℝ) := Metric.sphere 0 1
  let u' : C(s, Fin n → ℂ) :=
    ⟨fun z ↦ u z, continuousOn_iff_continuous_restrict.mp hu⟩
  obtain ⟨f, hf⟩ := u'.exists_restrict_eq Metric.isClosed_sphere
  obtain ⟨v, hv, hvf, -⟩ := f.continuous.exists_contDiff_approx (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : Fin (k + 1) → ℝ ↦ ε)) (fun _ ↦ hε)
  refine ⟨v, hv, fun z hz ↦ ?_⟩
  have hfz : f z = u z := congrFun (congrArg DFunLike.coe hf) ⟨z, hz⟩
  calc
    dist (v z) (u z) = dist (v z) (f z) := congrArg (dist (v z)) hfz.symm
    _ < ε := hvf z

/-- Small translations avoid a countable differentiable cover when each incidence
parameter space has smaller real dimension than the target.
Source: `DifferentiableOn.dimH_image_le`, `dimH_iUnion`,
`Real.dimH_univ_eq_finrank`, and `dense_compl_of_dimH_lt_finrank`. -/
theorem bh14_small_translation_aux (n m : ℕ)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j)) (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → 2 * d j + m < 2 * n)
    (v : (Fin m → ℝ) → (Fin n → ℂ)) (hv : ContDiff ℝ 1 v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Fin n → ℂ, ‖a‖ < ε ∧
      ∀ z ∈ Metric.closedBall (0 : Fin m → ℝ) 1,
        v z + a ∉ ⋃ j, g j '' U j := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, ?_, ?_⟩
    · change ‖(0 : Fin 0 → ℂ)‖ < ε
      rw [norm_zero]
      exact hε
    · intro z hz hmem
      rw [mem_iUnion] at hmem
      obtain ⟨j, u, hu, heq⟩ := hmem
      have := hd j ⟨u, hu⟩
      omega
  let I : ∀ j, ((Fin (d j) → ℂ) × (Fin m → ℝ)) → (Fin n → ℂ) :=
    fun j q ↦ g j q.1 - v q.2
  let D : ∀ j, Set ((Fin (d j) → ℂ) × (Fin m → ℝ)) :=
    fun j ↦ U j ×ˢ Metric.closedBall 0 1
  have hdiff : ∀ j, DifferentiableOn ℝ (I j) (D j) := by
    intro j
    apply DifferentiableOn.sub
    · exact ((hg j).restrictScalars (𝕜 := ℝ)).comp
        (fun q hq ↦ differentiableWithinAt_fst) (fun q hq ↦ hq.1)
    · exact hv.differentiable_one.comp_differentiableOn differentiableOn_snd
  have hdim_source : ∀ j, (U j).Nonempty → dimH (D j) ≤ (2 * d j + m : ℕ) := by
    intro j hj
    calc
      dimH (D j) ≤ dimH (univ : Set ((Fin (d j) → ℂ) × (Fin m → ℝ))) :=
        dimH_mono (subset_univ _)
      _ = (2 * d j + m : ℕ) := by
        rw [Real.dimH_univ_eq_finrank, Module.finrank_prod,
          Module.finrank_pi_fintype, Module.finrank_pi_fintype]
        simp [Complex.finrank_real_complex, Nat.mul_comm]
  have hdim_image : ∀ j, dimH (I j '' D j) ≤ (2 * n - 1 : ℕ) := by
    intro j
    by_cases hj : (U j).Nonempty
    · exact (hdiff j).dimH_image_le |>.trans ((hdim_source j hj).trans (by
        exact_mod_cast (show 2 * d j + m ≤ 2 * n - 1 by have := hd j hj; omega)))
    · have hUempty : U j = ∅ := not_nonempty_iff_eq_empty.mp hj
      simp [D, hUempty]
  have hdim_union : dimH (⋃ j, I j '' D j) ≤ (2 * n - 1 : ℕ) := by
    rw [dimH_iUnion]
    exact iSup_le hdim_image
  have hlt : dimH (⋃ j, I j '' D j) < Module.finrank ℝ (Fin n → ℂ) := by
    apply hdim_union.trans_lt
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    exact_mod_cast (show 2 * n - 1 < n * 2 by omega)
  have hdense : Dense (⋃ j, I j '' D j)ᶜ := dense_compl_of_dimH_lt_finrank hlt
  obtain ⟨a, ha_bad, ha_ball⟩ := hdense.exists_mem_open
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Fin n → ℂ) ε))
    (Metric.nonempty_ball.2 hε)
  refine ⟨a, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right] using ha_ball
  · intro z hz hmem
    rw [mem_iUnion] at hmem
    obtain ⟨j, u, hu, heq⟩ := hmem
    apply ha_bad
    apply mem_iUnion_of_mem j
    refine ⟨(u, z), ⟨hu, hz⟩, ?_⟩
    dsimp [I]
    rw [sub_eq_iff_eq_add, add_comm]
    exact heq

/-- A uniform boundary tolerance permits restoring exact continuous sphere data
by a collar inside the prescribed open set.
Source: compactness of the sphere, positive distance to a closed complement,
and the radial collar construction in Hatcher, Algebraic Topology, §0 (homotopy extension). -/
theorem bh14_collar_restoration_aux (n k : ℕ) (U : Set (Fin n → ℂ))
    (hU : IsOpen U) (u : (Fin (k + 1) → ℝ) → (Fin n → ℂ))
    (hu : ContinuousOn u (Metric.sphere 0 1)) (huU : MapsTo u (Metric.sphere 0 1) U) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn v (Metric.closedBall 0 1) →
        MapsTo v (Metric.closedBall 0 1) U →
        (∀ z ∈ Metric.sphere 0 1, dist (v z) (u z) < ε) →
        ∃ w : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn w (Metric.closedBall 0 1) ∧
          MapsTo w (Metric.closedBall 0 1) U ∧
          ∀ z ∈ Metric.sphere 0 1, w z = u z := by
  let S := u '' Metric.sphere (0 : Fin (k + 1) → ℝ) 1
  have hS : IsCompact S :=
    (isCompact_sphere (0 : Fin (k + 1) → ℝ) 1).image_of_continuousOn hu
  have hSU : S ⊆ U := image_subset_iff.2 huU
  obtain ⟨ε, hε, hεU⟩ := hS.exists_cthickening_subset_open hU hSU
  refine ⟨ε, hε, ?_⟩
  intro v hv hvU hvnear
  let inner : (Fin (k + 1) → ℝ) → (Fin n → ℂ) := fun z ↦ v ((2 : ℝ) • z)
  let radial : (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ) :=
    fun z ↦ ‖z‖⁻¹ • z
  let outer : (Fin (k + 1) → ℝ) → (Fin n → ℂ) := fun z ↦
    u (radial z) + (2 - 2 * ‖z‖) • (v (radial z) - u (radial z))
  let A : Set (Fin (k + 1) → ℝ) := {z | ‖z‖ ≤ 1 / 2}
  let B : Set (Fin (k + 1) → ℝ) := {z | 1 / 2 ≤ ‖z‖}
  let w : (Fin (k + 1) → ℝ) → (Fin n → ℂ) := fun z ↦
    if z ∈ A then inner z else outer z
  have hAclosed : IsClosed A := isClosed_le continuous_norm continuous_const
  have hrad_sphere : ∀ z, z ∉ A → radial z ∈ Metric.sphere 0 1 := by
    intro z hz
    have hn : ‖z‖ ≠ 0 := by
      intro hn
      apply hz
      simp [A, hn]
    simp [radial, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, hn,
      abs_inv, abs_norm]
  have hrad_cont : ContinuousOn radial B := by
    apply (continuousOn_id.norm.inv₀ ?_).smul continuousOn_id
    intro z hz hn
    have hn' : ‖z‖ = 0 := by simpa using hn
    change 1 / 2 ≤ ‖z‖ at hz
    rw [hn'] at hz
    norm_num at hz
  have hrad_sphere_B : ∀ z ∈ B, radial z ∈ Metric.sphere 0 1 := by
    intro z hz
    have hn0 : ‖z‖ ≠ 0 := by
      intro hn
      have : (1 / 2 : ℝ) ≤ 0 := by simpa [B, hn] using hz
      norm_num at this
    simp [radial, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, hn0]
  have houter_cont : ContinuousOn outer B := by
    have hur : ContinuousOn (fun z ↦ u (radial z)) B :=
      hu.comp hrad_cont hrad_sphere_B
    have hvr : ContinuousOn (fun z ↦ v (radial z)) B :=
      hv.comp hrad_cont (fun z hz ↦ Metric.sphere_subset_closedBall (hrad_sphere_B z hz))
    exact hur.add
      ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id.norm)).smul
        (hvr.sub hur))
  have hinner_cont : ContinuousOn inner (Metric.closedBall 0 1 ∩ closure A) := by
    change ContinuousOn (fun z ↦ v ((2 : ℝ) • z)) _
    have hscale : Continuous (fun z : Fin (k + 1) → ℝ ↦ (2 : ℝ) • z) :=
      continuous_const_smul (2 : ℝ)
    have hcomp : ContinuousOn (v ∘ fun z ↦ (2 : ℝ) • z)
        (Metric.closedBall 0 1 ∩ closure A) :=
      hv.comp hscale.continuousOn (fun z hz ↦ by
        rcases hz with ⟨hzball, hzcl⟩
        have hza : z ∈ A := hAclosed.closure_subset hzcl
        simpa [Metric.mem_closedBall, dist_zero_right, norm_smul] using
          (mul_le_mul_of_nonneg_left hza (by norm_num : (0 : ℝ) ≤ 2)))
    exact hcomp.congr (fun z hz ↦ rfl)
  refine ⟨w, ?_, ?_, ?_⟩
  · apply ContinuousOn.piecewise
    · intro z hz
      have hn : ‖z‖ = 1 / 2 :=
        frontier_le_subset_eq continuous_norm continuous_const hz.2
      have hn0 : ‖z‖ ≠ 0 := by rw [hn]; norm_num
      change v ((2 : ℝ) • z) = u (‖z‖⁻¹ • z) + (2 - 2 * ‖z‖) •
        (v (‖z‖⁻¹ • z) - u (‖z‖⁻¹ • z))
      rw [hn]
      norm_num
    · exact hinner_cont
    · exact houter_cont.mono (inter_subset_right.trans <| closure_minimal (by
        intro z hz
        simp only [A, B, mem_compl_iff, mem_setOf_eq] at hz ⊢
        exact le_of_not_ge hz) (isClosed_le continuous_const continuous_norm))
  · intro z hz
    by_cases hzi : z ∈ A
    · simp only [w, hzi]
      exact hvU (by
        simpa [Metric.mem_closedBall, dist_zero_right, norm_smul] using
          (mul_le_mul_of_nonneg_left hzi (by norm_num : (0 : ℝ) ≤ 2)))
    · have hr := hrad_sphere z hzi
      have hnv := hvnear _ hr
      have hzU : u (radial z) ∈ S := ⟨radial z, hr, rfl⟩
      have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have hzhalf : 1 / 2 < ‖z‖ := lt_of_not_ge hzi
      have hc0 : 0 ≤ 2 - 2 * ‖z‖ := by linarith
      have hc1 : 2 - 2 * ‖z‖ ≤ 1 := by linarith
      apply hεU
      apply (Metric.closedBall_subset_cthickening_singleton (u (radial z)) ε).trans
        (Metric.cthickening_subset_of_subset ε (singleton_subset_iff.mpr hzU))
      simp only [w, hzi]
      rw [Metric.mem_closedBall]
      calc
        dist (outer z) (u (radial z)) = (2 - 2 * ‖z‖) *
            dist (v (radial z)) (u (radial z)) := by
          simp [outer, dist_eq_norm, norm_smul, abs_of_nonneg hc0]
        _ ≤ dist (v (radial z)) (u (radial z)) :=
          mul_le_of_le_one_left (dist_nonneg) hc1
        _ ≤ ε := hnv.le
  · intro z hz
    have hn : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzA : z ∉ A := by simp [A, hn]; norm_num
    simp [w, hzA, outer, radial, hn]

/-- The ball and simplex models have a homeomorphism carrying sphere to boundary.
Source: `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`, applied
in affine coordinates on the simplex, and Hatcher, Algebraic Topology, §2.1. -/
theorem bh14_simplex_ball_aux (k : ℕ) :
    ∃ e : (Metric.closedBall (0 : Fin (k + 1) → ℝ) 1) ≃ₜ
      (Convexity.StdSimplex ℝ (Fin (k + 2))),
      ∀ z, (z.1 ∈ Metric.sphere (0 : Fin (k + 1) → ℝ) 1 ↔
        ∃ i : Fin (k + 2), (e z).weights i = 0) := by
  classical
  let E := Fin (k + 1) → ℝ
  have hcard : Fintype.card (Fin (k + 2)) = Module.finrank ℝ E + 1 := by
    simp [E]
  let b : AffineBasis (Fin (k + 2)) ℝ E :=
    Classical.choice (AffineBasis.exists_affineBasis_of_finiteDimensional hcard)
  let s : Set E := _root_.convexHull ℝ (Set.range b)
  have hscompact : IsCompact s := by
    exact Set.Finite.isCompact_convexHull ℝ (Set.finite_range b)
  have hsclosed : IsClosed s := hscompact.isClosed
  have hsconvex : Convex ℝ s := convex_convexHull ℝ _
  have hsinterior : (interior s).Nonempty := by
    exact ⟨Finset.centroid ℝ Finset.univ b, b.centroid_mem_interior_convexHull⟩
  obtain ⟨h, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hsconvex hsinterior hscompact.isBounded
  have hsimage : h '' s = Metric.closedBall (0 : E) 1 := by
    simpa only [hsclosed.closure_eq] using hclosure
  let r : s ≃ₜ Metric.closedBall (0 : E) 1 :=
    (h.image s).trans (Homeomorph.setCongr hsimage)
  let f : Convexity.StdSimplex ℝ (Fin (k + 2)) → s := fun w =>
    ⟨Finset.univ.affineCombination ℝ b (fun i => w.weights i), by
      change Finset.univ.affineCombination ℝ b (fun i => w.weights i) ∈
        _root_.convexHull ℝ (Set.range b)
      rw [b.convexHull_eq_nonneg_coord]
      intro i
      rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) w.total_of_fintype]
      exact w.weights_nonneg i⟩
  have hfbij : Function.Bijective f := by
    constructor
    · intro w₁ w₂ hw
      apply Convexity.StdSimplex.weights_inj.mp
      ext i
      have hi := congrArg (fun x : s => b.coord i x.1) hw
      calc
        w₁.weights i = b.coord i (f w₁).1 := by
          change _ = b.coord i (Finset.univ.affineCombination ℝ b fun i => w₁.weights i)
          rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) w₁.total_of_fintype]
        _ = b.coord i (f w₂).1 := hi
        _ = w₂.weights i := by
          change b.coord i (Finset.univ.affineCombination ℝ b fun i => w₂.weights i) = _
          rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) w₂.total_of_fintype]
    · intro x
      have hx : ∀ i, 0 ≤ b.coord i x.1 := by
        have hx' := x.2
        change x.1 ∈ _root_.convexHull ℝ (Set.range b) at hx'
        rw [b.convexHull_eq_nonneg_coord] at hx'
        exact hx'
      let w : Convexity.StdSimplex ℝ (Fin (k + 2)) :=
        { weights := Finsupp.equivFunOnFinite.symm (fun i => b.coord i x.1)
          nonneg := by intro i; simpa using hx i
          total := by simp [Finsupp.sum_fintype, b.sum_coord_apply_eq_one x.1] }
      refine ⟨w, Subtype.ext ?_⟩
      apply b.ext_elem
      intro i
      rw [show (f w).1 = Finset.univ.affineCombination ℝ b (fun i => w.weights i) by rfl,
        b.coord_apply_combination_of_mem (Finset.mem_univ i) w.total_of_fintype]
      simp [w]
  let qEquiv : Convexity.StdSimplex ℝ (Fin (k + 2)) ≃ s := Equiv.ofBijective f hfbij
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    have heq : (fun w : Convexity.StdSimplex ℝ (Fin (k + 2)) =>
        Finset.univ.affineCombination ℝ b (fun i => w.weights i)) =
        (fun w => ∑ i, w.weights i • b i) := by
      funext w
      rw [Finset.univ.affineCombination_eq_linear_combination _ _ w.total_of_fintype]
    rw [heq]
    fun_prop
  have hqcont : Continuous qEquiv := by simpa [qEquiv] using hfcont
  let q : Convexity.StdSimplex ℝ (Fin (k + 2)) ≃ₜ s := hqcont.homeoOfEquivCompactToT2
  let e : Metric.closedBall (0 : E) 1 ≃ₜ Convexity.StdSimplex ℝ (Fin (k + 2)) :=
    r.symm.trans q.symm
  refine ⟨e, ?_⟩
  intro z
  have hqweights (x : s) (i : Fin (k + 2)) :
      (q.symm x).weights i = b.coord i x.1 := by
    have hfx : f (q.symm x) = x := by
      change q (q.symm x) = x
      exact q.apply_symm_apply x
    have hi := congrArg (fun y : s => b.coord i y.1) hfx
    calc
      (q.symm x).weights i = b.coord i (f (q.symm x)).1 := by
        change _ = b.coord i (Finset.univ.affineCombination ℝ b fun i => (q.symm x).weights i)
        rw [b.coord_apply_combination_of_mem (Finset.mem_univ i)
          (q.symm x).total_of_fintype]
      _ = b.coord i x.1 := hi
  have hfront (x : s) : x.1 ∈ frontier s ↔ ∃ i, b.coord i x.1 = 0 := by
    rw [frontier, hsclosed.closure_eq, b.interior_convexHull]
    constructor
    · rintro ⟨_, hx⟩
      change ¬ ∀ i, 0 < b.coord i x.1 at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      have hxnonneg : ∀ j, 0 ≤ b.coord j x.1 := by
        have hx' := x.2
        change x.1 ∈ _root_.convexHull ℝ (Set.range b) at hx'
        rw [b.convexHull_eq_nonneg_coord] at hx'
        exact hx'
      exact ⟨i, le_antisymm hi (hxnonneg i)⟩
    · rintro ⟨i, hi⟩
      refine ⟨x.2, ?_⟩
      change ¬ ∀ i, 0 < b.coord i x.1
      intro hall
      exact (ne_of_gt (hall i)) hi
  rw [show (∃ i, (e z).weights i = 0) ↔ (r.symm z).1 ∈ frontier s by
    simp only [e, Homeomorph.trans_apply]
    rw [hfront]
    exact exists_congr fun i => by rw [hqweights]]
  constructor
  · intro hz
    have hzimg : z.1 ∈ h '' frontier s := by simpa only [hfrontier] using hz
    obtain ⟨x, hx, hxeq⟩ := hzimg
    have hr : r ⟨x, hsclosed.closure_eq ▸ frontier_subset_closure hx⟩ = z := by
      apply Subtype.ext
      exact hxeq
    rw [← hr, r.symm_apply_apply]
    exact hx
  · intro hx
    have hmem : h (r.symm z).1 ∈ Metric.sphere (0 : E) 1 := by
      rw [← hfrontier]
      exact ⟨(r.symm z).1, hx, rfl⟩
    have hrval : h (r.symm z).1 = z.1 := congrArg Subtype.val (r.apply_symm_apply z)
    rwa [hrval] at hmem

/-- A countable cover of real codimension at least four permits exact sphere
fillings in its open complement in dimensions zero through two.
Source: `bh14_sphere_approximation_aux`, `bh14_small_translation_aux`, and
`bh14_collar_restoration_aux`. -/
theorem bh14_cover_sphere_filling_aux (n : ℕ) (O : Set (Fin n → ℂ))
    (hO : IsOpen O) (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j)) (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j)
    (k : ℕ) (hk : k ≤ 2)
    (u : (Fin (k + 1) → ℝ) → (Fin n → ℂ))
    (hu : ContinuousOn u (Metric.sphere 0 1)) (huO : MapsTo u (Metric.sphere 0 1) O) :
    ∃ w : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
      ContinuousOn w (Metric.closedBall 0 1) ∧ MapsTo w (Metric.closedBall 0 1) O ∧
      ∀ z ∈ Metric.sphere 0 1, w z = u z := by
  obtain ⟨ε, hε, hrestore⟩ := bh14_collar_restoration_aux n k O hO u hu huO
  obtain ⟨v, hv, hnear⟩ := bh14_sphere_approximation_aux n k u hu (ε / 2) (by linarith)
  have hdim : ∀ j, (U j).Nonempty → 2 * d j + (k + 1) < 2 * n := by
    intro j hj
    have := hd j hj
    omega
  obtain ⟨a, ha, havoid⟩ := bh14_small_translation_aux n (k + 1) d U g hU hg hdim
    v (hv.of_le (by simp)) (ε / 2) (by linarith)
  apply hrestore (fun z ↦ v z + a) (hv.continuous.add continuous_const).continuousOn
  · intro z hz
    by_contra h
    exact havoid z hz (hcover ▸ h)
  · intro z hz
    calc
      dist (v z + a) (u z) ≤ dist (v z + a) (v z) + dist (v z) (u z) :=
        dist_triangle _ _ _
      _ = ‖a‖ + dist (v z) (u z) := by simp only [dist_eq_norm, add_sub_cancel_left]
      _ < ε := by have := hnear z hz; linarith

/-- Sphere filling supplies an extension of the entire compatible simplex boundary.
This is a geometric intermediate for building cones on singular simplices.
Source: `bh14_simplex_ball` and Hatcher, Algebraic Topology, §2.1 (singular simplices). -/
theorem bh14_simplex_extension_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (hne : (U : Set (Fin n → ℂ)).Nonempty) (k : ℕ) (hk : k ≤ 2)
    (hfill : ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
      ContinuousOn u (Metric.sphere 0 1) →
      MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
      ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn v (Metric.closedBall 0 1) ∧
        MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
        ∀ z ∈ Metric.sphere 0 1, v z = u z)
    (u : C({x : Convexity.StdSimplex ℝ (Fin (k + 2)) | ∃ i, x.weights i = 0}, U)) :
    ∃ v : C(Convexity.StdSimplex ℝ (Fin (k + 2)), U), ∀ z, v z.1 = u z :=
  by
  classical
  obtain ⟨e, he⟩ := bh14_simplex_ball_aux k
  let b : (Fin (k + 1) → ℝ) → (Fin n → ℂ) := fun x ↦
    if hx : x ∈ Metric.sphere (0 : Fin (k + 1) → ℝ) 1 then
      (u ⟨e ⟨x, Metric.sphere_subset_closedBall hx⟩, (he _).mp hx⟩ : U)
    else hne.some
  have hb : ContinuousOn b (Metric.sphere (0 : Fin (k + 1) → ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : Metric.sphere (0 : Fin (k + 1) → ℝ) 1 ↦
        (u ⟨e ⟨x.1, Metric.sphere_subset_closedBall x.2⟩,
          (he ⟨x.1, Metric.sphere_subset_closedBall x.2⟩).mp x.2⟩ : U).1) := by
      fun_prop
    apply hc.congr
    intro x
    change _ = b x.1
    simp only [b, dif_pos x.property]
  have hbU : MapsTo b (Metric.sphere (0 : Fin (k + 1) → ℝ) 1) (U : Set (Fin n → ℂ)) := by
    intro x hx
    simp only [b, dif_pos hx]
    exact (u ⟨e ⟨x, Metric.sphere_subset_closedBall hx⟩, (he _).mp hx⟩).property
  obtain ⟨w, hw, hwU, hwb⟩ := hfill b hb hbU
  let v : C(Convexity.StdSimplex ℝ (Fin (k + 2)), U) :=
    ⟨fun x ↦ ⟨w (e.symm x), hwU (e.symm x).property⟩,
      (hw.comp_continuous
        (continuous_subtype_val.comp e.symm.continuous)
        (fun x : Convexity.StdSimplex ℝ (Fin (k + 2)) ↦ (e.symm x).property)).subtype_mk _⟩
  refine ⟨v, ?_⟩
  intro z
  have hzboundary : ∃ i, (e (e.symm z.1)).weights i = 0 := by
    rw [e.apply_symm_apply]
    exact z.property
  have hz : (e.symm z.1 : Fin (k + 1) → ℝ) ∈ Metric.sphere 0 1 :=
    (he (e.symm z.1)).mpr hzboundary
  apply Subtype.ext
  change w (e.symm z.1) = (u z).1
  rw [hwb _ hz]
  simp only [b, dif_pos hz]
  exact congrArg (fun y ↦ (u y).1) (Subtype.ext (e.apply_symm_apply z.1))

end HodgeLean.Adapters
