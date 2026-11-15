import HodgeLean.Foundations.AnalyticGermRSAssemblyDefs
import HodgeLean.Foundations.AnalyticGermLyingOver
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.DerivedSet
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Module.Submodule.Union

/-! # Homogeneous cone projection and vertex extension

Implication from punctured homogeneous analytic cone data to a finite pure
cover of the cone, from a pure cone to a surjective finite proper whole-cone
projection, and from such a projection to vertex analyticity, glued over the
finite cover. The six confinement and sheet interfaces and the attained
dimension projection are preserved.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open scoped NNReal ENNReal MeasureTheory
namespace HodgeLean.Foundations

private theorem adim9_closed_insert_zero_of_closed_punctured {N : Type*}
    [NormedAddCommGroup N] (C : Set N)
    (hclosed : IsClosed {z : {z : N // z ≠ 0} | z.val ∈ C}) :
    IsClosed (insert 0 C) := by
  rw [isClosed_iff_clusterPt]
  intro x hx
  by_cases hx0 : x = 0
  · exact hx0 ▸ mem_insert 0 C
  · have hopen : IsOpen {z : N | z ≠ 0} := isOpen_ne
    have hsubopen : IsOpen
        ({z : {z : N // z ≠ 0} | z.val ∉ C}) := hclosed.isOpen_compl
    by_contra hxC
    have hxnot : x ∉ insert 0 C := by simpa [hx0] using hxC
    have hxsub : (⟨x, hx0⟩ : {z : N // z ≠ 0}) ∈
        {z : {z : N // z ≠ 0} | z.val ∉ C} := by simpa [hx0] using hxnot
    obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp hsubopen
    have hxV : x ∈ V := by
      have : (⟨x, hx0⟩ : {z : N // z ≠ 0}) ∈ Subtype.val ⁻¹' V := by
        rw [hV]
        exact hxsub
      exact this
    have hVn : V ∩ {z : N | z ≠ 0} ∈ nhds x :=
      (hVo.inter hopen).mem_nhds ⟨hxV, hx0⟩
    have hfreq := hx.frequently hVn
    obtain ⟨y, hyins, hyV, hy0⟩ := Filter.frequently_principal.mp hfreq
    have hySub : (⟨y, hy0⟩ : {z : N // z ≠ 0}) ∈
        {z : {z : N // z ≠ 0} | z.val ∉ C} := by
      rw [← hV]
      exact hyV
    rcases hyins with (rfl | hyC)
    · exact hy0 rfl
    · exact hySub hyC

private theorem adim9_local_insert_zero_away (n : ℕ) (C : Set (Fin n → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (x : Fin n → ℂ) (hx : x ∈ insert 0 C) (hx0 : x ≠ 0) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ chartAt (Fin n → ℂ) x x ∈ U ∧
      U ⊆ (chartAt (Fin n → ℂ) x).target ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, ((chartAt (Fin n → ℂ) x).symm z ∈ insert 0 C ↔
          ∀ j, f j z = 0) := by
  have hxC : x ∈ C := by rcases hx with (rfl | hxC) <;> simp_all
  obtain ⟨U, hUo, hxU, hUnz, m, f, hf, hCf⟩ := hloc x hxC
  refine ⟨U, hUo, ?_, ?_, m, f, hf, ?_⟩
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hxU
  · simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_target, subset_univ]
  · intro z hz
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq]
    rw [mem_insert_iff, or_iff_right (hUnz hz), hCf z hz]

private theorem adim9_closed_analytic_of_vertex_equations (n : ℕ)
    (C : Set (Fin n → ℂ))
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ C})
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hvertex : ∃ U : Set (Fin n → ℂ), IsOpen U ∧
      chartAt (Fin n → ℂ) (0 : Fin n → ℂ) 0 ∈ U ∧
      U ⊆ (chartAt (Fin n → ℂ) (0 : Fin n → ℂ)).target ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, ((chartAt (Fin n → ℂ) (0 : Fin n → ℂ)).symm z ∈ insert 0 C ↔
          ∀ j, f j z = 0)) :
    IsClosedAnalytic (Fin n → ℂ) (insert 0 C) := by
  refine ⟨adim9_closed_insert_zero_of_closed_punctured C hclosed, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · simpa only [hx0] using hvertex
  · exact adim9_local_insert_zero_away n C hloc x hx hx0

private theorem adim9_eqOn_of_analytic_mapsTo_max
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (K : Set E) (f : E → ℂ) (c : E)
    (hU : IsOpen U) (hconn : IsPreconnected U) (hc : c ∈ U)
    (hf : AnalyticOnNhd ℂ f U) (hUK : U ⊆ K)
    (hmax : ∀ z ∈ K, ‖f z‖ ≤ ‖f c‖) :
    Set.EqOn f (Function.const E (f c)) U := by
  apply Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn hU hf.differentiableOn hc
  intro z hz
  exact hmax z (hUK hz)

private theorem adim9_exists_linear_norm_max {n : ℕ} {K : Set (Fin n → ℂ)}
    (hK : IsCompact K) (hne : K.Nonempty) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) :
    ∃ x ∈ K, ∀ z ∈ K, ‖ℓ z‖ ≤ ‖ℓ x‖ := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne ℓ.continuous.continuousOn.norm
  exact ⟨x, hx, fun z hz ↦ hmax hz⟩

/-- A Euclidean norm maximizer forces every analytic disc through it in the compact
set to be constant. The point is chosen before any local projection. -/
private theorem adim9_exists_disc_rigid_point {n : ℕ} {K : Set (Fin n → ℂ)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ x ∈ K, ∀ (U : Set ℂ) (c : ℂ) (g : ℂ → (Fin n → ℂ)),
      IsOpen U → IsPreconnected U → c ∈ U → AnalyticOnNhd ℂ g U →
      MapsTo g U K → g c = x → EqOn g (Function.const ℂ x) U := by
  let e := (EuclideanSpace.equiv (Fin n) ℂ).symm
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne e.continuous.continuousOn.norm
  refine ⟨x, hx, ?_⟩
  intro U c g hU hconn hc hg hmaps hgc
  have hd : DifferentiableOn ℂ (fun t ↦ e (g t)) U :=
    e.differentiable.comp_differentiableOn hg.differentiableOn
  have hm : IsMaxOn (norm ∘ (fun t ↦ e (g t))) U c := by
    intro t ht
    change ‖e (g t)‖ ≤ ‖e (g c)‖
    rw [hgc]
    exact hmax (hmaps ht)
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn hU hd hc hm
  intro t ht
  apply e.injective
  simpa only [Function.const_apply, hgc] using heq ht

/-- A nonconstant analytic disc cannot pass through an isolated point of its
containing set, including away from its chosen central parameter. -/
private theorem adim9_disc_mapsTo_derivedSet {n : ℕ} {K : Set (Fin n → ℂ)}
    {U : Set ℂ} {g : ℂ → (Fin n → ℂ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hg : AnalyticOnNhd ℂ g U)
    (hmaps : MapsTo g U K)
    (hne : ∃ a ∈ U, ∃ b ∈ U, g a ≠ g b) :
    MapsTo g U (derivedSet K) := by
  intro t ht
  by_contra hacc
  have he : ∀ᶠ y in 𝓝 (g t), y ∈ K → y = g t := by
    have h := not_frequently.mp (mt accPt_iff_frequently.mpr hacc)
    filter_upwards [h] with y hy hyK
    by_contra hne
    exact hy ⟨hne, hyK⟩
  have hc := (hg t ht).continuousAt
  have heq : g =ᶠ[𝓝 t] Function.const ℂ (g t) := by
    filter_upwards [hc.eventually he, hU.mem_nhds ht] with z hz hzU
    exact hz (hmaps hzU)
  have hall := hg.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hconn ht heq
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  exact hab ((hall ha).trans (hall hb).symm)

/-- The compact analytic-set argument reduces to constructing a nonconstant
analytic disc at each accumulation point. No local equations are assumed here. -/
private theorem adim9_finite_of_discs_at_accumulation_points
    {n : ℕ} {K : Set (Fin n → ℂ)} (hK : IsCompact K)
    (hdisc : ∀ x ∈ K, AccPt x (𝓟 K) →
      ∃ (U : Set ℂ) (c : ℂ) (g : ℂ → (Fin n → ℂ)),
        IsOpen U ∧ IsPreconnected U ∧ c ∈ U ∧ AnalyticOnNhd ℂ g U ∧
        MapsTo g U K ∧ g c = x ∧ ∃ a ∈ U, ∃ b ∈ U, g a ≠ g b) :
    K.Finite := by
  by_contra hinf
  obtain ⟨x, _, hx⟩ := (show K.Infinite from hinf).exists_accPt_of_subset_isCompact hK Subset.rfl
  have hsub : derivedSet K ⊆ K := (isClosed_iff_derivedSet_subset K).mp hK.isClosed
  have hcompact : IsCompact (derivedSet K) :=
    hK.of_isClosed_subset (isClosed_derivedSet K) hsub
  obtain ⟨y, hy, hrigid⟩ := adim9_exists_disc_rigid_point hcompact ⟨x, hx⟩
  obtain ⟨U, c, g, hU, hconn, hc, hg, hmaps, hgc, hne⟩ := hdisc y (hsub hy) hy
  have hmaps' := adim9_disc_mapsTo_derivedSet hU hconn hg hmaps hne
  have heq := hrigid U c g hU hconn hc hg hmaps' hgc
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  exact hab ((heq ha).trans (heq hb).symm)

/-- A punctured analytic sheet with image in a compact set extends analytically,
and closedness keeps the extension inside that set. -/
private theorem adim9_extend_compact_sheet {n : ℕ} {K : Set (Fin n → ℂ)}
    (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (g : ℂ → (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g (U \ {0}))
    (hmaps : MapsTo g (U \ {0}) K) :
    ∃ G : ℂ → (Fin n → ℂ), AnalyticOnNhd ℂ G U ∧ MapsTo G U K ∧
      EqOn G g (U \ {0}) := by
  classical
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hb : BddAbove ((norm ∘ g) '' (U \ {0})) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hC _ (hmaps ht)
  let G := Function.update g 0 (limUnder (𝓝[≠] 0) g)
  have hd : DifferentiableOn ℂ G U :=
    Complex.differentiableOn_update_limUnder_of_bddAbove
      (hU.mem_nhds h0) hg.differentiableOn hb
  have hG : AnalyticOnNhd ℂ G U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU).mpr hd
  have heq : EqOn G g (U \ {0}) := by
    intro t ht
    exact Function.update_of_ne ht.2 _ _
  have hpunct : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ U \ {0} := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0),
      self_mem_nhdsWithin] with t ht hne
    exact ⟨ht, hne⟩
  refine ⟨G, hG, ?_, heq⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    apply hK.isClosed.mem_of_tendsto (b := 𝓝[≠] (0 : ℂ))
      ((hG 0 h0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
    filter_upwards [hpunct] with t ht
    rw [heq ht]
    exact hmaps ht
  · rw [heq ⟨ht, ht0⟩]
    exact hmaps ⟨ht, ht0⟩

/-- A nonzero analytic discriminant germ vanishing at the origin admits a line
on which its only sufficiently nearby zero is the origin. -/
private theorem adim9_line_avoids_discriminant {n : ℕ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (h0 : (0 : Fin n → ℂ) ∈ U)
    (Δ : (Fin n → ℂ) → ℂ) (hΔ : AnalyticOnNhd ℂ Δ U) (hΔ0 : Δ 0 = 0)
    (hne : ¬ (Δ =ᶠ[𝓝 0] fun _ ↦ 0)) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ), Δ (t • v) ≠ 0 := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  have hfreq : ∃ᶠ z in 𝓝 (0 : Fin n → ℂ), Δ z ≠ 0 := not_eventually.mp hne
  obtain ⟨v, hv, hvB⟩ := (hfreq.and_eventually (Metric.ball_mem_nhds _ hR)).exists
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv hΔ0
  let L : ℂ →L[ℂ] (Fin n → ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  let D : Set ℂ := L ⁻¹' Metric.ball 0 R
  have hD0 : (0 : ℂ) ∈ D := by
    change L 0 ∈ Metric.ball 0 R
    simpa only [map_zero, Metric.mem_ball, dist_self] using hR
  have hD1 : (1 : ℂ) ∈ D := by
    simpa [D, L] using hvB
  have hconn : IsPreconnected D :=
    ((convex_ball (0 : Fin n → ℂ) R).linear_preimage
      (L.restrictScalars ℝ).toLinearMap).isPreconnected
  have han : AnalyticOnNhd ℂ (fun t ↦ Δ (L t)) D := by
    intro t ht
    exact (hΔ (L t) (hball ht)).comp (L.analyticAt t)
  refine ⟨v, hv0, ?_⟩
  change ∀ᶠ t in 𝓝[≠] (0 : ℂ), Δ (L t) ≠ 0
  apply not_frequently.mp
  intro hf
  have heq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn hD0 hf
  have h := heq hD1
  apply hv
  simpa [L] using h

/-- A sheet over a nonconstant power parametrization extends through the unique
central fibre point and remains nonconstant after extension. -/
private theorem adim9_extend_power_sheet {n d : ℕ} {K : Set (Fin n → ℂ)}
    (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (x : Fin n → ℂ)
    (hcentral : ∀ z ∈ K, π z = 0 → z = x)
    (m : ℕ) (hm : 0 < m) (e : Fin d → ℂ) (he : e ≠ 0)
    (g : ℂ → (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g (U \ {0}))
    (hmaps : MapsTo g (U \ {0}) K)
    (hproj : ∀ t ∈ U \ {0}, π (g t) = t ^ m • e) :
    ∃ G : ℂ → (Fin n → ℂ), AnalyticOnNhd ℂ G U ∧ MapsTo G U K ∧
      EqOn G g (U \ {0}) ∧ G 0 = x ∧ ∃ a ∈ U, ∃ b ∈ U, G a ≠ G b := by
  obtain ⟨G, hG, hGK, hagree⟩ := adim9_extend_compact_sheet hK hU h0 g hg hmaps
  have hpunct : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ U \ {0} := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0),
      self_mem_nhdsWithin] with t ht hne
    exact ⟨ht, hne⟩
  have hp : ∀ t ∈ U \ {0}, π (G t) = t ^ m • e := by
    intro t ht
    rw [hagree ht]
    exact hproj t ht
  have hevent : (fun t ↦ π (G t)) =ᶠ[𝓝[≠] (0 : ℂ)] fun t ↦ t ^ m • e :=
    hpunct.mono fun t ht ↦ hp t ht
  have ht₁ : Tendsto (fun t ↦ π (G t)) (𝓝[≠] (0 : ℂ)) (𝓝 (π (G 0))) :=
    (π.continuous.continuousAt.comp (hG 0 h0).continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have ht₂ : Tendsto (fun t : ℂ ↦ t ^ m • e) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℂ ↦ t ^ m • e) := by fun_prop
    simpa only [zero_pow (Nat.ne_of_gt hm), zero_smul] using
      (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
  have hπ0 : π (G 0) = 0 := tendsto_nhds_unique ht₁ (ht₂.congr' hevent.symm)
  refine ⟨G, hG, hGK, hagree, hcentral _ (hGK h0) hπ0, ?_⟩
  obtain ⟨t, ht⟩ := hpunct.exists
  refine ⟨t, ht.1, 0, h0, ?_⟩
  intro heq
  have hpow : t ^ m • e = 0 := by rw [← hp t ht, heq, hπ0]
  exact (smul_ne_zero (pow_ne_zero m ht.2) he) hpow

/-- At an accumulation point every minimal component of the set germ has
positive dimension: a maximal minimal prime would force all coordinates to vanish. -/
private theorem adim9_positive_dimension_at_accumulation {n : ℕ}
    (K : Set (Fin n → ℂ)) (x : Fin n → ℂ) (hx : AccPt x (𝓟 K))
    (P : Ideal (AnalyticGerm n))
    (hP : P ∈ (adim2_ideal n (adim2_germ n K x)).minimalPrimes) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm n ⧸ P) := by
  let I := adim2_ideal n (adim2_germ n K x)
  let : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro a b hab
    rw [analyticGerm_isUnit_iff] at hab
    simp only [map_add] at hab
    by_cases ha : analyticGermValue n a = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [ha] using hab
    · left
      rwa [analyticGerm_isUnit_iff]
  apply le_of_not_gt
  intro hdim
  let : P.IsPrime := hP.isPrime
  have hPm : P.IsMaximal := by
    apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr
    let : Ring.KrullDimLE 0 (AnalyticGerm n ⧸ P) := Ring.krullDimLE_iff.mpr <|
      le_of_not_gt (fun hpos ↦
        not_lt_of_ge ((WithBot.one_le_iff_pos _).mpr hpos) hdim)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hPeq : P = IsLocalRing.maximalIdeal (AnalyticGerm n) :=
    IsLocalRing.eq_maximalIdeal hPm
  have hIP : I = P := by
    have hunique : ∀ Q ∈ I.minimalPrimes, Q = P := by
      intro Q hQ
      have hQP : Q ≤ P := hPeq.symm ▸ IsLocalRing.le_maximalIdeal hQ.isPrime.ne_top
      exact hQP.antisymm (hP.2 hQ.1 hQP)
    have hrad : I.radical = I := adim2_radical n (adim2_germ n K x)
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    apply le_antisymm (sInf_le hP)
    exact le_sInf fun Q hQ ↦ (hunique Q hQ).ge
  have hmax : (analyticGermMaximalIdeal n).IsMaximal := by
    apply RingHom.ker_isMaximal_of_surjective
    intro c
    exact ⟨⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩
  have hPval : P = analyticGermMaximalIdeal n :=
    hPeq.trans (IsLocalRing.eq_maximalIdeal hmax).symm
  have hcoords : ∀ i : Fin n, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      x + z ∈ K → z i = 0 := by
    intro i
    let c : AnalyticGerm n := ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i),
      (fun z : Fin n → ℂ ↦ z i),
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
    have hc : c ∈ I := by
      rw [hIP, hPval]
      rfl
    exact hc
  have he : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ K → z = 0 := by
    filter_upwards [Filter.eventually_all.mpr hcoords] with z hz hzK
    ext i
    exact hz i hzK
  have ht : Tendsto (fun z : Fin n → ℂ ↦ z - x) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun z : Fin n → ℂ ↦ z - x) := by fun_prop
    simpa only [sub_self] using hc.tendsto x
  obtain ⟨z, ⟨hzx, hzK⟩, hz⟩ :=
    ((accPt_iff_frequently.mp hx).and_eventually (ht.eventually he)).exists
  have hztrans : x + (z - x) = z := by abel
  exact hzx (sub_eq_zero.mp (hz (hztrans.symm ▸ hzK)))

/-- A continuous selection among finitely many continuous branches agrees locally
with its branch at the anchor, when those branch values are distinct. -/
private theorem adim9_selection_eventually_eq
    {X E ι : Type*} [TopologicalSpace X] [TopologicalSpace E] [T2Space E]
    [Finite ι] {x : X} (r : ι → X → E) (g : X → E)
    (hr : ∀ i, ContinuousAt (r i) x) (hg : ContinuousAt g x)
    (hinj : Function.Injective (fun i ↦ r i x))
    (hsel : ∀ᶠ y in 𝓝 x, ∃ i, g y = r i y)
    (i : ι) (hi : g x = r i x) : g =ᶠ[𝓝 x] r i := by
  have hsep : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → g y ≠ r j y := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hji).elim
    · have hne : g x ≠ r j x := by
        rw [hi]
        exact fun h ↦ hji (hinj h).symm
      exact ((hg.ne_iff_eventually_ne (hr j)).mp hne).mono fun _ h _ ↦ h
  filter_upwards [Filter.eventually_all.mpr hsep, hsel] with y hy hys
  obtain ⟨j, hj⟩ := hys
  have hji : j = i := by
    by_contra h
    exact hy j h hj
  simpa only [hji] using hj


/-- Continuous lifts of analytic base maps through distinct local analytic sheets
are analytic, without making a global choice of sheet labels. -/
private theorem adim9_analytic_lift_of_local_sheets {n k : ℕ}
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {D : Set B} (s : B → Finset (Fin n → ℂ))
    (hsheets : ∀ x ∈ D, ∃ (W : Set B)
      (r : Fin k → B → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ s y ↔ ∃ j, r j y = z)
    {U : Set ℂ} (hU : IsOpen U) (b : ℂ → B)
    (hb : AnalyticOnNhd ℂ b U) (hbD : MapsTo b U D)
    (g : ℂ → (Fin n → ℂ)) (hg : ContinuousOn g U)
    (hmem : ∀ t ∈ U, g t ∈ s (b t)) : AnalyticOnNhd ℂ g U := by
  intro t ht
  obtain ⟨W, r, hW, hbtW, hr, hs⟩ := hsheets (b t) (hbD ht)
  obtain ⟨i, hi⟩ := (hs (b t) hbtW).2 (g t) |>.mp (hmem t ht)
  have hnear : ∀ᶠ u in 𝓝 t, u ∈ U ∧ b u ∈ W :=
    Filter.Eventually.and (hU.mem_nhds ht)
      ((hb t ht).continuousAt.eventually (hW.mem_nhds hbtW))
  have heq : g =ᶠ[𝓝 t] fun u ↦ r i (b u) := by
    apply adim9_selection_eventually_eq (fun j u ↦ r j (b u)) g
      (fun j ↦ ((hr j (b t) hbtW).comp (hb t ht)).continuousAt)
      ((hg t ht).continuousAt (hU.mem_nhds ht)) (hs (b t) hbtW).1
      (hnear.mono fun u hu ↦ ?_) i hi.symm
    obtain ⟨j, hj⟩ := (hs (b u) hu.2).2 (g u) |>.mp (hmem u hu.1)
    exact ⟨j, hj.symm⟩
  exact ((hr i (b t) hbtW).comp (hb t ht)).congr heq.symm


/-- Finitely many distinct continuous local sheets give an actual covering map
of their incidence space. -/
private theorem adim9_covering_of_local_sheets
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [T2Space E]
    {k : ℕ} (s : X → Set E)
    (hsheets : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ r : Fin k → W → E, (∀ i, Continuous (r i)) ∧
        ∀ y : W, Function.Injective (fun i ↦ r i y) ∧
          ∀ z, z ∈ s y ↔ ∃ i, r i y = z) :
    IsCoveringMap (fun p : {p : X × E // p.2 ∈ s p.1} ↦ p.val.1) := by
  classical
  let Z := {p : X × E // p.2 ∈ s p.1}
  let p : Z → X := fun z ↦ z.val.1
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  intro x
  obtain ⟨W, hW, hx, r, hr, hs⟩ := hsheets x
  let b : p ⁻¹' W → W := fun z ↦ ⟨p z.val, z.property⟩
  let v : p ⁻¹' W → E := fun z ↦ z.val.val.2
  have hb : Continuous b := (hp.comp continuous_subtype_val).subtype_mk _
  have hv : Continuous v := continuous_snd.comp
    (continuous_subtype_val.comp continuous_subtype_val)
  have hsel : ∀ z : p ⁻¹' W, ∃ i, r i (b z) = v z :=
    fun z ↦ (hs (b z)).2 (v z) |>.mp z.val.property
  let label : p ⁻¹' W → Fin k := fun z ↦ (hsel z).choose
  have hlabel : ∀ z, r (label z) (b z) = v z := fun z ↦ (hsel z).choose_spec
  have hlcont : Continuous label := by
    rw [continuous_iff_continuousAt]
    intro z
    have heq := adim9_selection_eventually_eq (fun i y ↦ r i (b y)) v
      (fun i ↦ ((hr i).comp hb).continuousAt) hv.continuousAt
      (hs (b z)).1 (Filter.Eventually.of_forall fun y ↦
        ⟨label y, (hlabel y).symm⟩) (label z) (hlabel z).symm
    have hloc : (fun _ ↦ label z) =ᶠ[𝓝 z] label := by
      filter_upwards [heq] with y hy
      exact (hs (b y)).1 (hy.symm.trans (hlabel y).symm)
    exact continuousAt_const.congr hloc
  let H : p ⁻¹' W ≃ₜ W × Fin k :=
    { toFun := fun z ↦ (b z, label z)
      invFun := fun yi ↦ ⟨⟨(yi.1.val, r yi.2 yi.1),
        (hs yi.1).2 _ |>.mpr ⟨yi.2, rfl⟩⟩, yi.1.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext rfl (hlabel z)
      right_inv := by
        intro yi
        apply Prod.ext
        · rfl
        · exact (hs yi.1).1 (hlabel _)
      continuous_toFun := hb.prodMk hlcont
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        apply Continuous.prodMk (continuous_subtype_val.comp continuous_fst)
        exact continuous_prod_of_discrete_right.mpr hr }
  exact (show IsEvenlyCovered p x (Fin k) from
    ⟨inferInstance, W, hx, hW, hW.preimage hp, H, fun _ ↦ rfl⟩).to_isEvenlyCovered_preimage


/-- A lift through a finite covering becomes invariant under a positive iterate
of any surjective continuous transformation preserving its projection. This is
the finite monodromy step for translation on a universal covering space. -/
private theorem adim9_finite_cover_lift_period
    {A E B : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsCoveringMap p)
    (g : A → E) (hg : Continuous g) (T : A → A)
    (hT : Continuous T) (hTsurj : Function.Surjective T)
    (hproj : ∀ a, p (g (T a)) = p (g a))
    (a₀ : A) (hfinite : (p ⁻¹' {p (g a₀)}).Finite) :
    ∃ m : ℕ, 0 < m ∧ ∀ a, g (T^[m] a) = g a := by
  have hiter : ∀ n a, p (g (T^[n] a)) = p (g a) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', hproj, ih]
  let orbit : ℕ → p ⁻¹' {p (g a₀)} := fun n ↦ ⟨g (T^[n] a₀), hiter n a₀⟩
  letI : Finite (p ⁻¹' {p (g a₀)}) := hfinite.to_subtype
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite orbit
  have hcollision : ∃ i j : ℕ, i < j ∧ g (T^[i] a₀) = g (T^[j] a₀) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, congrArg Subtype.val he⟩
    · exact ⟨j, i, h, (congrArg Subtype.val he).symm⟩
  obtain ⟨i, j, hij, he⟩ := hcollision
  have hall : (fun a ↦ g (T^[j] a)) = fun a ↦ g (T^[i] a) := by
    apply hp.eq_of_comp_eq (hg.comp (hT.iterate j)) (hg.comp (hT.iterate i))
      (funext fun a ↦ (hiter j a).trans (hiter i a).symm) a₀ he.symm
  refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := hTsurj.iterate i a
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
  exact congrFun hall b


/-- Pulling a finite covering of the punctured unit disc back by a positive
power map admits a continuous section. The period comes from a lifted
exponential on the left half-plane. -/
private theorem adim9_punctured_disc_power_lift
    {E : Type*} [TopologicalSpace E]
    (p : E → {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1}) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (hfinite : ∀ w, (p ⁻¹' {w}).Finite) :
    ∃ (m : ℕ) (_hm : 0 < m)
      (g : {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1} → E),
      Continuous g ∧ ∀ z, (p (g z)).val = z.val ^ m := by
  classical
  let H := {z : ℂ | z.re < 0}
  let D := {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1}
  have hH : IsOpen H := isOpen_lt Complex.continuous_re continuous_const
  have hD : IsOpen D := isOpen_ne_fun continuous_id continuous_const |>.inter
    (isOpen_lt continuous_norm continuous_const)
  have hconv : Convex ℝ H := convex_halfSpace_lt (.mk Complex.add_re Complex.smul_re) 0
  have hnonempty : H.Nonempty := ⟨-1, by norm_num [H]⟩
  letI := hconv.contractibleSpace hnonempty
  letI := hH.locallyPathConnectedSpace
  let q : H → D := fun z ↦ ⟨Complex.exp z.val, Complex.exp_ne_zero _, by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    exact z.property⟩
  have hq : Continuous q := (Complex.continuous_exp.comp continuous_subtype_val).subtype_mk _
  have hqsurj : Function.Surjective q := by
    intro z
    refine ⟨⟨Complex.log z.val, ?_⟩, Subtype.ext (Complex.exp_log z.property.1)⟩
    change (Complex.log z.val).re < 0
    rw [Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr z.property.1) z.property.2
  have hqopen : IsOpenMap q := by
    apply hD.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    exact Complex.isOpenMap_exp.comp hH.isOpenEmbedding_subtypeVal.isOpenMap
  have hqquot : Topology.IsQuotientMap q := hqopen.isQuotientMap hq hqsurj
  let a₀ : H := ⟨-1, by norm_num [H]⟩
  obtain ⟨e₀, he₀⟩ := hsurj (q a₀)
  obtain ⟨F, ⟨_, hF⟩, _⟩ := hp.existsUnique_continuousMap_lifts ⟨q, hq⟩ a₀ e₀ he₀
  have hFq : ∀ z, p (F z) = q z := fun z ↦ congrFun hF z
  let τ : ℂ := 2 * Real.pi * Complex.I
  have hτ : τ.re = 0 := by simp [τ]
  let T : H → H := fun z ↦ ⟨z.val + τ, by simpa only [H, Set.mem_setOf_eq, Complex.add_re, hτ, add_zero] using z.property⟩
  have hT : Continuous T := (continuous_subtype_val.add continuous_const).subtype_mk _
  have hTsurj : Function.Surjective T := by
    intro z
    exact ⟨⟨z.val - τ, by simpa only [H, Set.mem_setOf_eq, Complex.sub_re, hτ, sub_zero] using z.property⟩,
      Subtype.ext (sub_add_cancel _ _)⟩
  have hproj : ∀ z, p (F (T z)) = p (F z) := by
    intro z
    rw [hFq, hFq]
    exact Subtype.ext (Complex.exp_periodic z.val)
  obtain ⟨m, hm, hperiod⟩ := adim9_finite_cover_lift_period p hp F F.continuous
    T hT hTsurj hproj a₀ (hfinite _)
  have hiter : ∀ j (z : H), (T^[j] z).val = z.val + j * τ := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ j ih =>
      intro z
      rw [Function.iterate_succ_apply']
      change (T^[j] z).val + τ = z.val + (j + 1 : ℕ) * τ
      rw [ih, Nat.cast_add, Nat.cast_one]
      ring
  let F' : ℂ → E := fun z ↦ if hz : z ∈ H then F ⟨z, hz⟩ else e₀
  have hperiod' : Function.Periodic F' (m * τ) := by
    intro z
    have hre : (z + m * τ).re = z.re := by simp [τ]
    by_cases hz : z ∈ H
    · have hz' : z + m * τ ∈ H := by change (z + m * τ).re < 0; rwa [hre]
      simp only [F', dif_pos hz, dif_pos hz']
      have hi : (⟨z + m * τ, hz'⟩ : H) = T^[m] ⟨z, hz⟩ :=
        Subtype.ext (hiter m ⟨z, hz⟩).symm
      rw [hi, hperiod]
    · have hz' : z + m * τ ∉ H := by change ¬ (z + m * τ).re < 0; rwa [hre]
      simp only [F', dif_neg hz, dif_neg hz']
  let scale : H → H := fun z ↦ ⟨m * z.val, by
    change (m * z.val).re < 0
    simpa using mul_neg_of_pos_of_neg (show (0 : ℝ) < m by exact_mod_cast hm) z.property⟩
  have hscale : Continuous scale := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have hdesc : ∀ z w : H, q z = q w → F (scale z) = F (scale w) := by
    intro z w he
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp (congrArg Subtype.val he)
    have hs (v : H) : F' (m * v.val) = F (scale v) := dif_pos (scale v).property
    rw [← hs, ← hs, hj]
    have heq : (m : ℂ) * (w.val + j * τ) = m * w.val + j * (m * τ) := by ring
    rw [heq]
    exact hperiod'.int_mul j (m * w.val)
  let g : D → E := fun z ↦ F (scale ((hqsurj z).choose))
  have hgq : ∀ z, g (q z) = F (scale z) := fun z ↦
    hdesc _ z (hqsurj (q z)).choose_spec
  refine ⟨m, hm, g, ?_, ?_⟩
  · apply hqquot.continuous_iff.mpr
    exact (F.continuous.comp hscale).congr (fun z ↦ (hgq z).symm)
  · intro z
    obtain ⟨w, rfl⟩ := hqsurj z
    rw [hgq, hFq]
    exact Complex.exp_nat_mul w.val m


/-- Finite nonempty fibres with distinct analytic local enumerations have an
analytic single-valued sheet after a positive power substitution. -/
private theorem adim9_analytic_power_sheet {n k : ℕ}
    (s : ℂ → Finset (Fin n → ℂ))
    (hne : ∀ x : ℂ, x ≠ 0 ∧ ‖x‖ < 1 → (s x).Nonempty)
    (hsheets : ∀ x : ℂ, x ≠ 0 ∧ ‖x‖ < 1 →
      ∃ (W : Set ℂ) (r : Fin k → ℂ → (Fin n → ℂ)),
        IsOpen W ∧ x ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
          ∀ z, z ∈ s y ↔ ∃ j, r j y = z) :
    ∃ (m : ℕ) (_hm : 0 < m) (g : ℂ → (Fin n → ℂ)),
      AnalyticOnNhd ℂ g {t | t ≠ 0 ∧ ‖t‖ < 1} ∧
      ∀ t, t ≠ 0 ∧ ‖t‖ < 1 → g t ∈ s (t ^ m) := by
  classical
  let D := {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1}
  let Z := {z : D × (Fin n → ℂ) // z.2 ∈ s z.1.val}
  let p : Z → D := fun z ↦ z.val.1
  have hp : IsCoveringMap p := by
    apply adim9_covering_of_local_sheets (fun x : D ↦ (s x.val : Set (Fin n → ℂ)))
    intro x
    obtain ⟨W, r, hW, hxW, hr, hs⟩ := hsheets x.val x.property
    refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hxW,
      fun i y ↦ r i y.val.val, ?_, ?_⟩
    · intro i
      exact (hr i).continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun y ↦ y.property)
    · intro y
      exact hs y.val.val y.property
  have hsurj : Function.Surjective p := by
    intro x
    obtain ⟨z, hz⟩ := hne x.val x.property
    exact ⟨⟨(x, z), hz⟩, rfl⟩
  have hfinite : ∀ w, (p ⁻¹' {w}).Finite := by
    intro w
    apply Set.Finite.of_injOn (f := fun z : Z ↦ z.val.2) (t := (s w.val : Set _))
    · intro z hz
      change p z = w at hz
      have hmem := z.property
      change z.val.2 ∈ s (p z).val at hmem
      rwa [hz] at hmem
    · intro z hz y hy he
      apply Subtype.ext
      exact Prod.ext (hz.trans hy.symm) he
    · exact (s w.val).finite_toSet
  obtain ⟨m, hm, G, hG, hGp⟩ := adim9_punctured_disc_power_lift p hp hsurj hfinite
  let g : ℂ → (Fin n → ℂ) := fun t ↦ if ht : t ∈ D then (G ⟨t, ht⟩).val.2 else 0
  have hgval : ∀ t : D, g t.val = (G t).val.2 := fun t ↦ dif_pos t.property
  have hg : ContinuousOn g D := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_snd.comp (continuous_subtype_val.comp hG)).congr
      (fun t ↦ (hgval t).symm)
  have hmem : ∀ t ∈ D, g t ∈ s (t ^ m) := by
    intro t ht
    rw [hgval ⟨t, ht⟩]
    have h := (G ⟨t, ht⟩).property
    change (G ⟨t, ht⟩).val.2 ∈ s (p (G ⟨t, ht⟩)).val at h
    rwa [hGp] at h
  have hpow : MapsTo (fun t : ℂ ↦ t ^ m) D D := by
    intro t ht
    refine ⟨pow_ne_zero m ht.1, ?_⟩
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ht.2 (Nat.ne_of_gt hm)
  refine ⟨m, hm, g, ?_, hmem⟩
  exact adim9_analytic_lift_of_local_sheets s hsheets
    (isOpen_ne_fun continuous_id continuous_const |>.inter
      (isOpen_lt continuous_norm continuous_const))
    (fun t ↦ t ^ m) (analyticOnNhd_id.pow m) hpow g hg hmem


/-- A common power substitution enumerates all branches of a finite analytic
cover, including covers with several connected components. -/
private theorem adim9_analytic_power_enumeration {n k : ℕ}
    (s : ℂ → Finset (Fin n → ℂ))
    (hsheets : ∀ x : ℂ, x ≠ 0 ∧ ‖x‖ < 1 →
      ∃ (W : Set ℂ) (r : Fin k → ℂ → (Fin n → ℂ)),
        IsOpen W ∧ x ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
          ∀ z, z ∈ s y ↔ ∃ j, r j y = z) :
    ∃ (m : ℕ), 0 < m ∧ ∃ r : Fin k → ℂ → (Fin n → ℂ),
      (∀ j, AnalyticOnNhd ℂ (r j) {t | t ≠ 0 ∧ ‖t‖ < 1}) ∧
      ∀ t, t ≠ 0 ∧ ‖t‖ < 1 → ∀ z, z ∈ s (t ^ m) ↔ ∃ j, r j t = z := by
  classical
  induction k generalizing s with
  | zero =>
    refine ⟨1, zero_lt_one, Fin.elim0, (fun j ↦ Fin.elim0 j), ?_⟩
    intro t ht z
    obtain ⟨W, r, _, htW, _, hs⟩ := hsheets t ht
    simpa using (hs t htW).2 z
  | succ k ih =>
    let D := {t : ℂ | t ≠ 0 ∧ ‖t‖ < 1}
    have hD : IsOpen D := (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_lt continuous_norm continuous_const)
    have hne : ∀ t : ℂ, t ∈ D → (s t).Nonempty := by
      intro t ht
      obtain ⟨W, r, _, htW, _, hs⟩ := hsheets t ht
      exact ⟨r 0 t, ((hs t htW).2 _).mpr ⟨0, rfl⟩⟩
    obtain ⟨m, hm, g, hg, hgmem⟩ := adim9_analytic_power_sheet s hne hsheets
    have hpow (t : ℂ) (ht : t ∈ D) : t ^ m ∈ D := by
      exact ⟨pow_ne_zero m ht.1, by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) ht.2 (Nat.ne_of_gt hm)⟩
    let s' : ℂ → Finset (Fin n → ℂ) := fun t ↦ (s (t ^ m)).erase (g t)
    have hs' : ∀ x : ℂ, x ∈ D →
        ∃ (W : Set ℂ) (r : Fin k → ℂ → (Fin n → ℂ)),
          IsOpen W ∧ x ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
          ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
            ∀ z, z ∈ s' y ↔ ∃ j, r j y = z := by
      intro x hx
      obtain ⟨W, r, hW, hxW, hr, hs⟩ := hsheets (x ^ m) (hpow x hx)
      obtain ⟨i, hi⟩ := ((hs (x ^ m) hxW).2 (g x)).mp (hgmem x hx)
      have hnear : ∀ᶠ y in 𝓝 x, y ∈ D ∧ y ^ m ∈ W :=
        Filter.Eventually.and (hD.mem_nhds hx)
          ((continuousAt_id.pow m).eventually (hW.mem_nhds hxW))
      have heq : g =ᶠ[𝓝 x] fun y ↦ r i (y ^ m) := by
        apply adim9_selection_eventually_eq (fun j y ↦ r j (y ^ m)) g
          (fun j ↦ ((hr j (x ^ m) hxW).comp (f := fun z : ℂ ↦ z ^ m) (analyticAt_id.pow m)).continuousAt)
          (hg x hx).continuousAt (hs (x ^ m) hxW).1
          (hnear.mono fun y hy ↦ ?_) i hi.symm
        obtain ⟨j, hj⟩ := ((hs (y ^ m) hy.2).2 (g y)).mp (hgmem y hy.1)
        exact ⟨j, hj.symm⟩
      obtain ⟨W', hW'sub, hW', hxW'⟩ := mem_nhds_iff.mp (hnear.and heq)
      refine ⟨W', fun j y ↦ r (i.succAbove j) (y ^ m), hW', hxW', ?_, ?_⟩
      · intro j y hy
        exact (hr (i.succAbove j) (y ^ m) (hW'sub hy).1.2).comp (f := fun z : ℂ ↦ z ^ m) (analyticAt_id.pow m)
      · intro y hy
        have hyW := (hW'sub hy).1.2
        have hyEq := (hW'sub hy).2
        refine ⟨(hs (y ^ m) hyW).1.comp Fin.succAbove_right_injective, ?_⟩
        intro z
        simp only [s', Finset.mem_erase]
        constructor
        · rintro ⟨hne, hz⟩
          obtain ⟨j, hj⟩ := ((hs (y ^ m) hyW).2 z).mp hz
          have hji : j ≠ i := by
            intro hji
            exact hne (hj.symm.trans (hji ▸ hyEq.symm))
          obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hji
          exact ⟨l, hl ▸ hj⟩
        · rintro ⟨j, rfl⟩
          refine ⟨?_, ((hs (y ^ m) hyW).2 _).mpr ⟨i.succAbove j, rfl⟩⟩
          intro h
          exact Fin.succAbove_ne i j ((hs (y ^ m) hyW).1 (h.trans hyEq))
    obtain ⟨l, hl, r, hr, henum⟩ := ih s' hs'
    let R : Fin (k + 1) → ℂ → (Fin n → ℂ) := Fin.cons (fun t ↦ g (t ^ l)) r
    have hpow' (t : ℂ) (ht : t ∈ D) : t ^ l ∈ D := by
      exact ⟨pow_ne_zero l ht.1, by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) ht.2 (Nat.ne_of_gt hl)⟩
    refine ⟨l * m, Nat.mul_pos hl hm, R, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun i ↦ hr i) j
      intro t ht
      exact (hg (t ^ l) (hpow' t ht)).comp (f := fun z : ℂ ↦ z ^ l) (analyticAt_id.pow l)
    · intro t ht z
      rw [pow_mul]
      constructor
      · intro hz
        by_cases he : z = g (t ^ l)
        · exact ⟨0, he.symm⟩
        · obtain ⟨j, hj⟩ := (henum t ht z).mp (Finset.mem_erase.mpr ⟨he, hz⟩)
          exact ⟨j.succ, hj⟩
      · rintro ⟨j, hj⟩
        revert hj
        refine Fin.cases ?_ ?_ j
        · intro hj
          rw [← hj]
          exact hgmem (t ^ l) (hpow' t ht)
        · intro i hi
          exact (Finset.mem_erase.mp ((henum t ht z).mpr ⟨i, hi⟩)).2


/-- A monic analytic polynomial without discriminant zeros along a punctured
line disc has a full analytic root enumeration after a positive power substitution. -/
private theorem adim9_polynomial_power_roots {d k : ℕ}
    (a : Fin k → (Fin d → ℂ) → ℂ) (e : Fin d → ℂ)
    (ha : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ j, AnalyticAt ℂ (a j) (t • e))
    (hdiscr : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      AnalyticDivisorAlgebraic5.weierstrassDiscr a (t • e) ≠ 0) :
    ∃ (m : ℕ) (_hm : 0 < m) (ρ : Fin k → ℂ → ℂ),
      (∀ j, AnalyticOnNhd ℂ (ρ j) {t | t ≠ 0 ∧ ‖t‖ < 1}) ∧
      ∀ t, t ≠ 0 ∧ ‖t‖ < 1 → ∀ v,
        (AnalyticDivisorAlgebraic5.monicPoly a (t ^ m • e)).eval v = 0 ↔
          ∃ j, ρ j t = v := by
  classical
  let L : ℂ →L[ℂ] (Fin d → ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight e
  let s : ℂ → Finset (Fin 1 → ℂ) := fun t ↦
    (AnalyticDivisorAlgebraic5.monicPoly a (L t)).roots.toFinset.image (fun z _ ↦ z)
  have hmem (t : ℂ) (z : Fin 1 → ℂ) :
      z ∈ s t ↔ (AnalyticDivisorAlgebraic5.monicPoly a (L t)).eval (z 0) = 0 := by
    simp only [s, Finset.mem_image, Multiset.mem_toFinset,
      Polynomial.mem_roots (AnalyticDivisorAlgebraic5.spec_monicPoly a (L t)).1.ne_zero,
      Polynomial.IsRoot]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      refine ⟨z 0, hz, ?_⟩
      ext i
      exact congrArg z (Subsingleton.elim 0 i)
  have hsheets : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      ∃ (W : Set ℂ) (r : Fin k → ℂ → (Fin 1 → ℂ)),
        IsOpen W ∧ t ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
          ∀ z, z ∈ s y ↔ ∃ j, r j y = z := by
    intro t ht
    obtain ⟨φ, hφ, hfactor⟩ := AnalyticDivisorAlgebraic5.spec_exists_root_graphs
      (ha t ht) (hdiscr t ht)
    have han : ∀ᶠ y in 𝓝 t, ∀ j, AnalyticAt ℂ (fun u ↦ φ j (L u)) y :=
      Filter.eventually_all.mpr fun j ↦ ((show AnalyticAt ℂ (φ j) (L t) from hφ j).comp (L.analyticAt t)).eventually_analyticAt
    have hfac := L.continuous.continuousAt.eventually hfactor
    obtain ⟨W, hWsub, hW, htW⟩ := mem_nhds_iff.mp (han.and hfac)
    refine ⟨W, fun j u _ ↦ φ j (L u), hW, htW, ?_, ?_⟩
    · intro j y hy
      exact analyticAt_pi_iff.mpr (fun _ ↦ (hWsub hy).1 j)
    · intro y hy
      have hfy := (hWsub hy).2
      refine ⟨?_, ?_⟩
      · intro i j hij
        by_contra hne
        exact hfy.2 hne (congrFun hij 0)
      · intro z
        rw [hmem, (AnalyticDivisorAlgebraic5.spec_monicPoly a (L y)).2.2, hfy.1]
        simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
        constructor
        · rintro ⟨j, hj⟩
          refine ⟨j, ?_⟩
          ext i
          exact hj.symm.trans (congrArg z (Subsingleton.elim 0 i))
        · rintro ⟨j, hj⟩
          exact ⟨j, (congrFun hj 0).symm⟩
  obtain ⟨m, hm, g, hg, henum⟩ := adim9_analytic_power_enumeration s hsheets
  refine ⟨m, hm, fun j t ↦ g j t 0, fun j ↦ analyticOnNhd_pi_iff.mp (hg j) 0, ?_⟩
  intro t ht v
  have h := henum t ht (fun _ ↦ v)
  rw [hmem] at h
  constructor
  · intro hv
    obtain ⟨j, hj⟩ := h.mp hv
    exact ⟨j, congrFun hj 0⟩
  · rintro ⟨j, hj⟩
    apply h.mpr
    refine ⟨j, ?_⟩
    ext i
    exact (congrArg (g j t) (Subsingleton.elim i 0)).trans hj


/-- A positive-degree monic family has a chosen analytic power root. -/
private theorem adim9_polynomial_power_root {d k : ℕ} (hk : 0 < k)
    (a : Fin k → (Fin d → ℂ) → ℂ) (e : Fin d → ℂ)
    (ha : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ j, AnalyticAt ℂ (a j) (t • e))
    (hdiscr : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      AnalyticDivisorAlgebraic5.weierstrassDiscr a (t • e) ≠ 0) :
    ∃ (m : ℕ) (_hm : 0 < m) (ρ : ℂ → ℂ),
      AnalyticOnNhd ℂ ρ {t | t ≠ 0 ∧ ‖t‖ < 1} ∧
      ∀ t, t ≠ 0 ∧ ‖t‖ < 1 →
        (AnalyticDivisorAlgebraic5.monicPoly a (t ^ m • e)).eval (ρ t) = 0 := by
  obtain ⟨m, hm, ρ, hρ, hroots⟩ := adim9_polynomial_power_roots a e ha hdiscr
  exact ⟨m, hm, ρ ⟨0, hk⟩, hρ ⟨0, hk⟩,
    fun t ht ↦ (hroots t ht _).mpr ⟨⟨0, hk⟩, rfl⟩⟩


/-- Polynomial evaluation along analytic coefficient and root functions is analytic. -/
private theorem adim9_analytic_polynomial_eval {d : ℕ}
    (r : Polynomial ((Fin d → ℂ) → ℂ)) (w : ℂ → (Fin d → ℂ))
    (ρ : ℂ → ℂ) (t : ℂ) (hw : AnalyticAt ℂ w t)
    (hρ : AnalyticAt ℂ ρ t)
    (hr : ∀ i, AnalyticAt ℂ (r.coeff i) (w t)) :
    AnalyticAt ℂ (fun u ↦ r.eval₂
      (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (w u)) (ρ u)) t := by
  classical
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum]
  convert (Finset.analyticAt_sum r.support fun i _ ↦ ((hr i).comp hw).mul (hρ.pow i)) using 1
  ext u
  simp

/-- A punctured line condition can be rescaled to hold throughout the punctured
unit disc while staying in a prescribed parameter neighbourhood. -/
private theorem adim9_rescale_punctured_line {d : ℕ}
    (V : Set (Fin d → ℂ)) (hV : V ∈ 𝓝 (0 : Fin d → ℂ))
    (Δ : (Fin d → ℂ) → ℂ) (v : Fin d → ℂ) (hv : v ≠ 0)
    (hline : ∀ᶠ t in 𝓝[≠] (0 : ℂ), Δ (t • v) ≠ 0) :
    ∃ e : Fin d → ℂ, e ≠ 0 ∧ ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      t • e ∈ V ∧ Δ (t • e) ≠ 0 := by
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ V := by
    have hc : ContinuousAt (fun t : ℂ ↦ t • v) 0 :=
      continuousAt_id.smul continuousAt_const
    exact hc.preimage_mem_nhds (by simpa only [zero_smul] using hV)
  have hline' : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → Δ (t • v) ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
      using hline
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hnear.and hline')
  let c : ℂ := (ε / 2 : ℝ)
  have hcpos : 0 < ε / 2 := half_pos hε
  have hc : c ≠ 0 := by
    change ((ε / 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt hcpos)
  have hcnorm : ‖c‖ = ε / 2 := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  refine ⟨c • v, smul_ne_zero hc hv, ?_⟩
  intro t ht
  have htc : t * c ≠ 0 := mul_ne_zero ht.1 hc
  have hsmall : dist (t * c) 0 < ε := by
    rw [dist_zero_right, norm_mul, hcnorm]
    have hlt := mul_lt_mul_of_pos_right ht.2 hcpos
    linarith
  simpa only [mul_smul] using
    And.intro (hball hsmall).1 ((hball hsmall).2 htc)


/-- Distinguished coordinate relations force every chosen root branch to tend
to the origin, without a uniqueness assumption on a larger compact fibre. -/
private theorem adim9_tendsto_zero_of_coordinate_relations
    {α : Type*} {l : Filter α} {n d : ℕ}
    (w : α → (Fin d → ℂ)) (g : α → (Fin n → ℂ))
    (hw : Tendsto w l (𝓝 0)) (k : Fin n → ℕ)
    (a : (i : Fin n) → Fin (k i) → (Fin d → ℂ) → ℂ)
    (ha : ∀ i j, ContinuousAt (a i j) 0) (ha0 : ∀ i j, a i j 0 = 0)
    (hrel : ∀ᶠ t in l, ∀ i,
      AnalyticDivisorAlgebraic4.monicInLast (a i) (w t, g t i) = 0) :
    Tendsto g l (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := hw.eventually
    (AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small (ha i) (ha0 i) hε)
  filter_upwards [hsmall, hrel] with t ht hrt
  simpa only [Pi.zero_apply, dist_zero_right] using ht (g t i) (hrt i)

/-- A prescribed punctured limit identifies the value of a compact-valued
analytic extension. A nonzero power projection ensures nonconstancy. -/
private theorem adim9_extend_power_sheet_of_tendsto {n d : ℕ}
    {K : Set (Fin n → ℂ)} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (m : ℕ) (hm : 0 < m) (e : Fin d → ℂ) (he : e ≠ 0)
    (g : ℂ → (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g (U \ {0}))
    (hmaps : MapsTo g (U \ {0}) K)
    (hproj : ∀ t ∈ U \ {0}, π (g t) = t ^ m • e)
    (hx : Tendsto g (𝓝[≠] 0) (𝓝 0)) :
    ∃ G : ℂ → (Fin n → ℂ), AnalyticOnNhd ℂ G U ∧ MapsTo G U K ∧
      EqOn G g (U \ {0}) ∧ G 0 = 0 ∧ ∃ a ∈ U, ∃ b ∈ U, G a ≠ G b := by
  obtain ⟨G, hG, hGK, hagree⟩ := adim9_extend_compact_sheet hK hU h0 g hg hmaps
  have hpunct : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ U \ {0} := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0),
      self_mem_nhdsWithin] with t ht hne
    exact ⟨ht, hne⟩
  have hevent : G =ᶠ[𝓝[≠] (0 : ℂ)] g := hpunct.mono fun t ht ↦ hagree ht
  have hG0 : G 0 = 0 := tendsto_nhds_unique
    ((hG 0 h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hx.congr' hevent.symm)
  refine ⟨G, hG, hGK, hagree, hG0, ?_⟩
  obtain ⟨t, ht⟩ := hpunct.exists
  refine ⟨t, ht.1, 0, h0, ?_⟩
  intro heq
  have hpow : t ^ m • e = 0 := by
    rw [← hproj t ht, ← hagree ht, heq, hG0, map_zero]
  exact (smul_ne_zero (pow_ne_zero m ht.2) he) hpow


/-- Rational reconstruction of a power root in a compact representative produces
an analytic disc through its unique central fibre point. -/
private theorem adim9_disc_of_reconstructed_roots {n d k : ℕ}
    (hk : 0 < k) (a : Fin k → (Fin d → ℂ) → ℂ)
    (e : Fin d → ℂ) (he : e ≠ 0)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (ha : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ j, AnalyticAt ℂ (a j) (t • e))
    (hdiscr : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      AnalyticDivisorAlgebraic5.weierstrassDiscr a (t • e) ≠ 0)
    (hr : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ j i,
      AnalyticAt ℂ ((r j).coeff i) (t • e))
    (hΔ : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → AnalyticAt ℂ Δ (t • e))
    (hΔne : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → Δ (t • e) ≠ 0)
    (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (x : Fin n → ℂ)
    (hcentral : ∀ z ∈ K, π z = 0 → z = x)
    (hroot : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ v : ℂ,
      (AnalyticDivisorAlgebraic5.monicPoly a (t • e)).eval v = 0 →
      let z : Fin n → ℂ := fun i ↦
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (t • e)) v / Δ (t • e)
      z ∈ K ∧ π z = t • e) :
    ∃ G : ℂ → (Fin n → ℂ), AnalyticOnNhd ℂ G (Metric.ball 0 1) ∧
      MapsTo G (Metric.ball 0 1) K ∧ G 0 = x ∧
      ∃ u ∈ Metric.ball (0 : ℂ) 1, ∃ v ∈ Metric.ball (0 : ℂ) 1, G u ≠ G v := by
  obtain ⟨m, hm, ρ, hρ, hρroot⟩ := adim9_polynomial_power_root hk a e ha hdiscr
  let w : ℂ → (Fin d → ℂ) := fun t ↦ t ^ m • e
  let g : ℂ → (Fin n → ℂ) := fun t i ↦
    (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (w t)) (ρ t) / Δ (w t)
  have hpow (t : ℂ) (ht : t ≠ 0 ∧ ‖t‖ < 1) : t ^ m ≠ 0 ∧ ‖t ^ m‖ < 1 := by
    exact ⟨pow_ne_zero m ht.1, by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht.2 (Nat.ne_of_gt hm)⟩
  have hmem (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) 1 \ {0}) :
      t ≠ 0 ∧ ‖t‖ < 1 := ⟨ht.2, by simpa using ht.1⟩
  have hw (t : ℂ) : AnalyticAt ℂ w t :=
    (analyticAt_id.pow m).smul analyticAt_const
  have hg : AnalyticOnNhd ℂ g (Metric.ball 0 1 \ {0}) := by
    intro t ht
    have ht' := hmem t ht
    apply analyticAt_pi_iff.mpr
    intro i
    exact (adim9_analytic_polynomial_eval (r i) w ρ t (hw t) (hρ t ht')
      (hr (t ^ m) (hpow t ht') i)).div
      ((show AnalyticAt ℂ Δ (w t) from hΔ (t ^ m) (hpow t ht')).comp (hw t)) (hΔne (t ^ m) (hpow t ht'))
  have hgK : MapsTo g (Metric.ball 0 1 \ {0}) K := by
    intro t ht
    exact (hroot (t ^ m) (hpow t (hmem t ht)) (ρ t) (hρroot t (hmem t ht))).1
  have hproj : ∀ t ∈ Metric.ball (0 : ℂ) 1 \ {0}, π (g t) = t ^ m • e := by
    intro t ht
    exact (hroot (t ^ m) (hpow t (hmem t ht)) (ρ t) (hρroot t (hmem t ht))).2
  obtain ⟨G, hG, hGK, _, hG0, hne⟩ := adim9_extend_power_sheet hK
    Metric.isOpen_ball (Metric.mem_ball_self zero_lt_one) π x hcentral m hm e he g hg hgK hproj
  exact ⟨G, hG, hGK, hG0, hne⟩


/-- Membership in a closed locally analytic set continues along an analytic
map on a connected domain once it holds on a nonempty open subset. -/
private theorem adim9_mapsTo_of_local_membership {n : ℕ}
    (K : Set (Fin n → ℂ)) (hK : IsClosed K)
    (hloc : ∀ x ∈ K, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ x ∈ V ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) V) ∧
        ∀ z ∈ V, (z ∈ K ↔ ∀ j, f j z = 0))
    (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (g : ℂ → (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g U)
    (hne : (U ∩ interior (g ⁻¹' K)).Nonempty) : MapsTo g U K := by
  have hsub : U ⊆ interior (g ⁻¹' K) := by
    apply hconn.subset_of_closure_inter_subset isOpen_interior hne
    rintro t ⟨htcl, htU⟩
    have htK : g t ∈ K := by
      apply hK.mem_of_frequently_of_tendsto _ (hg t htU).continuousAt.tendsto
      exact (mem_closure_iff_frequently.mp htcl).mono fun z hz ↦ interior_subset (s := g ⁻¹' K) hz
    obtain ⟨V, hV, htV, m, f, hf, hKV⟩ := hloc (g t) htK
    have hnear : U ∩ g ⁻¹' V ∈ 𝓝 t :=
      inter_mem (hU.mem_nhds htU) ((hg t htU).continuousAt.preimage_mem_nhds (hV.mem_nhds htV))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hfreq := (mem_closure_iff_frequently.mp htcl).and_eventually
      (Metric.ball_mem_nhds t hε)
    obtain ⟨y, hy, hyB⟩ := hfreq.exists
    have heq (j : Fin m) : EqOn (fun z ↦ f j (g z)) 0 (Metric.ball t ε) := by
      have han : AnalyticOnNhd ℂ (fun z ↦ f j (g z)) (Metric.ball t ε) := by
        intro z hz
        exact (hf j (g z) (hball hz).2).comp (hg z (hball hz).1)
      apply han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball t ε).isPreconnected hyB
      filter_upwards [isOpen_interior.mem_nhds hy, Metric.ball_mem_nhds y
        (show 0 < ε - dist y t by linarith [Metric.mem_ball.mp hyB])] with z hzK hzB
      have hzball : z ∈ Metric.ball t ε := by
        have hzdist := Metric.mem_ball.mp hzB
        have htri := dist_triangle z y t
        exact Metric.mem_ball.mpr (by linarith)
      exact (hKV (g z) (hball hzball).2).mp (interior_subset (s := g ⁻¹' K) hzK) j
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds t hε)
    intro z hz
    exact (hKV (g z) (hball hz).2).mpr fun j ↦ heq j hz
  exact fun _ ht ↦ interior_subset (s := g ⁻¹' K) (hsub ht)


/-- If finitely many analytic branches collectively meet a closed analytic set
over every parameter, one entire branch lies in that set. -/
private theorem adim9_select_admissible_analytic_branch {n k : ℕ}
    (K : Set (Fin n → ℂ)) (hK : IsClosed K)
    (hloc : ∀ x ∈ K, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ x ∈ V ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) V) ∧
        ∀ z ∈ V, (z ∈ K ↔ ∀ j, f j z = 0))
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) (hconn : IsPreconnected U)
    (g : Fin k → ℂ → (Fin n → ℂ)) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hcover : ∀ t ∈ U, ∃ i, g i t ∈ K) :
    ∃ i, MapsTo (g i) U K := by
  letI : Nonempty U := hne.to_subtype
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hc (i : Fin k) : IsClosed ((fun t : U ↦ g i t.val) ⁻¹' K) :=
    hK.preimage ((hg i).continuousOn.comp_continuous continuous_subtype_val
      (fun t ↦ t.property))
  have hu : (⋃ i : Fin k, (fun t : U ↦ g i t.val) ⁻¹' K) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨i, hi⟩ := hcover t.val t.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, t, ht⟩ := nonempty_interior_of_iUnion_of_closed hc hu
  refine ⟨i, adim9_mapsTo_of_local_membership K hK hloc U hU hconn (g i) (hg i) ?_⟩
  refine ⟨t.val, t.property, ?_⟩
  exact hU.isOpenEmbedding_subtypeVal.isOpenMap.interior_preimage_subset_preimage_interior ht


/-- The punctured unit disc is the continuous exponential image of a convex
half-plane. -/
private theorem adim9_punctured_unit_disc_preconnected :
    IsPreconnected {t : ℂ | t ≠ 0 ∧ ‖t‖ < 1} := by
  have hconv : Convex ℝ {z : ℂ | z.re < 0} :=
    convex_halfSpace_lt (.mk Complex.add_re Complex.smul_re) 0
  have heq : Complex.exp '' {z : ℂ | z.re < 0} = {t : ℂ | t ≠ 0 ∧ ‖t‖ < 1} := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨Complex.exp_ne_zero _, by rwa [Complex.norm_exp, Real.exp_lt_one_iff]⟩
    · rintro ⟨ht, htn⟩
      refine ⟨Complex.log t, ?_, Complex.exp_log ht⟩
      change (Complex.log t).re < 0
      rw [Complex.log_re]
      exact Real.log_neg (norm_pos_iff.mpr ht) htn
  rw [← heq]
  exact hconv.isPreconnected.image _ Complex.continuous_exp.continuousOn

/-- Pointwise existence of admissible candidates in a finite analytic cover
suffices to choose one analytic power sheet entirely in the closed analytic set. -/
private theorem adim9_admissible_power_sheet {n k : ℕ}
    (s : ℂ → Finset (Fin n → ℂ))
    (hsheets : ∀ x : ℂ, x ≠ 0 ∧ ‖x‖ < 1 →
      ∃ (W : Set ℂ) (r : Fin k → ℂ → (Fin n → ℂ)),
        IsOpen W ∧ x ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
          ∀ z, z ∈ s y ↔ ∃ j, r j y = z)
    (K : Set (Fin n → ℂ)) (hK : IsClosed K)
    (hloc : ∀ x ∈ K, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ x ∈ V ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) V) ∧
        ∀ z ∈ V, (z ∈ K ↔ ∀ j, f j z = 0))
    (hadmissible : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∃ z ∈ s t, z ∈ K) :
    ∃ (m : ℕ), 0 < m ∧ ∃ g : ℂ → (Fin n → ℂ),
      AnalyticOnNhd ℂ g {t | t ≠ 0 ∧ ‖t‖ < 1} ∧
      MapsTo g {t | t ≠ 0 ∧ ‖t‖ < 1} K ∧
      ∀ t, t ≠ 0 ∧ ‖t‖ < 1 → g t ∈ s (t ^ m) := by
  obtain ⟨m, hm, r, hr, henum⟩ := adim9_analytic_power_enumeration s hsheets
  have hpow (t : ℂ) (ht : t ≠ 0 ∧ ‖t‖ < 1) : t ^ m ≠ 0 ∧ ‖t ^ m‖ < 1 := by
    exact ⟨pow_ne_zero m ht.1, by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht.2 (Nat.ne_of_gt hm)⟩
  have hcover : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∃ i, r i t ∈ K := by
    intro t ht
    obtain ⟨z, hz, hzK⟩ := hadmissible (t ^ m) (hpow t ht)
    obtain ⟨i, hi⟩ := (henum t ht z).mp hz
    exact ⟨i, hi ▸ hzK⟩
  have hne : {t : ℂ | t ≠ 0 ∧ ‖t‖ < 1}.Nonempty := by
    refine ⟨(1 / 2 : ℂ), ?_, ?_⟩ <;> norm_num
  obtain ⟨i, hi⟩ := adim9_select_admissible_analytic_branch K hK hloc
    {t : ℂ | t ≠ 0 ∧ ‖t‖ < 1}
    ((isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_lt continuous_norm continuous_const)) hne
    adim9_punctured_unit_disc_preconnected r hr hcover
  exact ⟨m, hm, r i, hr i, hi, fun t ht ↦ (henum t ht _).mpr ⟨i, rfl⟩⟩


/-- Monic germ polynomials have monic analytic coefficient representatives. -/
private theorem adim9_monic_representative (d : ℕ) (Q : Polynomial (AnalyticGerm d))
    (hQ : Q.Monic) :
    ∃ q : Polynomial ((Fin d → ℂ) → ℂ), q.Monic ∧
      ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧ Germ.ofFun (q.coeff i) = (Q.coeff i).val := by
  classical
  let k := Q.natDegree
  choose a ha hrep using fun i : Fin k ↦ (Q.coeff i).property
  let q : Polynomial ((Fin d → ℂ) → ℂ) := X ^ k + ∑ i : Fin k, C (a i) * X ^ (i : ℕ)
  have hmonic : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt a)
  have hform : Q = X ^ k + ∑ i : Fin k, C (Q.coeff i) * X ^ (i : ℕ) := by
    simpa only [← Fin.sum_univ_eq_sum_range] using hQ.as_sum
  have hcoeff (i : ℕ) : q.coeff i =
      (if i = k then 1 else 0) + ∑ j : Fin k, if (j : ℕ) = i then a j else 0 := by
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, eq_comm]
  have hmap : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      Q.map (analyticGermSubring d).subtype := by
    conv_rhs => rw [hform]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Germ.coe_coeRingHom, Subring.subtype_apply, hrep]
  refine ⟨q, hmonic, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [hcoeff]
    apply AnalyticAt.add
    · split_ifs <;> exact analyticAt_const
    · apply Finset.analyticAt_sum
      intro j _
      split_ifs <;> first | exact ha j | exact analyticAt_const
  · simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hmap

/-- Every germ polynomial has a polynomial of analytic representatives. -/
private theorem adim9_polynomial_representative {d : ℕ}
    (Q : Polynomial (AnalyticGerm d)) :
    ∃ q : Polynomial ((Fin d → ℂ) → ℂ),
      ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
        Germ.ofFun (q.coeff i) = (Q.coeff i).val := by
  classical
  choose a ha hrep using fun i ↦ (Q.coeff i).property
  let q : Polynomial ((Fin d → ℂ) → ℂ) :=
    Q.sum fun i _ ↦ Polynomial.monomial i (a i)
  refine ⟨q, fun i ↦ ?_⟩
  by_cases hi : i ∈ Q.support
  · simpa [q, Polynomial.sum, Polynomial.coeff_monomial, hi] using
      And.intro (ha i) (hrep i)
  · have hQi : Q.coeff i = 0 := by
      simpa [Polynomial.mem_support_iff] using hi
    simpa [q, Polynomial.sum, Polynomial.coeff_monomial, hi, hQi] using
      (And.intro (show AnalyticAt ℂ (0 : (Fin d → ℂ) → ℂ) 0 from analyticAt_const)
        (rfl : Germ.ofFun (0 : (Fin d → ℂ) → ℂ) = (0 : AnalyticGerm d).val))


/-- Primitive finite parameters have simultaneous analytic polynomial representatives
with a monic primitive equation and a denominator with nonzero germ. -/
private theorem adim9_primitive_representatives (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
      (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
      (R : Fin n → Polynomial (AnalyticGerm d))
      (B C : Polynomial (AnalyticGerm d)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      (∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T) ∧
      (∀ i, θ δ * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v)) ∧
      ∃ (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
        (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ)),
        q.Monic ∧
        (∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
          Germ.ofFun (q.coeff i) = (Q.coeff i).val) ∧
        AnalyticAt ℂ Δ 0 ∧ Germ.ofFun Δ = δ.val ∧
        (∀ j i, AnalyticAt ℂ ((r j).coeff i) 0 ∧
          Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val) ∧
        ¬ (Δ =ᶠ[𝓝 0] fun _ ↦ 0) := by
  obtain ⟨ℓ, v, Q, δ, R, B, C, hv, hℓ, hQ, hδ, hbezout, hmin, hcoord⟩ :=
    adim7_primitive_form n d P hP π θ hfinite hinj hcomp c hc
  obtain ⟨q, hqm, hq⟩ := adim9_monic_representative d Q hQ.1
  obtain ⟨Δ, hΔ, hΔrep⟩ := δ.property
  choose r hr using fun j ↦ adim9_polynomial_representative (R j)
  refine ⟨ℓ, v, Q, δ, R, B, C, hv, hℓ, hQ, hδ, hbezout, hmin, hcoord,
    q, Δ, r, hqm, hq, hΔ, hΔrep, hr, ?_⟩
  intro he
  apply hδ
  apply Subtype.ext
  rw [← hΔrep]
  exact Filter.EventuallyEq.germ_eq he


/-- A nonzero analytic germ in positive dimension stays nonzero on a suitably
rescaled punctured complex line inside any prescribed neighbourhood. -/
private theorem adim9_nonzero_germ_line {d : ℕ} (hd : 0 < d)
    (Δ : (Fin d → ℂ) → ℂ) (hΔ : AnalyticAt ℂ Δ 0)
    (hne : ¬ (Δ =ᶠ[𝓝 0] fun _ ↦ 0))
    (V : Set (Fin d → ℂ)) (hV : V ∈ 𝓝 (0 : Fin d → ℂ)) :
    ∃ e : Fin d → ℂ, e ≠ 0 ∧ ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      t • e ∈ V ∧ Δ (t • e) ≠ 0 := by
  have hex : ∃ v : Fin d → ℂ, v ≠ 0 ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), Δ (t • v) ≠ 0 := by
    by_cases hzero : Δ 0 = 0
    · obtain ⟨U, hUsub, hU, hU0⟩ := mem_nhds_iff.mp hΔ.eventually_analyticAt
      exact adim9_line_avoids_discriminant hU hU0 Δ
        (fun z hz ↦ hUsub hz) hzero hne
    · let v : Fin d → ℂ := fun _ ↦ 1
      have hv : v ≠ 0 := by
        intro h
        have := congrFun h ⟨0, hd⟩
        exact one_ne_zero this
      have hc : ContinuousAt (fun t : ℂ ↦ Δ (t • v)) 0 := by
        have houter : ContinuousAt Δ ((0 : ℂ) • v) := by
          simpa only [zero_smul] using hΔ.continuousAt
        exact houter.comp (f := fun t : ℂ ↦ t • v)
          (continuousAt_id.smul continuousAt_const)
      refine ⟨v, hv, ?_⟩
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      exact hc.eventually_ne (by simpa only [zero_smul] using hzero)
  obtain ⟨v, hv, hline⟩ := hex
  exact adim9_rescale_punctured_line V hV Δ v hv hline


/-- A polynomial identity between coefficient germs holds throughout some
neighbourhood, simultaneously in the polynomial variable. -/
private theorem adim9_polynomial_representatives_eq (d : ℕ)
    (p q : Polynomial ((Fin d → ℂ) → ℂ))
    (h : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)))) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      p.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) =
        q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) := by
  classical
  have hc (i : ℕ) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), p.coeff i w = q.coeff i w := by
    apply Germ.coe_eq.mp
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom] using congrArg (fun a ↦ a.coeff i) h
  have hs : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ i ∈ p.support ∪ q.support, p.coeff i w = q.coeff i w := by
    rw [Finset.eventually_all]
    exact fun i _ ↦ hc i
  filter_upwards [hs] with w hw
  ext i
  simp only [Polynomial.coeff_map, Pi.evalRingHom_apply]
  by_cases hi : i ∈ p.support ∪ q.support
  · exact hw i hi
  · have hp : p.coeff i = 0 := Polynomial.notMem_support_iff.mp
      (fun hip ↦ hi (Finset.mem_union_left _ hip))
    have hq : q.coeff i = 0 := Polynomial.notMem_support_iff.mp
      (fun hiq ↦ hi (Finset.mem_union_right _ hiq))
    rw [hp, hq]

/-- The primitive Bezout denominator excludes repeated roots of every nearby
representative polynomial wherever that denominator is nonzero. -/
private theorem adim9_separable_off_denominator {d : ℕ}
    (Q B C : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (hbezout : B * Q + C * Q.derivative = Polynomial.C δ)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), Δ w ≠ 0 →
      (q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)).Separable := by
  obtain ⟨b, hb⟩ := adim9_polynomial_representative B
  obtain ⟨c, hc⟩ := adim9_polynomial_representative C
  have hmap (F : Polynomial (AnalyticGerm d))
      (f : Polynomial ((Fin d → ℂ) → ℂ))
      (hf : ∀ i, Germ.ofFun (f.coeff i) = (F.coeff i).val) :
      f.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        F.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hf i
  have heq : (b * q + c * q.derivative).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      (Polynomial.C Δ).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, hmap Q q hq,
      hmap B b (fun i ↦ (hb i).2), hmap C c (fun i ↦ (hc i).2),
      Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, hbezout]
    simp only [Polynomial.map_C, Germ.coe_coeRingHom, Subring.subtype_apply, hΔ]
  filter_upwards [adim9_polynomial_representatives_eq d _ _ heq] with w hw hne
  let ev := Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w
  have hid : b.map ev * q.map ev + c.map ev * (q.map ev).derivative =
      Polynomial.C (Δ w) := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.derivative_map, Pi.evalRingHom_apply] using hw
  rw [Polynomial.separable_def']
  refine ⟨Polynomial.C (Δ w)⁻¹ * b.map ev,
    Polynomial.C (Δ w)⁻¹ * c.map ev, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, hid, ← Polynomial.C_mul, inv_mul_cancel₀ hne,
    Polynomial.C_1]


/-- An accumulation point has a minimal component with faithful finite parameters
of positive dimension, in every ambient dimension. -/
private theorem adim9_component_parameters_at_accumulation {n : ℕ}
    (K : Set (Fin n → ℂ)) (x : Fin n → ℂ) (hxK : x ∈ K)
    (hx : AccPt x (𝓟 K)) :
    ∃ P ∈ (adim2_ideal n (adim2_germ n K x)).minimalPrimes,
      ∃ (d : ℕ) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
        (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)),
        0 < d ∧ d ≤ n ∧ θ.Finite ∧ Function.Injective θ ∧
        (∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
          AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
          Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b) ∧
        ringKrullDim (AnalyticGerm n ⧸ P) = (d : WithBot ℕ∞) := by
  have hproper : adim2_ideal n (adim2_germ n K x) ≠ ⊤ := by
    intro htop
    have hone : (1 : AnalyticGerm n) ∈ adim2_ideal n (adim2_germ n K x) := by
      rw [htop]
      trivial
    change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ K → (1 : ℂ) = 0 at hone
    exact one_ne_zero (hone.self_of_nhds (by simpa using hxK))
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hproper
  obtain ⟨d, π, θ, hdle, hfinite, hinj, hcomp, hdim⟩ :=
    adim5_finite_parameters n P hP.isPrime
  have hquot : ringKrullDim (AnalyticGerm n ⧸ P) = (d : WithBot ℕ∞) := by
    rw [← adim6_parameter_dimension d]
    exact hdim.symm
  have hd : 0 < d := by
    have hpos := adim9_positive_dimension_at_accumulation K x hx P hP
    rw [hquot] at hpos
    have : 1 ≤ d := by exact_mod_cast hpos
    omega
  exact ⟨P, hP, d, π, θ, hd, hdle, hfinite, hinj, hcomp, hquot⟩


private theorem adim9_polynomial_roots_of_germ_dvd (d : ℕ)
    (p q : Polynomial ((Fin d → ℂ) → ℂ))
    (h : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) ∣
      p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)))) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ,
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        p.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 := by
  obtain ⟨S, hS⟩ := h
  have hsurj : Function.Surjective (Germ.coeRingHom (R := ℂ) (𝓝 (0 : Fin d → ℂ))) :=
    Quot.mk_surjective
  obtain ⟨s, hs⟩ := Polynomial.map_surjective _ hsurj S
  have heq : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      (q * s).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
    rw [Polynomial.map_mul, hs, hS]
  filter_upwards [adim9_polynomial_representatives_eq d p (q * s) heq] with w hw
  intro t ht
  have := congrArg (fun a : Polynomial ℂ ↦ a.eval t) hw
  simpa only [Polynomial.eval_map, Polynomial.eval₂_mul, ht, zero_mul] using this

private theorem adim9_polynomial_roots_of_relation (d : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q T : Polynomial (AnalyticGerm d))
    (hmin : ∀ S : Polynomial (AnalyticGerm d), S.eval₂ θ v = 0 ↔ Q ∣ S)
    (hT : T.eval₂ θ v = 0)
    (q p : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ,
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        p.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 := by
  apply adim9_polynomial_roots_of_germ_dvd d p q
  have hqmap : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      Q.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hq i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hp i
  rw [hqmap, hpmap]
  obtain ⟨S, hS⟩ := (hmin T).mp hT
  exact ⟨S.map (analyticGermSubring d).subtype, by rw [hS, Polynomial.map_mul]⟩

private theorem adim9_linear_relation {A B : Type*} [CommRing A] [CommRing B]
    (n : ℕ) (θ : A →+* B) (v : B) (δ : A) (c : Fin n → B)
    (R : Fin n → Polynomial A) (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin n → A) (S : Polynomial A)
    (hlinear : ∑ i, θ (a i) * c i = S.eval₂ θ v) :
    (∑ i, C (a i) * R i - C δ * S).eval₂ θ v = 0 := by
  rw [Polynomial.eval₂_sub, sub_eq_zero]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rw [← hlinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hcoord i]
  ring

private theorem adim9_linear_reconstruction (n d : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (c : Fin n → B) (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin n → AnalyticGerm d) (S : Polynomial (AnalyticGerm d))
    (hlinear : ∑ i, θ (a i) * c i = S.eval₂ θ v)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (a₀ : Fin n → (Fin d → ℂ) → ℂ) (s : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ha : ∀ i, Germ.ofFun (a₀ i) = (a i).val)
    (hs : ∀ i, Germ.ofFun (s.coeff i) = (S.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∑ i, a₀ i w *
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
          s.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t := by
  classical
  let T := ∑ i, C (a i) * R i - C δ * S
  let p := ∑ i, C (a₀ i) * r i - C Δ * s
  have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (G : Polynomial (AnalyticGerm d))
      (hFG : ∀ i, Germ.ofFun (F.coeff i) = (G.coeff i).val) :
      F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        G.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hFG i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    simp only [p, T, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Germ.coe_coeRingHom, Subring.subtype_apply, hΔ, ha,
      hmap s S hs, hmap _ _ (hr _)]
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  have hT := adim9_linear_relation n θ v δ c R hcoord a S hlinear
  filter_upwards [adim9_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have heq := hw t ht
  simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Pi.evalRingHom_apply, sub_eq_zero] at heq
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, heq, mul_div_cancel_left₀ _ hΔw]

private theorem adim9_linear_germ_identity (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (L : (Fin n → ℂ) →L[ℂ] ℂ) (b : AnalyticGerm n)
    (hb : b.val = Germ.ofFun (fun z ↦ L z))
    (a : Fin n → AnalyticGerm d)
    (ha : ∀ i, Germ.ofFun (fun _ : Fin d → ℂ ↦ L (Pi.single i 1)) = (a i).val) :
    ∑ i, θ (a i) * Ideal.Quotient.mk P (c i) = Ideal.Quotient.mk P b := by
  classical
  let a' : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun _ ↦ L (Pi.single i 1)), _, analyticAt_const, rfl⟩
  have hθ (i : Fin n) : θ (a i) = Ideal.Quotient.mk P (a' i) :=
    hcomp (a i) (fun _ ↦ L (Pi.single i 1)) analyticAt_const (ha i) (a' i) rfl
  simp_rw [hθ, ← map_mul, ← map_sum]
  congr 1
  apply Subtype.ext
  change (analyticGermSubring n).subtype (∑ i, a' i * c i) = b.val
  rw [map_sum, hb]
  simp only [map_mul, Subring.subtype_apply, hc]
  change (∑ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun _ ↦ L (Pi.single i 1)) *
    Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ z i)) =
      Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ L z)
  simp only [← map_mul, ← map_sum]
  congr 1
  funext z
  simp only [Finset.sum_apply, Pi.mul_apply]
  conv_rhs => rw [pi_eq_sum_univ' z]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

private theorem adim9_linear_form_reconstruction (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (L : (Fin n → ℂ) →L[ℂ] ℂ) (b : AnalyticGerm n)
    (hb : b.val = Germ.ofFun (fun z ↦ L z))
    (S : Polynomial (AnalyticGerm d)) (s : Polynomial ((Fin d → ℂ) → ℂ))
    (hS : S.eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b)
    (hs : ∀ i, Germ.ofFun (s.coeff i) = (S.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      L (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
        s.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t := by
  classical
  let a : Fin n → AnalyticGerm d := fun i ↦
    ⟨Germ.ofFun (fun _ ↦ L (Pi.single i 1)), _, analyticAt_const, rfl⟩
  have hlinear : ∑ i, θ (a i) * Ideal.Quotient.mk P (c i) =
      S.eval₂ θ (Ideal.Quotient.mk P v) := by
    rw [hS]
    exact adim9_linear_germ_identity n d P π θ hcomp c hc L b hb a (fun _ ↦ rfl)
  filter_upwards [adim9_linear_reconstruction n d θ (Ideal.Quotient.mk P v) Q δ
    (fun i ↦ Ideal.Quotient.mk P (c i)) R hmin hcoord a S hlinear q Δ r
    (fun i _ ↦ L (Pi.single i 1)) s hq hΔ hr (fun _ ↦ rfl) hs] with w hw
  intro t hΔw ht
  rw [← hw t hΔw ht]
  conv_lhs => rw [pi_eq_sum_univ'
    (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w)]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

private theorem adim9_reconstructed_projection_and_primitive (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z)) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin n → ℂ := fun i ↦
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
      π z = w ∧ ℓ z = t := by
  classical
  have hX : ∀ i : ℕ,
      Germ.ofFun ((X : Polynomial ((Fin d → ℂ) → ℂ)).coeff i) =
        ((X : Polynomial (AnalyticGerm d)).coeff i).val := by
    intro i
    simp only [Polynomial.coeff_X]
    split_ifs <;> rfl
  have hℓ := adim9_linear_form_reconstruction n d P π θ hcomp c hc v Q δ R
    hmin hcoord q Δ r hq hΔ hr ℓ v hv X X (by simp only [Polynomial.eval₂_X]) hX
  have hπ (k : Fin d) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      (π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t /
        Δ w)) k = w k := by
    let L := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).comp π
    let b : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ L z), _, L.analyticAt 0, rfl⟩
    let a : AnalyticGerm d := ⟨Germ.ofFun (fun w ↦ w k), _,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).analyticAt 0, rfl⟩
    have hS : (C a).eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b := by
      rw [Polynomial.eval₂_C]
      exact hcomp a (fun w ↦ w k)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).analyticAt 0)
          (by rfl) b rfl
    have hs : ∀ i, Germ.ofFun ((C (fun w : Fin d → ℂ ↦ w k)).coeff i) =
        ((C a).coeff i).val := by
      intro i
      simp only [Polynomial.coeff_C]
      split_ifs <;> rfl
    simpa only [Polynomial.eval₂_C, Pi.evalRingHom_apply, L,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      adim9_linear_form_reconstruction n d P π θ hcomp c hc v Q δ R hmin hcoord
        q Δ r hq hΔ hr L b rfl (C a) (C (fun w ↦ w k)) hS hs
  have hπall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ k : Fin d, ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      (π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t /
        Δ w)) k = w k := by
    rw [Filter.eventually_all]
    exact hπ
  filter_upwards [hℓ, hπall] with w hwℓ hwπ
  intro t hΔw ht
  refine ⟨funext (fun k ↦ hwπ k t hΔw ht), ?_⟩
  simpa only [Polynomial.eval₂_X] using hwℓ t hΔw ht

private theorem adim9_coordinate_relation (d : ℕ) {B : Type*} [CommRing B]
    (θ : AnalyticGerm d →+* B) (v x : B)
    (Q W R : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : θ δ * x = R.eval₂ θ v) (hW : W.Monic) (hWx : W.eval₂ θ x = 0)
    (q u r : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hu : ∀ i, Germ.ofFun (u.coeff i) = (W.coeff i).val) (humonic : u.Monic)
    (hr : ∀ i, Germ.ofFun (r.coeff i) = (R.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
        (r.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) = 0 := by
  let T := (W.scaleRoots δ).comp R
  let p := (u.scaleRoots Δ).comp r
  have hT : T.eval₂ θ v = 0 := by
    rw [Polynomial.eval₂_comp, ← hcoord]
    exact Polynomial.scaleRoots_eval₂_eq_zero θ hWx
  have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (G : Polynomial (AnalyticGerm d))
      (hFG : ∀ i, Germ.ofFun (F.coeff i) = (G.coeff i).val) :
      F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        G.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hFG i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    rw [Polynomial.map_comp, Polynomial.map_comp,
      Polynomial.map_scaleRoots u Δ _ (by rw [humonic.leadingCoeff, map_one]; exact one_ne_zero),
      Polynomial.map_scaleRoots W δ _ (by rw [hW.leadingCoeff, map_one]; exact one_ne_zero),
      hmap u W hu, hmap r R hr]
    congr 2
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  filter_upwards [adim9_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have hz := hw t ht
  rw [Polynomial.eval₂_comp] at hz
  have heq := Polynomial.scaleRoots_eval₂_mul (p := u)
    (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
    (r.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) Δ
  simp only [Pi.evalRingHom_apply, mul_div_cancel₀ _ hΔw] at heq
  rw [hz] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hΔw)

private theorem adim9_coordinate_weierstrass (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    ∀ i, ∃ W : Polynomial (AnalyticGerm d), IsWeierstrassPolynomial W ∧
      W.eval₂ θ (Ideal.Quotient.mk P (c i)) = 0 := by
  have hlocal : ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b := by
    intro a b hab
    obtain ⟨fa, hfa, hfarep⟩ := a.property
    let b' : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ fa (π z)), _,
      hfa.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
    have hab' : θ a = Ideal.Quotient.mk P b' := hcomp a fa hfa hfarep b' rfl
    have hdiff : b - b' ∈ P :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem b b').mp (hab.symm.trans hab')
    have hzero : analyticGermValue n (b - b') = 0 := by
      by_contra hne
      exact hP (P.eq_top_of_isUnit_mem hdiff ((analyticGerm_isUnit_iff _).mpr hne))
    have hval : analyticGermValue n b = analyticGermValue n b' := by
      simpa only [map_sub, sub_eq_zero] using hzero
    rw [hval]
    change a.val.value = b'.val.value
    rw [← hfarep]
    change (Germ.ofFun fa).value = (Germ.ofFun (fun z ↦ fa (π z))).value
    simp only [Germ.value_ofFun, map_zero]
  intro i
  apply adim5_distinguished_relation n d P hP θ hfinite hlocal (c i)
  change (c i).val.value = 0
  rw [hc i]
  rfl

private theorem adim9_weierstrass_representative (d : ℕ)
    (Q : Polynomial (AnalyticGerm d)) (q : Polynomial ((Fin d → ℂ) → ℂ))
    (hQ : IsWeierstrassPolynomial Q)
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val) :
    ∃ (k : ℕ) (a : Fin k → (Fin d → ℂ) → ℂ),
      0 < k ∧ (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t =
          AnalyticDivisorAlgebraic4.monicInLast a (w, t) := by
  classical
  let k := Q.natDegree
  let a : Fin k → (Fin d → ℂ) → ℂ := fun i ↦ q.coeff i
  have hk : 0 < k := hQ.2.1
  have ha : ∀ i, AnalyticAt ℂ (a i) 0 := fun i ↦ (hq i).1
  have ha0 : ∀ i, a i 0 = 0 := by
    intro i
    have hi := hQ.2.2 i i.isLt
    change (Q.coeff i).val.value = 0 at hi
    rw [← (hq i).2] at hi
    simpa [a] using hi
  have hlead : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), q.coeff k w = 1 := by
    apply Filter.Germ.coe_eq.mp
    rw [(hq k).2]
    have hcoeff : Q.coeff k = 1 := hQ.1.coeff_natDegree
    rw [hcoeff]
    rfl
  have hkq : k ≤ q.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hw := hlead.self_of_nhds
    rw [hz] at hw
    norm_num at hw
  have hhigh : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ j ∈ Finset.Ioc k q.natDegree, q.coeff j w = 0 := by
    rw [Finset.eventually_all]
    intro j hj
    apply Filter.Germ.coe_eq.mp
    rw [(hq j).2, Polynomial.coeff_eq_zero_of_natDegree_lt (Finset.mem_Ioc.mp hj).1]
    rfl
  refine ⟨k, a, hk, ha, ha0, ?_⟩
  filter_upwards [hlead, hhigh] with w hwlead hwhigh
  intro t
  rw [Polynomial.eval₂_eq_sum_range]
  simp only [Pi.evalRingHom_apply]
  rw [show ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i w * t ^ i =
      t ^ k + ∑ i : Fin k, q.coeff i w * t ^ (i : ℕ) by
    calc
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i w * t ^ i =
          ∑ i ∈ Finset.range (k + 1), q.coeff i w * t ^ i := by
            symm
            apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkq))
            intro j hjbig hjsmall
            rw [hwhigh j]
            · simp
            · simp only [Finset.mem_Ioc]
              simp only [Finset.mem_range, not_lt] at hjsmall
              simp only [Finset.mem_range, Nat.lt_succ_iff] at hjbig
              omega
      _ = (∑ i ∈ Finset.range k, q.coeff i w * t ^ i) +
          q.coeff k w * t ^ k := by rw [Finset.sum_range_succ]
      _ = t ^ k + ∑ i : Fin k, q.coeff i w * t ^ (i : ℕ) := by
          rw [hwlead, one_mul, add_comm, ← Fin.sum_univ_eq_sum_range]]
  rfl

private theorem adim9_reconstructed_coordinates_small (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∀ i, ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w‖ < ε := by
  classical
  have hsmall (i : Fin n) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w‖ < ε := by
    obtain ⟨W, hW, hWx⟩ := adim9_coordinate_weierstrass n d P hP π θ hfinite hcomp c hc i
    obtain ⟨u, humonic, hu⟩ := adim9_monic_representative d W hW.1
    obtain ⟨k, a, _, ha, ha0, hform⟩ := adim9_weierstrass_representative d W u hW hu
    have hbound := AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small
      (fun j ↦ (ha j).continuousAt) ha0 hε
    have hrelation := adim9_coordinate_relation d θ (Ideal.Quotient.mk P v)
      (Ideal.Quotient.mk P (c i)) Q W (R i) δ hmin (hcoord i) hW.1 hWx
      q u (r i) Δ hq (fun j ↦ (hu j).2) humonic (hr i) hΔ
    filter_upwards [hform, hbound, hrelation] with w hwform hwbound hwrelation
    intro t hΔw ht
    apply hwbound
    rw [← hwform]
    exact hwrelation t hΔw ht
  have hall := Filter.eventually_all.mpr hsmall
  filter_upwards [hall] with w hw
  exact fun t hΔw ht i ↦ hw i t hΔw ht


/-- Finitely supported analytic polynomial coefficients are analytic together
on one neighbourhood, including the zero coefficients outside the support. -/
private theorem adim9_coefficients_eventually_analytic {d : ℕ}
    (q : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ i, AnalyticAt ℂ (q.coeff i) w := by
  classical
  have hfinite : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ i ∈ q.support, AnalyticAt ℂ (q.coeff i) w := by
    rw [Finset.eventually_all]
    exact fun i _ ↦ (hq i).eventually_analyticAt
  filter_upwards [hfinite] with w hw i
  by_cases hi : i ∈ q.support
  · exact hw i hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    exact analyticAt_const

/-- Primitive representatives yield a regular line on which the denominator and
polynomial discriminant never vanish, inside any prescribed neighbourhood. -/
private theorem adim9_primitive_regular_line {n d : ℕ} (hd : 0 < d)
    (Q B C : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (hQ : IsWeierstrassPolynomial Q)
    (hbezout : B * Q + C * Q.derivative = Polynomial.C δ)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : AnalyticAt ℂ Δ 0) (hΔrep : Germ.ofFun Δ = δ.val)
    (hne : ¬ (Δ =ᶠ[𝓝 0] fun _ ↦ 0))
    (hr : ∀ j i, AnalyticAt ℂ ((r j).coeff i) 0)
    (V : Set (Fin d → ℂ)) (hV : V ∈ 𝓝 (0 : Fin d → ℂ)) :
    ∃ (k : ℕ) (a : Fin k → (Fin d → ℂ) → ℂ) (e : Fin d → ℂ),
      0 < k ∧ e ≠ 0 ∧ (∀ j, a j 0 = 0) ∧
      ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
        t • e ∈ V ∧ Δ (t • e) ≠ 0 ∧ AnalyticAt ℂ Δ (t • e) ∧
        (∀ j i, AnalyticAt ℂ ((r j).coeff i) (t • e)) ∧
        (∀ j, AnalyticAt ℂ (a j) (t • e)) ∧
        AnalyticDivisorAlgebraic5.weierstrassDiscr a (t • e) ≠ 0 ∧
        q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (t • e)) =
          AnalyticDivisorAlgebraic5.monicPoly a (t • e) := by
  obtain ⟨k, a, hk, ha, ha0, hform⟩ := adim9_weierstrass_representative d Q q hQ hq
  have hrnear := Filter.eventually_all.mpr fun j ↦
    adim9_coefficients_eventually_analytic (r j) (hr j)
  have hanear := Filter.eventually_all.mpr fun j ↦ (ha j).eventually_analyticAt
  have hsep := adim9_separable_off_denominator Q B C δ hbezout q Δ
    (fun i ↦ (hq i).2) hΔrep
  have hnear : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      w ∈ V ∧ AnalyticAt ℂ Δ w ∧ (∀ j i, AnalyticAt ℂ ((r j).coeff i) w) ∧
      (∀ j, AnalyticAt ℂ (a j) w) ∧
      (Δ w ≠ 0 → (q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)).Separable) ∧
      q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) =
        AnalyticDivisorAlgebraic5.monicPoly a w := by
    filter_upwards [hV, hΔ.eventually_analyticAt, hrnear, hanear, hsep, hform]
      with w hwV hwΔ hwr hwa hws hwf
    refine ⟨hwV, hwΔ, hwr, hwa, hws, Polynomial.funext fun z ↦ ?_⟩
    rw [Polynomial.eval_map, hwf,
      (AnalyticDivisorAlgebraic5.spec_monicPoly a w).2.2]
  obtain ⟨e, he, hline⟩ := adim9_nonzero_germ_line hd Δ hΔ hne _ hnear
  refine ⟨k, a, e, hk, he, ha0, ?_⟩
  intro t ht
  obtain ⟨⟨hVt, hΔt, hrt, hat, hsept, hformt⟩, hnet⟩ := hline t ht
  refine ⟨hVt, hnet, hΔt, hrt, hat, ?_, hformt⟩
  apply (AnalyticDivisorAlgebraic5.gaga5b_discr_ne_zero_iff_separable
    (AnalyticDivisorAlgebraic5.spec_monicPoly a (t • e)).1).mpr
  rw [← hformt]
  exact hsept hnet


/-- An existentially admissible primitive root over each parameter suffices for
an analytic disc; projection and shrinking hold for all reconstructed roots. -/
private theorem adim9_disc_from_primitive_candidates {n d k : ℕ}
    (a : Fin k → (Fin d → ℂ) → ℂ) (e : Fin d → ℂ) (he : e ≠ 0)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (ha : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ j, AnalyticAt ℂ (a j) (t • e))
    (hdiscr : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 →
      AnalyticDivisorAlgebraic5.weierstrassDiscr a (t • e) ≠ 0)
    (hr : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ j i,
      AnalyticAt ℂ ((r j).coeff i) (t • e))
    (hΔ : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → AnalyticAt ℂ Δ (t • e))
    (hΔne : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → Δ (t • e) ≠ 0)
    (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ x ∈ V ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) V) ∧
        ∀ z ∈ V, (z ∈ K ↔ ∀ j, f j z = 0))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (hroot : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∃ v : ℂ,
      (AnalyticDivisorAlgebraic5.monicPoly a (t • e)).eval v = 0 ∧
      (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (t • e)) v /
        Δ (t • e)) ∈ K)
    (hproj : ∀ t : ℂ, t ≠ 0 ∧ ‖t‖ < 1 → ∀ v : ℂ,
      (AnalyticDivisorAlgebraic5.monicPoly a (t • e)).eval v = 0 →
      π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (t • e)) v /
        Δ (t • e)) = t • e)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ v : ℂ,
      (AnalyticDivisorAlgebraic5.monicPoly a (t • e)).eval v = 0 → ∀ i,
        ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (t • e)) v /
          Δ (t • e)‖ < ε) :
    ∃ G : ℂ → (Fin n → ℂ), AnalyticOnNhd ℂ G (Metric.ball 0 1) ∧
      MapsTo G (Metric.ball 0 1) K ∧ G 0 = 0 ∧
      ∃ u ∈ Metric.ball (0 : ℂ) 1, ∃ v ∈ Metric.ball (0 : ℂ) 1, G u ≠ G v := by
  obtain ⟨m, hm, ρ, hρ, henum⟩ := adim9_polynomial_power_roots a e ha hdiscr
  let w : ℂ → (Fin d → ℂ) := fun t ↦ t ^ m • e
  let g : Fin k → ℂ → (Fin n → ℂ) := fun j t i ↦
    (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (w t)) (ρ j t) / Δ (w t)
  let U : Set ℂ := {t | t ≠ 0 ∧ ‖t‖ < 1}
  have hU : IsOpen U := (isOpen_ne_fun continuous_id continuous_const).inter
    (isOpen_lt continuous_norm continuous_const)
  have hpow (t : ℂ) (ht : t ∈ U) : t ^ m ∈ U := by
    exact ⟨pow_ne_zero m ht.1, by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht.2 (Nat.ne_of_gt hm)⟩
  have hw (t : ℂ) : AnalyticAt ℂ w t :=
    (analyticAt_id.pow m).smul analyticAt_const
  have hg (j : Fin k) : AnalyticOnNhd ℂ (g j) U := by
    intro t ht
    apply analyticAt_pi_iff.mpr
    intro i
    exact (adim9_analytic_polynomial_eval (r i) w (ρ j) t (hw t) (hρ j t ht)
      (hr (t ^ m) (hpow t ht) i)).div
      ((show AnalyticAt ℂ Δ (w t) from hΔ (t ^ m) (hpow t ht)).comp (hw t))
      (hΔne (t ^ m) (hpow t ht))
  have hcover : ∀ t ∈ U, ∃ j, g j t ∈ K := by
    intro t ht
    obtain ⟨v, hv, hvK⟩ := hroot (t ^ m) (hpow t ht)
    obtain ⟨j, hj⟩ := (henum t ht v).mp hv
    exact ⟨j, by simpa only [g, w, hj] using hvK⟩
  have hUne : U.Nonempty := by
    refine ⟨(1 / 2 : ℂ), ?_, ?_⟩ <;> norm_num
  obtain ⟨j, hjK⟩ := adim9_select_admissible_analytic_branch K hK.isClosed hloc U hU hUne
    adim9_punctured_unit_disc_preconnected g hg hcover
  have hmem (t : ℂ) : t ∈ Metric.ball (0 : ℂ) 1 \ {0} ↔ t ∈ U := by
    simp only [Set.mem_diff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff, U,
      Set.mem_setOf_eq, and_comm]
  have hjroot (t : ℂ) (ht : t ∈ U) :
      (AnalyticDivisorAlgebraic5.monicPoly a (w t)).eval (ρ j t) = 0 :=
    (henum t ht _).mpr ⟨j, rfl⟩
  have hp : ∀ t ∈ Metric.ball (0 : ℂ) 1 \ {0}, π (g j t) = t ^ m • e := by
    intro t ht
    exact hproj (t ^ m) (hpow t ((hmem t).mp ht)) (ρ j t) (hjroot t ((hmem t).mp ht))
  have hpower : Tendsto (fun t : ℂ ↦ t ^ m) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hct : Continuous (fun t : ℂ ↦ t ^ m) := by fun_prop
      have ht := hct.tendsto (0 : ℂ)
      rw [zero_pow (Nat.ne_of_gt hm)] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_ne_zero m ht
  have hUnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ U := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with t ht htb
    exact ⟨ht, by simpa only [Metric.mem_ball, dist_zero_right] using htb⟩
  have hlim : Tendsto (g j) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hpower.eventually (hsmall ε hε), hUnear] with t ht htU
    simpa only [Pi.zero_apply, dist_zero_right] using ht (ρ j t) (hjroot t htU) i
  obtain ⟨G, hG, hGK, _, hG0, hne⟩ := adim9_extend_power_sheet_of_tendsto hK
    Metric.isOpen_ball (Metric.mem_ball_self zero_lt_one) π m hm e he (g j)
    (fun t ht ↦ hg j t ((hmem t).mp ht))
    (fun t ht ↦ hjK ((hmem t).mp ht)) hp hlim
  exact ⟨G, hG, hGK, hG0, hne⟩


/-- Generators of a component prime can include the original local equations,
so their representatives define points in the original set near the anchor. -/
private theorem adim9_prime_representatives {n : ℕ}
    (K : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (P : Ideal (AnalyticGerm n))
    (hIP : adim2_ideal n (adim2_germ n K x) ≤ P)
    (U₀ : Set (Fin n → ℂ)) (hU₀ : IsOpen U₀) (hxU₀ : x ∈ U₀)
    (m : ℕ) (f₀ : Fin m → (Fin n → ℂ) → ℂ)
    (hf₀ : ∀ j, AnalyticOnNhd ℂ (f₀ j) U₀)
    (hK₀ : ∀ z ∈ U₀, (z ∈ K ↔ ∀ j, f₀ j z = 0)) :
    ∃ (k : ℕ) (g : Fin k → AnalyticGerm n) (f : Fin k → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)),
      Ideal.span (Set.range g) = P ∧ IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
      (∀ j, Germ.ofFun (f j) = (g j).val) ∧
      ∀ z ∈ U, (∀ j, f j z = 0) → x + z ∈ K := by
  classical
  let a : Fin m → AnalyticGerm n := fun j ↦
    ⟨Germ.ofFun (fun z ↦ f₀ j (x + z)), _,
      (hf₀ j x hxU₀).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp), rfl⟩
  have haP (j : Fin m) : a j ∈ P := by
    apply hIP
    change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ K → f₀ j (x + z) = 0
    have htrans : ContinuousAt (fun z : Fin n → ℂ ↦ x + z) 0 :=
      continuousAt_const.add continuousAt_id
    filter_upwards [htrans.preimage_mem_nhds (hU₀.mem_nhds (by simpa using hxU₀))]
      with z hz hzK
    exact (hK₀ (x + z) hz).mp hzK j
  obtain ⟨k, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) P)
  choose f₁ hf₁ hrep₁ using fun j ↦ (b j).property
  let g : Fin (m + k) → AnalyticGerm n := Fin.addCases a b
  let f : Fin (m + k) → (Fin n → ℂ) → ℂ :=
    Fin.addCases (fun j z ↦ f₀ j (x + z)) f₁
  have hgen : Ideal.span (Set.range g) = P := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
      · change g (Fin.castAdd k i) ∈ P
        rw [show g (Fin.castAdd k i) = a i by simp only [g, Fin.addCases_left]]
        exact haP i
      · have hbi : b i ∈ P := by
          rw [← hb]
          exact Submodule.subset_span ⟨i, rfl⟩
        change g (Fin.natAdd m i) ∈ P
        rw [show g (Fin.natAdd m i) = b i by simp only [g, Fin.addCases_right]]
        exact hbi
    · rw [← hb]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨Fin.natAdd m i, by simp only [g, Fin.addCases_right]⟩
  have hnear : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      x + z ∈ U₀ ∧ ∀ j, AnalyticAt ℂ (f₁ j) z := by
    have htrans : ContinuousAt (fun z : Fin n → ℂ ↦ x + z) 0 :=
      continuousAt_const.add continuousAt_id
    filter_upwards [htrans.preimage_mem_nhds (hU₀.mem_nhds (by simpa using hxU₀)),
      Filter.eventually_all.mpr fun j ↦ (hf₁ j).eventually_analyticAt] with z hz han
    exact ⟨hz, han⟩
  obtain ⟨U, hUsub, hU, hU0⟩ := mem_nhds_iff.mp hnear
  refine ⟨m + k, g, f, U, hgen, hU, hU0, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp only [f, Fin.addCases_left]
      intro z hz
      exact (hf₀ i (x + z) (hUsub hz).1).comp (analyticAt_const.add analyticAt_id)
    · simp only [f, Fin.addCases_right]
      intro z hz
      exact (hUsub hz).2 i
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp only [f, g, Fin.addCases_left]
      rfl
    · simpa only [f, g, Fin.addCases_right] using hrep₁ i
  · intro z hz hzero
    apply (hK₀ (x + z) (hUsub hz).1).mpr
    intro i
    simpa only [f, Fin.addCases_left] using hzero (Fin.castAdd k i)


/-- A positive-dimensional finite component represented inside a compact locally
analytic set supplies a nonconstant analytic disc through the origin. -/
private theorem adim9_disc_of_finite_component {n d : ℕ}
    (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ x ∈ V ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) V) ∧
        ∀ z ∈ V, (z ∈ K ↔ ∀ j, f j z = 0))
    (hd : 0 < d) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (m : ℕ) (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val)
    (hUK : ∀ z ∈ U, (∀ j, f j z = 0) → z ∈ K) :
    ∃ G : ℂ → (Fin n → ℂ), AnalyticOnNhd ℂ G (Metric.ball 0 1) ∧
      MapsTo G (Metric.ball 0 1) K ∧ G 0 = 0 ∧
      ∃ u ∈ Metric.ball (0 : ℂ) 1, ∃ v ∈ Metric.ball (0 : ℂ) 1, G u ≠ G v := by
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), _,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  obtain ⟨ℓ, v, Q, δ, R, B, C, hv, _, hQ, hδ, hbezout, hmin, hcoord,
    q, Δ, r, _, hq, hΔ, hΔrep, hr, hne⟩ :=
    adim9_primitive_representatives n d P hP π θ hfinite hinj hcomp c hc
  obtain ⟨V₀, hV₀, hV₀0, hroots⟩ := adim7_roots_off_discriminant n d P hP π θ
    hfinite hinj hcomp c hc ℓ v hv Q δ R hQ hδ hmin hcoord
    q Δ r hq hΔ hΔrep hr m g hgen f U hU hU0 hf hrep
  have hprojection := adim9_reconstructed_projection_and_primitive n d P π θ hcomp c hc
    v Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep (fun j i ↦ (hr j i).2) ℓ hv
  have hV : {w | w ∈ V₀ ∧ ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin n → ℂ := fun i ↦
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
      π z = w ∧ ℓ z = t} ∈ 𝓝 (0 : Fin d → ℂ) :=
    Filter.Eventually.and (hV₀.mem_nhds hV₀0) hprojection
  obtain ⟨k, a, e, _, he, _, hline⟩ := adim9_primitive_regular_line hd Q B C δ hQ hbezout
    q Δ r hq hΔ hΔrep hne (fun j i ↦ (hr j i).1) _ hV
  have hpoly (t : ℂ) (ht : t ≠ 0 ∧ ‖t‖ < 1) (z : ℂ) :
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (t • e)) z =
        (AnalyticDivisorAlgebraic5.monicPoly a (t • e)).eval z := by
    rw [← Polynomial.eval_map, (hline t ht).2.2.2.2.2.2]
  apply adim9_disc_from_primitive_candidates a e he r Δ
    (fun t ht ↦ (hline t ht).2.2.2.2.1)
    (fun t ht ↦ (hline t ht).2.2.2.2.2.1)
    (fun t ht ↦ (hline t ht).2.2.2.1)
    (fun t ht ↦ (hline t ht).2.2.1)
    (fun t ht ↦ (hline t ht).2.1) K hK hloc π
  · intro t ht
    obtain ⟨z, hz, hzU, _, _, hzf⟩ :=
      hroots (t • e) (hline t ht).1.1 (hline t ht).2.1
    exact ⟨z, (hpoly t ht z).symm.trans hz, hUK _ hzU hzf⟩
  · intro t ht z hz
    exact ((hline t ht).1.2 z (hline t ht).2.1 ((hpoly t ht z).trans hz)).1
  · intro ε hε
    have hsmall := adim9_reconstructed_coordinates_small n d P hP.ne_top π θ hfinite
      hcomp c hc v Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep
      (fun j i ↦ (hr j i).2) ε hε
    have hparam : Tendsto (fun t : ℂ ↦ t • e) (𝓝[≠] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℂ ↦ t • e) 0 :=
        continuousAt_id.smul continuousAt_const
      simpa only [zero_smul] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hunit : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 ∧ ‖t‖ < 1 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with t ht htb
      exact ⟨ht, by simpa only [Metric.mem_ball, dist_zero_right] using htb⟩
    filter_upwards [hparam.eventually hsmall, hunit] with t hst ht
    intro z hz
    exact hst z (hline t ht).2.1 ((hpoly t ht z).trans hz)





private lemma adim9_exists_linear_observable_avoiding (n : ℕ)
    (s : Finset (Fin n → ℂ)) (z : Fin n → ℂ) (hz : z ∉ s) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ, ∀ w ∈ s, ℓ z ≠ ℓ w := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℂ) (v := fun w : {w // w ∈ s} ↦ z - w.1) (fun w ↦ sub_ne_zero.mpr <| by
      intro h
      apply hz
      simpa [h] using w.2)
  let ℓ : (Fin n → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap f
  refine ⟨ℓ, fun w hw h ↦ ?_⟩
  have hzero : f (z - w) = 0 := by
    simpa [ℓ, map_sub] using sub_eq_zero.mpr h
  exact (hf ⟨w, hw⟩) hzero

/-- Source: Demailly, Complex Analytic and Differential Geometry (2012), II, Theorem 5.9, p. 104. -/
theorem adim9_compact_analytic_finite_aux (n : ℕ) (K : Set (Fin n → ℂ))
    (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ K ↔ ∀ j, f j z = 0)) :
    K.Finite := by
  apply adim9_finite_of_discs_at_accumulation_points hK
  intro x hxK hx
  obtain ⟨P, hP, d, π, θ, hd, _, hfinite, hinj, hcomp, _⟩ :=
    adim9_component_parameters_at_accumulation K x hxK hx
  obtain ⟨U₀, hU₀, hxU₀, m₀, f₀, hf₀, hK₀⟩ := hloc x hxK
  obtain ⟨m, g, f, U, hgen, hU, hU0, hf, hrep, hUK⟩ :=
    adim9_prime_representatives K x P hP.le U₀ hU₀ hxU₀ m₀ f₀ hf₀ hK₀
  let K' : Set (Fin n → ℂ) := (fun z ↦ x + z) ⁻¹' K
  have hK' : IsCompact K' := (Homeomorph.addLeft x).isCompact_preimage.mpr hK
  have hloc' : ∀ y ∈ K', ∃ V : Set (Fin n → ℂ), IsOpen V ∧ y ∈ V ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) V) ∧
        ∀ z ∈ V, (z ∈ K' ↔ ∀ j, f j z = 0) := by
    intro y hy
    obtain ⟨V, hV, hyV, k, F, hF, hKV⟩ := hloc (x + y) hy
    refine ⟨(fun z ↦ x + z) ⁻¹' V,
      hV.preimage (continuous_const.add continuous_id), hyV,
      k, fun j z ↦ F j (x + z), ?_, ?_⟩
    · intro j z hz
      exact (hF j (x + z) hz).comp (analyticAt_const.add analyticAt_id)
    · intro z hz
      exact hKV (x + z) hz
  obtain ⟨G, hG, hGK, hG0, u, hu, v, hv, huv⟩ :=
    adim9_disc_of_finite_component K' hK' hloc' hd P hP.isPrime π θ hfinite hinj hcomp
      m g hgen f U hU hU0 hf hrep hUK
  refine ⟨Metric.ball 0 1, 0, fun t ↦ x + G t, Metric.isOpen_ball,
    (convex_ball (0 : ℂ) 1).isPreconnected, Metric.mem_ball_self zero_lt_one,
    ?_, ?_, ?_, u, hu, v, hv, ?_⟩
  · intro t ht
    exact analyticAt_const.add (hG t ht)
  · intro t ht
    exact hGK ht
  · simp only [hG0, add_zero]
  · exact fun h ↦ huv (add_left_cancel h)


private theorem adim9_exists_boundary_radius (n d : ℕ) (A : Set (Fin n → ℂ))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (R : ℝ)
    (hboundary : ∀ z ∈ closure A, ‖z‖ = R → π z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ closure A, ‖z‖ = R → ε < ‖π z‖ := by
  let S : Set (Fin n → ℂ) := closure A ∩ Metric.sphere 0 R
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun z hzA hzR ↦ ?_⟩
    have hzS : z ∈ S := ⟨hzA, by simpa [Metric.mem_sphere, dist_zero_right] using hzR⟩
    simpa [hS] using hzS
  · have hSc : IsCompact S :=
      (isCompact_sphere (0 : Fin n → ℂ) R).inter_left isClosed_closure
    obtain ⟨u, huS, hu⟩ := hSc.exists_isMinOn hS
      (π.continuous.norm.continuousOn)
    have huA : u ∈ closure A := huS.1
    have huR : ‖u‖ = R := by
      simpa [Metric.mem_sphere, dist_zero_right] using huS.2
    have hπu : 0 < ‖π u‖ := norm_pos_iff.mpr (hboundary u huA huR)
    refine ⟨‖π u‖ / 2, half_pos hπu, fun z hzA hzR ↦ ?_⟩
    have hzS : z ∈ S := ⟨hzA, by simpa [Metric.mem_sphere, dist_zero_right] using hzR⟩
    exact (half_lt_self hπu).trans_le (hu hzS)

/-- The boundary input concerns the missing origin, not a germ at a point of A.
Source: Demailly, Complex Analytic and Differential Geometry (2012),
II, proof of Theorem 8.7, pp. 119--120, boundary separation and compact fibres. -/
theorem adim9_punctured_confinement_aux (n d : ℕ) (A : Set (Fin n → ℂ))
    (hzero : (0 : Fin n → ℂ) ∉ A)
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ A})
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (R : ℝ) (hR : 0 < R)
    (hboundary : ∀ z ∈ closure A, ‖z‖ = R → π z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ p : {z : Fin n → ℂ // z ∈ A ∧ ‖z‖ < R ∧ ‖π z‖ < ε ∧ π z ≠ 0} →
        {w : Fin d → ℂ // ‖w‖ < ε ∧ w ≠ 0},
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        ∀ w, (p ⁻¹' {w}).Finite := by
  classical
  obtain ⟨ε, hε, hεboundary⟩ := adim9_exists_boundary_radius n d A π R hboundary
  let Z := {z : Fin n → ℂ // z ∈ A ∧ ‖z‖ < R ∧ ‖π z‖ < ε ∧ π z ≠ 0}
  let D := {w : Fin d → ℂ // ‖w‖ < ε ∧ w ≠ 0}
  let p : Z → D := fun z ↦ ⟨π z.val, z.property.2.2⟩
  have hpProper : IsProperMap p := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨?_, ?_⟩
    · apply Continuous.subtype_mk
      exact π.continuous.comp continuous_subtype_val
    intro K hK
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    let KV : Set (Fin d → ℂ) := Subtype.val '' K
    have hKV : IsCompact KV := hK.image continuous_subtype_val
    let C : Set (Fin n → ℂ) := Metric.closedBall 0 R ∩ π ⁻¹' KV
    have hC : IsCompact C :=
      (isCompact_closedBall (0 : Fin n → ℂ) R).inter_right
        (hKV.isClosed.preimage π.continuous)
    have hCπ (z : C) : π z.val ≠ 0 := by
      obtain ⟨w, hwK, hw⟩ := z.property.2
      rw [← hw]
      exact w.property.2
    let q : C → {z : Fin n → ℂ // z ≠ 0} := fun z ↦ ⟨z.val, fun hz ↦ hCπ z (by simp [hz])⟩
    have hq : Continuous q := by fun_prop
    let T : Set C := q ⁻¹' {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ A}
    have hT : IsCompact T := by
      have hCu : IsCompact (Set.univ : Set C) := by
        rw [IsEmbedding.subtypeVal.isCompact_iff]
        simpa using hC
      simpa [T] using hCu.inter_right (hclosed.preimage hq)
    have himg := hT.image (show Continuous (fun z : C ↦ z.val) by fun_prop)
    convert himg using 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hpxK : p x ∈ K := by simpa using hx
      let c : C := ⟨x.val, by
        refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using x.property.2.1.le,
          ⟨p x, hpxK, rfl⟩⟩⟩
      refine ⟨c, ?_, rfl⟩
      exact x.property.1
    · rintro ⟨x, hx, rfl⟩
      have hxA : x.val ∈ A := hx
      obtain ⟨w, hwK, hw⟩ := x.property.2
      have hwε : ‖π x.val‖ < ε := by rw [← hw]; exact w.property.1
      have hw0 : π x.val ≠ 0 := by rw [← hw]; exact w.property.2
      have hxRle : ‖x.val‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using x.property.1
      have hxR : ‖x.val‖ < R := by
        apply lt_of_le_of_ne hxRle
        intro heq
        have hcl : x.val ∈ closure A := subset_closure hxA
        exact (not_lt_of_ge (hεboundary x.val hcl heq).le) hwε
      let z : Z := ⟨x.val, hxA, hxR, hwε, hw0⟩
      refine ⟨z, ?_, rfl⟩
      change p z ∈ K
      have : p z = w := Subtype.ext (by simpa [p, z] using hw.symm)
      simpa [this] using hwK
  refine ⟨ε, hε, p, fun _ ↦ rfl, hpProper, ?_⟩
  · intro w
    have hc : IsCompact (p ⁻¹' {w}) :=
      hpProper.isCompact_preimage isCompact_singleton
    have hvfinite : (Subtype.val '' (p ⁻¹' {w}) : Set (Fin n → ℂ)).Finite := by
      apply adim9_compact_analytic_finite_aux n _ (hc.image continuous_subtype_val)
      rintro x ⟨z, hz, rfl⟩
      obtain ⟨U, hU, hzU, hU0, m, f, hf, hzero⟩ := hloc z.val z.property.1
      let W := U ∩ {x | ‖x‖ < R} ∩ π ⁻¹' Metric.ball (π z.val) 1
      refine ⟨W, hU.inter (isOpen_lt continuous_norm continuous_const) |>.inter
          (Metric.isOpen_ball.preimage π.continuous), ?_, m + d, ?_, ?_, ?_⟩
      · refine ⟨⟨hzU, z.property.2.1⟩, ?_⟩
        simp
      · intro i x
        exact Sum.elim f (fun j y ↦ π y j - (π z.val) j) (finSumFinEquiv.symm i) x
      · intro i
        rcases finSumFinEquiv.symm i with i | j
        · exact (hf i).mono (inter_subset_left.trans inter_subset_left)
        · exact ((((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) j).comp π).analyticOnNhd W).sub
            analyticOnNhd_const)
      · intro y hy
        constructor
        · rintro ⟨a, ha, rfl⟩
          have hpw : p a = w := by simpa using ha
          intro i
          rcases finSumFinEquiv.symm i with i | j
          · exact (hzero a.val (inter_subset_left (inter_subset_left hy))).mp a.property.1 i
          · have hpaz : π a.val = π z.val := by
              calc π a.val = (p a).val := rfl
                _ = w.val := congrArg Subtype.val hpw
                _ = (p z).val := congrArg Subtype.val hz.symm
                _ = π z.val := rfl
            exact sub_eq_zero.mpr (congrFun hpaz j)
        · intro hall
          have hyA : y ∈ A := (hzero y (inter_subset_left (inter_subset_left hy))).mpr fun i ↦
            by simpa using hall (finSumFinEquiv (Sum.inl i))
          have hπy : π y = π z.val := by
            ext j
            exact sub_eq_zero.mp (by simpa using hall (finSumFinEquiv (Sum.inr j)))
          have hyε : ‖π y‖ < ε := by simpa [hπy] using z.property.2.2.1
          have hy0 : π y ≠ 0 := by simpa [hπy] using z.property.2.2.2
          let a : Z := ⟨y, hyA, hy.1.2, hyε, hy0⟩
          refine ⟨a, ?_, rfl⟩
          change p a = w
          exact (Subtype.ext hπy).trans hz
    exact Set.Finite.of_finite_image hvfinite Subtype.val_injective.injOn

private theorem adim9_analytic_coeff_root_product {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set E} (u : Finset ι) {r : ι → E → ℂ}
    (hr : ∀ j ∈ u, AnalyticOnNhd ℂ (r j) D) (i : ℕ) :
    AnalyticOnNhd ℂ (fun x ↦ (∏ j ∈ u, (Polynomial.X - Polynomial.C (r j x))).coeff i) D := by
  classical
  induction u using Finset.induction_on generalizing i with
  | empty => simpa only [Finset.prod_empty] using analyticOnNhd_const
  | @insert j u hju ih =>
      simp only [Finset.prod_insert hju, Polynomial.coeff_mul]
      apply Finset.analyticOnNhd_fun_sum
      intro q hq
      apply AnalyticOnNhd.mul _ (ih (fun l hl ↦ hr l (Finset.mem_insert_of_mem hl)) q.2)
      have hj := hr j (Finset.mem_insert_self j u)
      cases q.1 with
      | zero =>
          simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
            Polynomial.coeff_C_zero, zero_sub] using! hj.neg
      | succ l =>
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_succ, sub_zero]
          exact analyticOnNhd_const

private theorem adim9_norm_coeff_root_product_le {ι : Type*} (u : Finset ι)
    (r : ι → ℂ) (R : ℝ) (hR : 0 ≤ R) (hr : ∀ j ∈ u, ‖r j‖ ≤ R) (i : ℕ) :
    ‖(∏ j ∈ u, (Polynomial.X - Polynomial.C (r j))).coeff i‖ ≤ (1 + R) ^ u.card := by
  classical
  induction u using Finset.induction_on generalizing i with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
      split <;> simp
  | @insert j u hju ih =>
      rw [Finset.prod_insert hju, Finset.card_insert_of_notMem hju, pow_succ']
      cases i with
      | zero =>
          rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub,
            neg_mul, norm_neg, norm_mul, ← Polynomial.coeff_zero_eq_eval_zero]
          calc
            ‖r j‖ * ‖(∏ l ∈ u, (X - C (r l))).coeff 0‖
                ≤ R * (1 + R) ^ u.card := mul_le_mul (hr j (Finset.mem_insert_self j u))
                  (ih (fun l hl ↦ hr l (Finset.mem_insert_of_mem hl)) 0) (norm_nonneg _) hR
            _ ≤ (1 + R) * (1 + R) ^ u.card := by gcongr <;> linarith
      | succ i =>
          rw [Polynomial.coeff_X_sub_C_mul]
          calc
            ‖(∏ l ∈ u, (X - C (r l))).coeff i -
                r j * (∏ l ∈ u, (X - C (r l))).coeff (i + 1)‖
                ≤ ‖(∏ l ∈ u, (X - C (r l))).coeff i‖ +
                    ‖r j * (∏ l ∈ u, (X - C (r l))).coeff (i + 1)‖ := norm_sub_le _ _
            _ = ‖(∏ l ∈ u, (X - C (r l))).coeff i‖ +
                    ‖r j‖ * ‖(∏ l ∈ u, (X - C (r l))).coeff (i + 1)‖ := by rw [norm_mul]
            _ ≤ (1 + R) ^ u.card + R * (1 + R) ^ u.card := by
                  gcongr
                  · exact ih (fun l hl ↦ hr l (Finset.mem_insert_of_mem hl)) i
                  · exact hr j (Finset.mem_insert_self j u)
                  · exact ih (fun l hl ↦ hr l (Finset.mem_insert_of_mem hl)) (i + 1)
            _ = (1 + R) * (1 + R) ^ u.card := by ring

/-- The polynomial is constructed from the actual finite fibre, without a global root labeling.
Source: Gunning--Rossi, III.C, symmetric functions of local sheets;
Demailly, Complex Analytic and Differential Geometry (2012), II, proof of Theorem 8.7, p. 120. -/
theorem adim9_sheet_coefficients_aux (n d k : ℕ) (D : Set (Fin d → ℂ))
    (s : (Fin d → ℂ) → Finset (Fin n → ℂ))
    (hsheets : ∀ x ∈ D, ∃ (W : Set (Fin d → ℂ))
      (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ s y ↔ ∃ j, r j y = z)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ D, ∀ z ∈ s x, ‖ℓ z‖ ≤ R) :
    (∀ i : ℕ, AnalyticOnNhd ℂ (fun x ↦ (adim9_fibrePolynomial n (s x) ℓ).coeff i) D) ∧
    ∀ x ∈ D, (adim9_fibrePolynomial n (s x) ℓ).Monic ∧
      (adim9_fibrePolynomial n (s x) ℓ).natDegree = k ∧
      (∀ i : ℕ, ‖(adim9_fibrePolynomial n (s x) ℓ).coeff i‖ ≤ (1 + R) ^ k) ∧
      ∀ t : ℂ, (adim9_fibrePolynomial n (s x) ℓ).eval t = 0 ↔
        ∃ z ∈ s x, ℓ z = t := by
  classical
  have hfinset : ∀ x ∈ D, ∀ (W : Set (Fin d → ℂ))
      (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ)),
      (∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ s y ↔ ∃ j, r j y = z) →
      ∀ y ∈ W, s y = Finset.univ.image (fun j ↦ r j y) := by
    intro x hx W r hs y hy
    ext z
    rw [hs y hy |>.2 z]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro i x hx
    obtain ⟨W, r, hWopen, hxW, hWD, hr, hs⟩ := hsheets x hx
    have ha : AnalyticOnNhd ℂ
        (fun y ↦ (∏ j : Fin k, (X - C (ℓ (r j y)))).coeff i) W :=
      adim9_analytic_coeff_root_product Finset.univ
        (fun j _ ↦ ℓ.comp_analyticOnNhd (hr j)) i
    apply (ha x hxW).congr
    filter_upwards [hWopen.mem_nhds hxW] with y hy
    rw [adim9_fibrePolynomial, hfinset x hx W r hs y hy,
      Finset.prod_image (hs y hy).1.injOn]
  · intro x hx
    obtain ⟨W, r, hWopen, hxW, hWD, hr, hs⟩ := hsheets x hx
    have hsx := hs x hxW
    have hs_eq := hfinset x hx W r hs x hxW
    have hcard : (s x).card = k := by
      rw [hs_eq, Finset.card_image_of_injective Finset.univ hsx.1]
      simp
    have hmonic : (adim9_fibrePolynomial n (s x) ℓ).Monic := by
      unfold adim9_fibrePolynomial
      exact Polynomial.monic_prod_of_monic (s x) _ (fun z _ ↦ Polynomial.monic_X_sub_C _)
    refine ⟨hmonic, ?_, ?_, ?_⟩
    · unfold adim9_fibrePolynomial
      rw [Polynomial.natDegree_prod (s x) _ (fun z _ ↦ Polynomial.X_sub_C_ne_zero _)]
      simpa only [Polynomial.natDegree_X_sub_C, Finset.sum_const_zero,
        Finset.sum_const, smul_eq_mul, mul_one] using hcard
    · intro i
      unfold adim9_fibrePolynomial
      simpa only [hcard] using
        (adim9_norm_coeff_root_product_le (s x) (fun z ↦ ℓ z) R hR
          (fun z hz ↦ hbound x hx z hz) i)
    · intro t
      simp only [adim9_fibrePolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, sub_eq_zero]
      constructor
      · rintro ⟨z, hz, hzt⟩
        exact ⟨z, hz, hzt.symm⟩
      · rintro ⟨z, hz, hzt⟩
        exact ⟨z, hz, hzt.symm⟩

private lemma adim9_sheet_membership_stable (n d k : ℕ) (D : Set (Fin d → ℂ))
    (s : (Fin d → ℂ) → Finset (Fin n → ℂ))
    (S : Set ((Fin d → ℂ) × (Fin n → ℂ)))
    (hS : IsClopen (((↑) : {p : (Fin d → ℂ) × (Fin n → ℂ) |
      p.1 ∈ D ∧ p.2 ∈ s p.1} → (Fin d → ℂ) × (Fin n → ℂ)) ⁻¹' S))
    (W : Set (Fin d → ℂ)) (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ))
    (x : Fin d → ℂ)
    (hWo : IsOpen W) (hxW : x ∈ W) (hWD : W ⊆ D)
    (hr : ∀ j, AnalyticOnNhd ℂ (r j) W)
    (hcover : ∀ y ∈ W, ∀ z, z ∈ s y ↔ ∃ j, r j y = z) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      ∀ y ∈ V, ∀ j, ((y, r j y) ∈ S ↔ (x, r j x) ∈ S) := by
  classical
  let E := {p : (Fin d → ℂ) × (Fin n → ℂ) | p.1 ∈ D ∧ p.2 ∈ s p.1}
  let g : Fin k → W → E := fun j y ↦
    ⟨(y.1, r j y.1), hWD y.2, (hcover y.1 y.2 (r j y.1)).2 ⟨j, rfl⟩⟩
  have hg : ∀ j, Continuous (g j) := by
    intro j
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk ((hr j).continuousOn.restrict)
  let U : Set W := ⋂ j, if (x, r j x) ∈ S then (g j) ⁻¹' ((↑) ⁻¹' S)
    else (g j) ⁻¹' (((↑) ⁻¹' S)ᶜ)
  have hUo : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs
    · exact hS.isOpen.preimage (hg j)
    · exact hS.compl.isOpen.preimage (hg j)
  have hxU : (⟨x, hxW⟩ : W) ∈ U := by
    simp only [U, Set.mem_iInter]
    intro j
    dsimp [g]
    split_ifs <;> simp_all
  refine ⟨Subtype.val '' U, hWo.isOpenMap_subtype_val U hUo,
    ⟨⟨x, hxW⟩, hxU, rfl⟩, ?_, ?_⟩
  · rintro y ⟨hy, -, rfl⟩
    exact hy.2
  · rintro y ⟨hy, hyU, rfl⟩ j
    have hj := Set.mem_iInter.mp hyU j
    simp only [U, g] at hj
    split_ifs at hj with h
    · exact ⟨fun _ ↦ h, fun _ ↦ hj⟩
    · exact ⟨fun hyS ↦ (hj hyS).elim, fun hxS ↦ (h hxS).elim⟩

private lemma adim9_selected_card_eq (n d k : ℕ)
    (s : Finset (Fin n → ℂ)) (r : Fin k → (Fin n → ℂ))
    (S : Set (Fin n → ℂ)) [DecidablePred fun z ↦ z ∈ S]
    [DecidablePred fun j ↦ r j ∈ S] (hinj : Function.Injective r)
    (hcover : ∀ z, z ∈ s ↔ ∃ j, r j = z) :
    (s.filter fun z ↦ z ∈ S).card =
      (Finset.univ.filter fun j ↦ r j ∈ S).card := by
  classical
  symm
  apply Finset.card_bij (fun j _ ↦ r j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨(hcover (r j)).2 ⟨j, rfl⟩, hj⟩
  · intro i _ j _ hij
    exact hinj hij
  · intro z hz
    simp only [Finset.mem_filter] at hz
    obtain ⟨j, hj⟩ := (hcover z).1 hz.1
    refine ⟨j, ?_, hj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj]
    exact hz.2

/-- A clopen part of a finite analytic cover has a constant number of sheets on a connected base.
Source: Gunning--Rossi, III.C, unramified local parametrization and monodromy. -/
theorem adim9_clopen_sheet_selection_aux (n d k : ℕ) (D : Set (Fin d → ℂ))
    (hconn : IsConnected D) (s : (Fin d → ℂ) → Finset (Fin n → ℂ))
    (hsheets : ∀ x ∈ D, ∃ (W : Set (Fin d → ℂ))
      (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ s y ↔ ∃ j, r j y = z)
    (S : Set ((Fin d → ℂ) × (Fin n → ℂ)))
    (hS : IsClopen (((↑) : {p : (Fin d → ℂ) × (Fin n → ℂ) |
      p.1 ∈ D ∧ p.2 ∈ s p.1} → (Fin d → ℂ) × (Fin n → ℂ)) ⁻¹' S)) :
    ∃ l : ℕ, l ≤ k ∧ ∀ x ∈ D, ∃ (W : Set (Fin d → ℂ))
      (r : Fin l → (Fin d → ℂ) → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, (z ∈ s y ∧ (y, z) ∈ S) ↔ ∃ j, r j y = z := by
  classical
  let q : (Fin d → ℂ) → ℕ := fun x ↦
    (s x |>.filter fun z ↦ (x, z) ∈ S).card
  have hq_local : IsLocallyConstant (fun x : D ↦ q x.1) := by
    rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨x, hxD⟩
    obtain ⟨W, r, hWo, hxW, hWD, hr, hsheet⟩ := hsheets x hxD
    obtain ⟨V, hVo, hxV, hVW, hstable⟩ :=
      adim9_sheet_membership_stable n d k D s S hS W r x hWo hxW hWD hr
        (fun y hy ↦ (hsheet y hy).2)
    refine ⟨Subtype.val ⁻¹' V, hVo.preimage continuous_subtype_val, hxV, ?_⟩
    rintro ⟨y, hyD⟩ hyV
    have hyW := hVW hyV
    rw [show q y = (Finset.univ.filter fun j ↦ (y, r j y) ∈ S).card by
      exact adim9_selected_card_eq n d k (s y) (fun j ↦ r j y)
        {z | (y, z) ∈ S} (hsheet y hyW).1 (hsheet y hyW).2]
    rw [show q x = (Finset.univ.filter fun j ↦ (x, r j x) ∈ S).card by
      exact adim9_selected_card_eq n d k (s x) (fun j ↦ r j x)
        {z | (x, z) ∈ S} (hsheet x hxW).1 (hsheet x hxW).2]
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstable y hyV j
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  let l := q x₀
  have hql : ∀ x ∈ D, q x = l := by
    intro x hx
    letI : PreconnectedSpace D :=
      isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
    change q x = q x₀
    exact (inferInstance : PreconnectedSpace D).constant hq_local.continuous
      (x := ⟨x, hx⟩) (y := ⟨x₀, hx₀⟩)
  refine ⟨l, ?_, ?_⟩
  · obtain ⟨W, r, -, hxW, -, -, hsheet⟩ := hsheets x₀ hx₀
    change (s x₀ |>.filter fun z ↦ (x₀, z) ∈ S).card ≤ k
    rw [show (s x₀ |>.filter fun z ↦ (x₀, z) ∈ S).card =
        (Finset.univ.filter fun j ↦ (x₀, r j x₀) ∈ S).card by
      simpa only [Set.mem_setOf_eq] using
        (adim9_selected_card_eq n d k (s x₀) (fun j ↦ r j x₀)
          {z | (x₀, z) ∈ S} (hsheet x₀ hxW).1 (hsheet x₀ hxW).2)]
    simpa using Finset.card_filter_le Finset.univ (fun j ↦ (x₀, r j x₀) ∈ S)
  · intro x hxD
    obtain ⟨W, r, hWo, hxW, hWD, hr, hsheet⟩ := hsheets x hxD
    let J := Finset.univ.filter fun j ↦ (x, r j x) ∈ S
    have hJ : J.card = l := by
      rw [← hql x hxD]
      exact (adim9_selected_card_eq n d k (s x) (fun j ↦ r j x)
        {z | (x, z) ∈ S} (hsheet x hxW).1 (hsheet x hxW).2).symm
    obtain ⟨V, hVo, hxV, hVW, hstable⟩ :=
      adim9_sheet_membership_stable n d k D s S hS W r x hWo hxW hWD hr
        (fun y hy ↦ (hsheet y hy).2)
    let e : Fin l ≃ J := (finCongr hJ.symm).trans (Finset.equivFin J).symm
    let r' : Fin l → (Fin d → ℂ) → (Fin n → ℂ) := fun j ↦ r (e j).1
    refine ⟨V, r', hVo, hxV, hVW.trans hWD, ?_, ?_⟩
    · intro j
      exact (hr (e j).1).mono hVW
    · intro y hyV
      have hyW := hVW hyV
      refine ⟨fun i j hij ↦ e.injective (Subtype.ext ((hsheet y hyW).1 hij)), ?_⟩
      intro z
      constructor
      · rintro ⟨hzs, hzS⟩
        obtain ⟨j, rfl⟩ := (hsheet y hyW).2 _ |>.1 hzs
        have hjS : (x, r j x) ∈ S := (hstable y hyV j).mp hzS
        have hjJ : j ∈ J := by simp [J, hjS]
        exact ⟨e.symm ⟨j, hjJ⟩, by simp [r']⟩
      · rintro ⟨j, rfl⟩
        have hjJ := (e j).2
        change (e j).1 ∈ Finset.univ.filter (fun i ↦ (x, r i x) ∈ S) at hjJ
        have hjS : (x, r (e j).1 x) ∈ S := (Finset.mem_filter.mp hjJ).2
        exact ⟨(hsheet y hyW).2 _ |>.2 ⟨(e j).1, rfl⟩,
          (hstable y hyV (e j).1).mpr hjS⟩

/-- Using all linear observables retains the coupling between fibre coordinates.
Source: Demailly, Complex Analytic and Differential Geometry (2012),
II, proof of Theorem 8.7, p. 120; finite avoidance of proper linear hyperplanes. -/
theorem adim9_linear_observables_separate_aux (n : ℕ) (s : Finset (Fin n → ℂ)) (z : Fin n → ℂ) :
    (∀ ℓ : (Fin n → ℂ) →L[ℂ] ℂ,
      (adim9_fibrePolynomial n s ℓ).eval (ℓ z) = 0) ↔ z ∈ s := by
  classical
  constructor
  · intro h
    by_contra hz
    obtain ⟨ℓ, hℓ⟩ := adim9_exists_linear_observable_avoiding n s z hz
    have hzero := h ℓ
    simp only [adim9_fibrePolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff] at hzero
    obtain ⟨w, hw, heq⟩ := hzero
    exact hℓ w hw (sub_eq_zero.mp heq)
  · intro hz ℓ
    rw [adim9_fibrePolynomial, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero hz (sub_self _)

private theorem adim9_evaluation_kernel_isNowhereDense (n : ℕ) (z : Fin n → ℂ)
    (hz : z ≠ 0) :
    IsNowhereDense {ℓ : (Fin n → ℂ) →L[ℂ] ℂ | ℓ z = 0} := by
  let e : ((Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ z
  have hset : {ℓ : (Fin n → ℂ) →L[ℂ] ℂ | ℓ z = 0} = (e.ker : Set _) := by
    ext ℓ
    simp [e]
  rw [hset, e.isClosed_ker.isNowhereDense_iff]
  by_contra hne
  have htop : e.ker = ⊤ :=
    e.ker.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext i
    exact h i
  have hp : ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i ∈ e.ker := by
    rw [htop]
    trivial
  exact hi (by simpa [e] using hp)

/-- Source: Chirka, Complex Analytic Sets, §§3--4, generic linear projections;
Baire category applied to the dual of a finite-dimensional complex vector space. -/
theorem adim9_countable_linear_avoidance_aux (n : ℕ) (S : Set (Fin n → ℂ))
    (hcount : S.Countable) (hzero : (0 : Fin n → ℂ) ∉ S) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ, ∀ z ∈ S, ℓ z ≠ 0 := by
  have hclosed : ∀ z ∈ S,
      IsClosed {ℓ : (Fin n → ℂ) →L[ℂ] ℂ | ℓ z = 0} := by
    intro z _
    let e : ((Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ z
    have hset : {ℓ : (Fin n → ℂ) →L[ℂ] ℂ | ℓ z = 0} = (e.ker : Set _) := by
      ext ℓ
      simp [e]
    rw [hset]
    exact e.isClosed_ker
  have hinterior :
      interior (⋃ z ∈ S, {ℓ : (Fin n → ℂ) →L[ℂ] ℂ | ℓ z = 0}) = ∅ :=
    interior_biUnion_of_isClosed hclosed hcount fun z hz ↦
      adim9_evaluation_kernel_isNowhereDense n z fun hz0 ↦ hzero (hz0 ▸ hz)
  have hne : (⋃ z ∈ S, {ℓ : (Fin n → ℂ) →L[ℂ] ℂ | ℓ z = 0}) ≠ univ := by
    intro hall
    rw [hall, interior_univ] at hinterior
    exact Set.univ_nonempty.ne_empty hinterior
  obtain ⟨ℓ, hℓ⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨ℓ, fun z hz heq ↦ hℓ ?_⟩
  exact Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem hz heq)

private theorem adim9_isClosed_insert_zero_of_punctured_isClosed (n : ℕ)
    (C : Set (Fin n → ℂ)) (hzero : (0 : Fin n → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ C}) :
    IsClosed (insert 0 C) := by
  rw [isClosed_iff_clusterPt]
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hmem : (⟨x, hx0⟩ : {z : Fin n → ℂ // z ≠ 0}) ∈
        closure {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ C} := by
      rw [closure_subtype]
      have hx' : x ∈ closure (insert 0 C) := by
        rwa [mem_closure_iff_clusterPt]
      have hxC : x ∈ closure C := by
        rw [insert_eq, closure_union, isClosed_singleton.closure_eq] at hx'
        rcases hx' with hx' | hx'
        · exact False.elim (hx0 (by simpa using hx'))
        · exact hx'
      have himage : ((↑) : {z : Fin n → ℂ // z ≠ 0} → (Fin n → ℂ)) ''
          {z | z.val ∈ C} = C := by
        ext y
        change (∃ z : {z : Fin n → ℂ // z ≠ 0}, z.val ∈ C ∧ z.val = y) ↔ y ∈ C
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hy
          exact ⟨⟨y, fun hy0 ↦ hzero (hy0 ▸ hy)⟩, hy, rfl⟩
      rw [himage]
      exact hxC
    exact mem_insert_iff.mpr (Or.inr (hclosed.closure_subset hmem))

private theorem adim9_isCompact_unit_link (n : ℕ) (C : Set (Fin n → ℂ))
    (hzero : (0 : Fin n → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ C}) :
    IsCompact {z | z ∈ C ∧ ‖z‖ = 1} := by
  have hcompleted := adim9_isClosed_insert_zero_of_punctured_isClosed n C hzero hclosed
  have hcompact : IsCompact
      (Metric.sphere (0 : Fin n → ℂ) 1 ∩ insert 0 C) :=
    (isCompact_sphere (0 : Fin n → ℂ) 1).inter_right hcompleted
  convert hcompact using 1
  ext z
  simp only [Metric.mem_sphere, dist_zero_right, mem_inter_iff, mem_insert_iff, mem_singleton_iff,
    mem_setOf_eq]
  constructor
  · rintro ⟨hzC, hzNorm⟩
    exact ⟨hzNorm, Or.inr hzC⟩
  · rintro ⟨hzNorm, rfl | hzC⟩
    · norm_num at hzNorm
    · exact ⟨hzC, hzNorm⟩

private theorem adim9_cone_norm_lower_bound (n d : ℕ) (C : Set (Fin n → ℂ))
    (hzero : (0 : Fin n → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ insert 0 C, c * ‖z‖ ≤ ‖L z‖ := by
  have hnormalize : ∀ z ∈ C,
      ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ {z | z ∈ C ∧ ‖z‖ = 1} := by
    intro z hz
    have hz0 : z ≠ 0 := fun h ↦ hzero (h ▸ hz)
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    refine ⟨hscale _ (by exact_mod_cast inv_ne_zero hn) z hz, ?_⟩
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ hn]
  obtain ⟨z, hz⟩ := hne
  obtain ⟨u, hu, hmin⟩ :=
    (adim9_isCompact_unit_link n C hzero hclosed).exists_isMinOn
      ⟨_, hnormalize z hz⟩ (L.continuous.norm.continuousOn)
  have hLu : L u ≠ 0 := by
    intro h
    have hu0 : u ∈ ({0} : Set (Fin n → ℂ)) := by
      rw [← hcentral]
      exact ⟨h, mem_insert_of_mem _ hu.1⟩
    have : u = 0 := hu0
    simpa [this] using hu.2
  refine ⟨‖L u‖, norm_pos_iff.mpr hLu, ?_⟩
  intro z hz
  rcases hz with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (fun h ↦ hzero (h ▸ hz))
  have hm : ‖L u‖ ≤ ‖L (((‖z‖⁻¹ : ℝ) : ℂ) • z)‖ := hmin (hnormalize z hz)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn)] at hm
  calc
    ‖L u‖ * ‖z‖ ≤ (‖z‖⁻¹ * ‖L z‖) * ‖z‖ := mul_le_mul_of_nonneg_right hm hn.le
    _ = ‖L z‖ := by field_simp

private theorem adim9_cone_proper_of_central (n d : ℕ) (C : Set (Fin n → ℂ))
    (hzero : (0 : Fin n → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0}) :
    IsProperMap (fun z : {z : Fin n → ℂ // z ∈ insert 0 C} ↦ L z.val) := by
  obtain ⟨c, hc, hbound⟩ := adim9_cone_norm_lower_bound n d C hzero hne hclosed hscale L hcentral
  refine isProperMap_iff_isCompact_preimage.mpr ⟨L.continuous.comp continuous_subtype_val, ?_⟩
  intro K hK
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val ''
      ((fun z : {z : Fin n → ℂ // z ∈ insert 0 C} ↦ L z.val) ⁻¹' K) =
      insert 0 C ∩ L ⁻¹' K := by
    ext z
    simp only [mem_image, mem_preimage, mem_inter_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
    · rintro ⟨hz, hLz⟩
      exact ⟨⟨z, hz⟩, hLz, rfl⟩
  rw [heq]
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨
    (adim9_isClosed_insert_zero_of_punctured_isClosed n C hzero hclosed).inter
      (hK.isClosed.preimage L.continuous), ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine isBounded_iff_forall_norm_le.mpr ⟨R / c, ?_⟩
  intro z hz
  exact (le_div_iff₀ hc).mpr (by
    simpa only [mul_comm] using (hbound z hz.1).trans (hR (L z) hz.2))

private theorem adim9_cone_finite_fibres_of_proper (n d : ℕ) (C : Set (Fin n → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (hproper : IsProperMap (fun z : {z : Fin n → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0}) :
    ∀ w, {z : Fin n → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite := by
  intro w
  by_cases hw : w = 0
  · subst w
    have heq : {z : Fin n → ℂ | z ∈ insert 0 C ∧ L z = 0} = {0} := by
      rw [← hcentral]
      ext z
      exact and_comm
    rw [heq]
    exact finite_singleton 0
  have hK : IsCompact {z : Fin n → ℂ | z ∈ insert 0 C ∧ L z = w} := by
    have h := (hproper.isCompact_preimage (isCompact_singleton (x := w))).image
      continuous_subtype_val
    convert h using 1
    ext z
    simp only [mem_image, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hz, hLz⟩
      exact ⟨⟨z, hz⟩, hLz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
  apply adim9_compact_analytic_finite_aux n _ hK
  intro x hx
  have hxC : x ∈ C := by
    rcases hx.1 with rfl | hxC
    · exact False.elim (hw (by simpa using hx.2.symm))
    · exact hxC
  obtain ⟨U, hU, hxU, hU0, m, f, hf, hCf⟩ := hloc x hxC
  refine ⟨U, hU, hxU, m + d, Fin.append f (fun j z ↦ L z j - w j), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa only [Fin.append_left] using hf i
    · rw [Fin.append_right]
      intro y hy
      exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).comp L).analyticAt y).sub
        analyticAt_const
  · intro z hz
    simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, sub_eq_zero]
    change (z ∈ insert 0 C ∧ L z = w) ↔ (∀ j, f j z = 0) ∧ ∀ j, L z j = w j
    rw [← hCf z hz, ← funext_iff]
    constructor
    · rintro ⟨rfl | hzC, hLz⟩
      · exact False.elim ((hU0 hz) rfl)
      · exact ⟨hzC, hLz⟩
    · rintro ⟨hzC, hLz⟩
      exact ⟨mem_insert_of_mem _ hzC, hLz⟩

private theorem adim9_extend_disjoint_center (n : ℕ) (C : Set (Fin n → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (K : Submodule ℂ (Fin n → ℂ)) (hK : ∀ z ∈ C, z ∉ K)
    (v : Fin n → ℂ)
    (hv : v ∉ {z | ∃ c ∈ insert 0 C, ∃ k ∈ K, z = c + k}) :
    (∀ z ∈ C, z ∉ K ⊔ Submodule.span ℂ {v}) ∧
      Module.finrank ℂ ↥(K ⊔ Submodule.span ℂ {v}) = Module.finrank ℂ K + 1 := by
  have hvK : v ∉ K := by
    intro h
    exact hv ⟨0, mem_insert _ _, v, h, (zero_add v).symm⟩
  refine ⟨?_, Submodule.finrank_sup_span_singleton hvK⟩
  intro z hz hmem
  obtain ⟨k, hk, y, hy, heq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
  by_cases ht : t = 0
  · subst t
    simp only [zero_smul, add_zero] at heq
    exact hK z hz (heq ▸ hk)
  · apply hv
    refine ⟨t⁻¹ • z, mem_insert_of_mem _ (hscale _ (inv_ne_zero ht) z hz),
      -(t⁻¹ • k), K.neg_mem (K.smul_mem _ hk), ?_⟩
    rw [← heq, smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul]
    abel

private theorem adim9_cone_dimension_maximum (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    ∃ r : ℕ, r ≤ n ∧
      (∀ x ∈ C,
        ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      (∃ x ∈ C, ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((r + 1 : ℕ) : WithBot ℕ∞)) := by
  classical
  have hdim : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ n + 1 ∧
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) := by
    intro x hx P hP
    obtain ⟨U, hU, hxU, _, m, f, hf, hCf⟩ := hloc x hx
    obtain ⟨F, hF, _, hcomp⟩ := adim7_component_comparison n C x hx U hU hxU m f hf hCf
      (adim3_cone_lower_bound n C hzero hclosed hscale hloc x hx)
    have hPF : P ∈ F := by rw [← hF] at hP; exact hP
    obtain ⟨_, d, π, θ, hd, hdn, _, _, _, heq⟩ := hcomp P hPF
    exact ⟨d, hd, hdn, heq⟩
  let D : Finset ℕ := (Finset.range (n + 2)).filter fun d ↦ ∃ x ∈ C,
    ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞)
  have hD : D.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have hI : adim2_ideal (n + 1) (adim2_germ (n + 1) C x) ≠ ⊤ := by
      intro heq
      have hone : (1 : AnalyticGerm (n + 1)) ∈
          adim2_ideal (n + 1) (adim2_germ (n + 1) C x) := by rw [heq]; trivial
      change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), x + z ∈ C → (1 : ℂ) = 0 at hone
      exact one_ne_zero (hone.self_of_nhds (by simpa using hx))
    obtain ⟨P, hP⟩ := Set.nonempty_iff_ne_empty.mpr
      (mt (Ideal.minimalPrimes_eq_empty_iff _).mp hI)
    obtain ⟨d, _, hd, heq⟩ := hdim x hx P hP
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), x, hx, P, hP, heq⟩⟩
  obtain ⟨d, hdD, hmax⟩ := Finset.exists_max_image D id hD
  obtain ⟨hdn, x, hx, P, hP, heq⟩ := Finset.mem_filter.mp hdD
  obtain ⟨e, he, _, heq'⟩ := hdim x hx P hP
  have hed : e = d := by exact_mod_cast heq'.symm.trans heq
  have hdpos : 1 ≤ d := hed ▸ he
  refine ⟨d - 1, ?_, ?_, ?_⟩
  · have := Finset.mem_range.mp hdn
    omega
  · intro y hy Q hQ
    obtain ⟨e, _, hen, heq'⟩ := hdim y hy Q hQ
    have heD : e ∈ D := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), y, hy, Q, hQ, heq'⟩
    have hed : e ≤ d := hmax e heD
    rw [heq', Nat.sub_add_cancel hdpos]
    exact_mod_cast hed
  · rw [Nat.sub_add_cancel hdpos]
    exact ⟨x, hx, P, hP, heq⟩

private theorem adim9_projection_of_disjoint_center (n d : ℕ)
    (C : Set (Fin n → ℂ)) (K : Submodule ℂ (Fin n → ℂ))
    (hdim : Module.finrank ℂ K + d = n) (hK : ∀ z ∈ C, z ∉ K) :
    ∃ L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ),
      Function.Surjective L ∧ (L ⁻¹' {0}) ∩ insert 0 C = {0} := by
  have hquot : Module.finrank ℂ ((Fin n → ℂ) ⧸ K) = Module.finrank ℂ (Fin d → ℂ) := by
    have h := K.finrank_quotient_add_finrank
    simp only [Module.finrank_pi, Fintype.card_fin] at h ⊢
    omega
  let e := LinearEquiv.ofFinrankEq ((Fin n → ℂ) ⧸ K) (Fin d → ℂ) hquot
  let L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (e.toLinearMap.comp K.mkQ).toContinuousLinearMap
  have hL : ∀ z, L z = 0 ↔ z ∈ K := by
    intro z
    change e (K.mkQ z) = 0 ↔ z ∈ K
    rw [e.map_eq_zero_iff]
    change z ∈ LinearMap.ker K.mkQ ↔ z ∈ K
    rw [K.ker_mkQ]
  refine ⟨L, ?_, ?_⟩
  · exact e.surjective.comp (LinearMap.range_eq_top.mp K.range_mkQ)
  · ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hL, mem_insert_iff]
    constructor
    · rintro ⟨hzK, rfl | hzC⟩
      · rfl
      · exact False.elim (hK z hzC hzK)
    · rintro rfl
      exact ⟨K.zero_mem, Or.inl rfl⟩

private theorem adim9_dense_compl_chart_sums (n d k : ℕ) (hd : d + k < n)
    (U : ℕ → Set (Fin d → ℂ))
    (f : ℕ → (Fin d → ℂ) → (Fin n → ℂ))
    (hf : ∀ i, DifferentiableOn ℝ (f i) (U i))
    (M : (Fin k → ℂ) →L[ℂ] (Fin n → ℂ)) :
    Dense {z : Fin n → ℂ | ∃ i, ∃ x ∈ U i, ∃ y, z = f i x + M y}ᶜ := by
  let g : ℕ → ((Fin d → ℂ) × (Fin k → ℂ)) → (Fin n → ℂ) :=
    fun i p ↦ f i p.1 + M p.2
  have hg (i : ℕ) : DifferentiableOn ℝ (g i) (U i ×ˢ univ) := by
    exact ((hf i).comp differentiable_fst.differentiableOn (fun p hp ↦ hp.1)).add
      ((M.restrictScalars ℝ).differentiable.comp differentiable_snd).differentiableOn
  have hdim : ∀ i, dimH (g i '' (U i ×ˢ univ)) ≤ (2 * (d + k) : ℕ) := by
    intro i
    calc
      dimH (g i '' (U i ×ˢ univ)) ≤ dimH (U i ×ˢ (univ : Set (Fin k → ℂ))) :=
        (hg i).dimH_image_le
      _ ≤ dimH (univ : Set ((Fin d → ℂ) × (Fin k → ℂ))) := dimH_mono (subset_univ _)
      _ = (2 * (d + k) : ℕ) := by
        rw [Real.dimH_univ_eq_finrank]
        congr 1
        simp [Module.finrank_prod, finrank_real_of_complex, Module.finrank_pi]
        <;> omega
  have heq : {z : Fin n → ℂ | ∃ i, ∃ x ∈ U i, ∃ y, z = f i x + M y} =
      ⋃ i, g i '' (U i ×ˢ univ) := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_image, mem_prod, mem_univ, and_true]
    constructor
    · rintro ⟨i, x, hx, y, rfl⟩
      exact ⟨i, (x, y), hx, rfl⟩
    · rintro ⟨i, p, hp, rfl⟩
      exact ⟨i, p.1, hp, p.2, rfl⟩
  rw [heq]
  apply dense_compl_of_dimH_lt_finrank
  rw [dimH_iUnion]
  apply lt_of_le_of_lt (iSup_le hdim)
  have hn : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    simp [finrank_real_of_complex, Module.finrank_pi]
  rw [hn]
  exact_mod_cast (by omega : 2 * (d + k) < 2 * n)

private theorem adim9_center_of_countable_charts (n d : ℕ) (hd : d ≤ n)
    (C : Set (Fin n → ℂ)) (hzero : (0 : Fin n → ℂ) ∉ C)
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (U : ℕ → Set (Fin d → ℂ))
    (f : ℕ → (Fin d → ℂ) → (Fin n → ℂ))
    (hf : ∀ i, DifferentiableOn ℝ (f i) (U i))
    (hcover : insert 0 C ⊆ ⋃ i, f i '' U i) :
    ∃ K : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ K + d = n ∧ ∀ z ∈ C, z ∉ K := by
  have hind : ∀ j, j ≤ n - d → ∃ K : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ K = j ∧ ∀ z ∈ C, z ∉ K := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⊥, by simp, ?_⟩
      intro z hz hzK
      have hz0 : z = 0 := by simpa using hzK
      exact hzero (hz0 ▸ hz)
    | succ j ih =>
      intro hj
      obtain ⟨K, hKdim, hK⟩ := ih (by omega)
      have hedim : Module.finrank ℂ (Fin j → ℂ) = Module.finrank ℂ K := by
        simpa only [Module.finrank_pi, Fintype.card_fin] using hKdim.symm
      let e := LinearEquiv.ofFinrankEq (Fin j → ℂ) K hedim
      let M : (Fin j → ℂ) →L[ℂ] (Fin n → ℂ) :=
        (K.subtype.comp e.toLinearMap).toContinuousLinearMap
      obtain ⟨v, hv⟩ := (adim9_dense_compl_chart_sums n d j (by omega) U f hf M).nonempty
      have hvsum : v ∉ {z | ∃ c ∈ insert 0 C, ∃ k ∈ K, z = c + k} := by
        rintro ⟨c, hc, k, hk, hvck⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hc)
        obtain ⟨x, hx, rfl⟩ := hi
        obtain ⟨y, hy⟩ := e.surjective ⟨k, hk⟩
        apply hv
        refine ⟨i, x, hx, y, ?_⟩
        have hMy : M y = k := congrArg Subtype.val hy
        simpa only [hMy] using hvck
      obtain ⟨havoid, hdim⟩ := adim9_extend_disjoint_center n C hscale K hK v hvsum
      exact ⟨K ⊔ Submodule.span ℂ {v}, by omega, havoid⟩
  obtain ⟨K, hKdim, hK⟩ := hind (n - d) le_rfl
  exact ⟨K, by omega, hK⟩

private theorem adim9_dimH_le_of_local {X : Type*} [EMetricSpace X] [SecondCountableTopology X]
    (S : Set X) (a : ℝ≥0∞) (h : ∀ x ∈ S, ∃ U ∈ 𝓝 x, dimH (S ∩ U) ≤ a) :
    dimH S ≤ a := by
  choose! U hU hdim using h
  obtain ⟨t, hts, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x ↦ S ∩ U x) (s := S) (fun x hx ↦ inter_mem_nhdsWithin S (hU x hx))
  calc
    dimH S ≤ dimH (⋃ x ∈ t, S ∩ U x) := dimH_mono hcover
    _ = ⨆ x ∈ t, dimH (S ∩ U x) := dimH_bUnion htc _
    _ ≤ a := iSup₂_le fun x hx ↦ hdim x (hts hx)

private theorem adim9_dimH_le_of_approximatesLinearOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {f' : E ≃L[ℂ] F} {s : Set E} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (f' : E →L[ℂ] F) s c)
    (hc : Subsingleton E ∨ c < ‖(f'.symm : F →L[ℂ] E)‖₊⁻¹) (t : Set E) (hts : t ⊆ s) :
    dimH t ≤ dimH (f '' t) := by
  have hanti := hf.antilipschitzWith hc
  have h := hanti.le_dimH_image {p : s | p.val ∈ t}
  have hval : Subtype.val '' {p : s | p.val ∈ t} = t := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨⟨x, hts hx⟩, hx, rfl⟩
  have himg : s.domRestrict f '' {p : s | p.val ∈ t} = f '' t := by
    conv_rhs => rw [← hval, image_image]
    rfl
  calc
    dimH t = dimH {p : s | p.val ∈ t} := by
      rw [← (isometry_subtype_coe (s := s)).dimH_image, hval]
    _ ≤ dimH (s.domRestrict f '' {p : s | p.val ∈ t}) := h
    _ = dimH (f '' t) := by rw [himg]

private theorem adim9_finrank_real_pi (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  simp [finrank_real_of_complex]

private theorem adim9_dimH_regular_zero_set (d : ℕ) (F : (Fin d → ℂ) × ℂ → ℂ)
    (H : Set ((Fin d → ℂ) × ℂ))
    (hH : ∀ p ∈ H, F p = 0 ∧ HasStrictFDerivAt F (fderiv ℂ F p) p ∧
      deriv (fun t ↦ F (p.1, t)) p.2 ≠ 0) :
    dimH H ≤ ((2 * d : ℕ) : ℝ≥0∞) := by
  apply adim9_dimH_le_of_local
  intro p hp
  obtain ⟨_, hF, hD⟩ := hH p hp
  set A := fderiv ℂ F p with hA
  set b := A (0, 1) with hbdef
  have hb : b ≠ 0 := by
    have h1 : HasDerivAt (fun t : ℂ ↦ ((p.1, t) : (Fin d → ℂ) × ℂ)) ((0 : Fin d → ℂ), (1 : ℂ)) p.2 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have h2 := hF.hasFDerivAt.comp_hasDerivAt p.2 h1
    have h3 : deriv (fun t ↦ F (p.1, t)) p.2 = b := h2.deriv
    rwa [h3] at hD
  have hsplit : ∀ u : Fin d → ℂ, ∀ s : ℂ, A (u, s) = A (u, 0) + s * b := by
    intro u s
    have : ((u, s) : (Fin d → ℂ) × ℂ) = (u, 0) + s • ((0 : Fin d → ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  let f₁ : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).prod A
  let f₂ : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).prod (b⁻¹ • (ContinuousLinearMap.snd ℂ _ _ -
      (A.comp (ContinuousLinearMap.inl ℂ _ _)).comp (ContinuousLinearMap.fst ℂ _ _)))
  have h21 : ∀ q, f₂ (f₁ q) = q := by
    intro q
    obtain ⟨u, s⟩ := q
    simp only [f₁, f₂, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [hsplit u s]
    ext
    · rfl
    · simp only
      field_simp
      ring
  have h12 : ∀ q, f₁ (f₂ q) = q := by
    intro q
    obtain ⟨u, y⟩ := q
    simp only [f₁, f₂, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [hsplit]
    ext
    · rfl
    · simp only
      field_simp
      ring
  let Φ' := ContinuousLinearEquiv.equivOfInverse f₁ f₂ h21 h12
  let Φ : (Fin d → ℂ) × ℂ → (Fin d → ℂ) × ℂ := fun q ↦ (q.1, F q)
  have hΦ : HasStrictFDerivAt Φ (Φ' : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ)) p :=
    hasStrictFDerivAt_fst.prodMk hF
  set N := ‖(Φ'.symm : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ))‖₊ with hN
  have hN0 : N ≠ 0 := by
    intro h0
    have h := congrArg (fun T : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ) ↦
      T ((0 : Fin d → ℂ), (1 : ℂ))) (nnnorm_eq_zero.mp h0)
    simp only [ContinuousLinearEquiv.coe_coe] at h
    have := congrArg Prod.snd (Φ'.symm.injective (h.trans (map_zero Φ'.symm).symm))
    simp at this
  have hcpos : 0 < N⁻¹ / 2 := by
    apply div_pos (inv_pos.mpr (pos_iff_ne_zero.mpr hN0)) two_pos
  obtain ⟨s, hs, happrox⟩ := hΦ.approximates_deriv_on_nhds (Or.inr hcpos)
  refine ⟨s, hs, ?_⟩
  calc
    dimH (H ∩ s) ≤ dimH (Φ '' (H ∩ s)) :=
      adim9_dimH_le_of_approximatesLinearOn happrox
        (Or.inr (NNReal.half_lt_self (inv_pos.mpr (pos_iff_ne_zero.mpr hN0)).ne')) _
        inter_subset_right
    _ ≤ dimH (range (ContinuousLinearMap.inl ℝ (Fin d → ℂ) ℂ)) := by
      apply dimH_mono
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q.1, by simp [Φ, (hH q hq.1).1]⟩
    _ ≤ Module.finrank ℝ (Fin d → ℂ) :=
      (ContinuousLinearMap.inl ℝ (Fin d → ℂ) ℂ).differentiable.dimH_range_le
    _ = ((2 * d : ℕ) : ℝ≥0∞) := by rw [adim9_finrank_real_pi]

private theorem adim9_kernel_projection (n d : ℕ) (K : Submodule ℂ (Fin n → ℂ))
    (hdim : Module.finrank ℂ K + d = n) :
    ∃ L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ),
      Function.Surjective L ∧ ∀ z, L z = 0 ↔ z ∈ K := by
  have hquot : Module.finrank ℂ ((Fin n → ℂ) ⧸ K) = Module.finrank ℂ (Fin d → ℂ) := by
    have h := K.finrank_quotient_add_finrank
    simp only [Module.finrank_pi, Fintype.card_fin] at h ⊢
    omega
  let e := LinearEquiv.ofFinrankEq ((Fin n → ℂ) ⧸ K) (Fin d → ℂ) hquot
  let L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (e.toLinearMap.comp K.mkQ).toContinuousLinearMap
  refine ⟨L, e.surjective.comp (LinearMap.range_eq_top.mp K.range_mkQ), ?_⟩
  intro z
  change e (K.mkQ z) = 0 ↔ z ∈ K
  rw [e.map_eq_zero_iff]
  change z ∈ LinearMap.ker K.mkQ ↔ z ∈ K
  rw [K.ker_mkQ]

private theorem adim9_center_of_dimH (n d : ℕ) (hd : d ≤ n)
    (C : Set (Fin n → ℂ)) (hzero : (0 : Fin n → ℂ) ∉ C)
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hdim : dimH (insert 0 C) ≤ ((2 * d : ℕ) : ℝ≥0∞)) :
    ∃ K : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ K + d = n ∧ ∀ z ∈ C, z ∉ K := by
  have hind : ∀ j, j ≤ n - d → ∃ K : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ K = j ∧ ∀ z ∈ C, z ∉ K := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⊥, by simp, ?_⟩
      intro z hz hzK
      have hz0 : z = 0 := by simpa using hzK
      exact hzero (hz0 ▸ hz)
    | succ j ih =>
      intro hj
      obtain ⟨K, hKdim, hK⟩ := ih (by omega)
      obtain ⟨L, hLsurj, hLker⟩ := adim9_kernel_projection n (n - j) K (by omega)
      have hlt : dimH (L '' insert 0 C) < Module.finrank ℝ (Fin (n - j) → ℂ) := by
        rw [adim9_finrank_real_pi]
        calc
          dimH (L '' insert 0 C) ≤ dimH (insert 0 C) := L.lipschitzWith.dimH_image_le _
          _ ≤ ((2 * d : ℕ) : ℝ≥0∞) := hdim
          _ < ((2 * (n - j) : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 2 * d < 2 * (n - j))
      obtain ⟨y, hy⟩ := (dense_compl_of_dimH_lt_finrank hlt).nonempty
      obtain ⟨v, rfl⟩ := hLsurj y
      have hvsum : v ∉ {z | ∃ c ∈ insert 0 C, ∃ k ∈ K, z = c + k} := by
        rintro ⟨c, hc, k, hk, rfl⟩
        apply hy
        refine ⟨c, hc, ?_⟩
        rw [map_add, (hLker k).mpr hk, add_zero]
      obtain ⟨havoid, hdim⟩ := adim9_extend_disjoint_center n C hscale K hK v hvsum
      exact ⟨K ⊔ Submodule.span ℂ {v}, by omega, havoid⟩
  obtain ⟨K, hKdim, hK⟩ := hind (n - d) le_rfl
  exact ⟨K, by omega, hK⟩

private theorem adim9_krullDim_drop {R : Type*} [CommRing R] (P Q : Ideal R) [P.IsPrime]
    (hPQ : P ≤ Q) (b : R) (hbP : b ∉ P) (hbQ : b ∈ Q) :
    ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  have hb : Ideal.Quotient.mk P b ∈ nonZeroDivisors (R ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  let f : (R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P b} →+* R ⧸ Q :=
    Ideal.Quotient.lift _ (Ideal.Quotient.factor hPQ) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hbQ, mul_zero])
  have hf : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hPQ)
  calc
    ringKrullDim (R ⧸ Q) + 1 ≤
        ringKrullDim ((R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P b}) + 1 := by
      gcongr
      exact ringKrullDim_le_of_surjective f hf
    _ ≤ ringKrullDim (R ⧸ P) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hb

private theorem adim9_le_pred_of_succ_le (x : WithBot ℕ∞) (d : ℕ) (h : x + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    x ≤ (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe] at h'
      simp at h'
    | coe k =>
      have : k + 1 ≤ d + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ d)

private theorem adim9_vanish_of_mem_span (n : ℕ) (G : Finset (AnalyticGerm n))
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ g, Germ.ofFun (rep g) = g.val)
    (b : AnalyticGerm n) (hb : b ∈ Ideal.span (G : Set (AnalyticGerm n)))
    (B : (Fin n → ℂ) → ℂ) (hB : Germ.ofFun B = b.val) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ g ∈ G, rep g z = 0) → B z = 0 := by
  classical
  obtain ⟨f, -, hsum⟩ := Submodule.mem_span_finset.mp hb
  have hval : b.val = Germ.ofFun (fun z ↦ ∑ g ∈ G, rep (f g) z * rep g z) := by
    rw [← hsum]
    change (analyticGermSubring n).subtype (∑ g ∈ G, f g • g) = _
    rw [map_sum]
    simp only [smul_eq_mul, map_mul, Subring.subtype_apply, ← hrep]
    change (∑ g ∈ G, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (rep (f g)) *
      Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (rep g)) = Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) _
    simp only [← map_mul, ← map_sum]
    congr 1
    funext z
    simp [Finset.sum_apply]
  have heq : B =ᶠ[𝓝 (0 : Fin n → ℂ)] fun z ↦ ∑ g ∈ G, rep (f g) z * rep g z :=
    Germ.coe_eq.mp (hB.trans hval)
  filter_upwards [heq] with z hz hzero
  rw [hz]
  exact Finset.sum_eq_zero fun g hg ↦ by rw [hzero g hg, mul_zero]

private theorem adim9_poly_rep (d : ℕ) (T : Polynomial (AnalyticGerm d)) :
    ∃ t : Polynomial ((Fin d → ℂ) → ℂ), ∀ i, AnalyticAt ℂ (t.coeff i) 0 ∧
      Germ.ofFun (t.coeff i) = (T.coeff i).val := by
  classical
  choose a ha hrep using fun i ↦ (T.coeff i).property
  refine ⟨T.sum fun i _ ↦ Polynomial.monomial i (a i), fun i ↦ ?_⟩
  by_cases hi : i ∈ T.support
  · simpa [Polynomial.sum, Polynomial.coeff_monomial, hi] using And.intro (ha i) (hrep i)
  · have hTi : T.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
    simpa [Polynomial.sum, Polynomial.coeff_monomial, hi, hTi] using
      (And.intro (show AnalyticAt ℂ (0 : (Fin d → ℂ) → ℂ) 0 from analyticAt_const)
        (rfl : Germ.ofFun (0 : (Fin d → ℂ) → ℂ) = (0 : AnalyticGerm d).val))

private theorem adim9_eval_germ (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (T : Polynomial (AnalyticGerm d)) (t : Polynomial ((Fin d → ℂ) → ℂ))
    (ht : ∀ i, AnalyticAt ℂ (t.coeff i) 0 ∧ Germ.ofFun (t.coeff i) = (T.coeff i).val) :
    ∃ b : AnalyticGerm n, b.val = Germ.ofFun (fun z ↦
        t.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (ℓ z)) ∧
      T.eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b := by
  classical
  set N := max T.natDegree t.natDegree + 1 with hN
  let bi : ℕ → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z ↦ t.coeff i (π z)), _,
      (ht i).1.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  refine ⟨∑ i ∈ Finset.range N, bi i * v ^ i, ?_, ?_⟩
  · change (analyticGermSubring n).subtype (∑ i ∈ Finset.range N, bi i * v ^ i) = _
    rw [map_sum]
    simp only [map_mul, map_pow, Subring.subtype_apply, hv]
    change (∑ i ∈ Finset.range N, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))
      (fun z ↦ t.coeff i (π z)) * (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ ℓ z)) ^ i) =
        Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) _
    simp only [← map_mul, ← map_pow, ← map_sum]
    congr 1
    funext z
    rw [Polynomial.eval₂_eq_sum_range' _ (by omega : t.natDegree < N)]
    simp [Finset.sum_apply]
  · rw [Polynomial.eval₂_eq_sum_range' _ (by omega : T.natDegree < N), map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_pow,
      hcomp (T.coeff i) (t.coeff i) (ht i).1 (ht i).2 (bi i) rfl]

private theorem adim9_poly_coeff_analytic_eventually (d : ℕ) (t : Polynomial ((Fin d → ℂ) → ℂ))
    (ht : ∀ i, AnalyticAt ℂ (t.coeff i) 0) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ i, AnalyticAt ℂ (t.coeff i) w := by
  classical
  have hs : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ i ∈ t.support, AnalyticAt ℂ (t.coeff i) w := by
    rw [Finset.eventually_all]
    exact fun i _ ↦ (ht i).eventually_analyticAt
  filter_upwards [hs] with w hw i
  by_cases hi : i ∈ t.support
  · exact hw i hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    exact analyticAt_const

private theorem adim9_poly_eval_analyticAt (d : ℕ) (t : Polynomial ((Fin d → ℂ) → ℂ))
    (p₀ : (Fin d → ℂ) × ℂ) (h : ∀ i, AnalyticAt ℂ (t.coeff i) p₀.1) :
    AnalyticAt ℂ (fun p : (Fin d → ℂ) × ℂ ↦
      t.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) p.1) p.2) p₀ := by
  simp only [Polynomial.eval₂_eq_sum_range, Pi.evalRingHom_apply]
  have := Finset.analyticAt_sum (f := fun i (p : (Fin d → ℂ) × ℂ) ↦ t.coeff i p.1 * p.2 ^ i)
    (c := p₀) (Finset.range (t.natDegree + 1))
    (fun i _ ↦ ((h i).comp analyticAt_fst).mul (analyticAt_snd.pow i))
  convert this using 1
  funext p
  simp [Finset.sum_apply]

private theorem adim9_poly_deriv (d : ℕ) (t : Polynomial ((Fin d → ℂ) → ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    deriv (fun s : ℂ ↦ t.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) s) s =
      t.derivative.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) s := by
  simp only [← Polynomial.eval_map, Polynomial.deriv, Polynomial.derivative_map]

private theorem adim9_off_discriminant_dimH (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (G : Finset (AnalyticGerm n)) (hG : Ideal.span (G : Set (AnalyticGerm n)) = P)
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ g, Germ.ofFun (rep g) = g.val) :
    ∃ (δ : AnalyticGerm d) (Δ : (Fin d → ℂ) → ℂ), δ ≠ 0 ∧ AnalyticAt ℂ Δ 0 ∧
      Germ.ofFun Δ = δ.val ∧ ∃ W ∈ 𝓝 (0 : Fin n → ℂ),
        dimH {z | z ∈ W ∧ (∀ g ∈ G, rep g z = 0) ∧ Δ (π z) ≠ 0} ≤
          ((2 * d : ℕ) : ℝ≥0∞) := by
  classical
  let ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun w ↦
    Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  obtain ⟨ℓ, v, Q, δ, R, B, Cb, hv, -, -, hδ, hbez, hmin, hcoord⟩ :=
    adim7_primitive_form n d P hP π θ hfinite hinj hcomp c hc
  obtain ⟨q, hq⟩ := adim9_poly_rep d Q
  obtain ⟨b, hb⟩ := adim9_poly_rep d B
  obtain ⟨cb, hcb⟩ := adim9_poly_rep d Cb
  choose r hr using fun i ↦ adim9_poly_rep d (R i)
  obtain ⟨Δ, hΔ, hΔrep⟩ := δ.property
  refine ⟨δ, Δ, hδ, hΔ, hΔrep, ?_⟩
  -- the primitive relation vanishes on the component
  have hQzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ g ∈ G, rep g z = 0) →
      q.eval₂ (ev (π z)) (ℓ z) = 0 := by
    obtain ⟨bq, hbq, hQe⟩ := adim9_eval_germ n d P π θ hcomp ℓ v hv Q q hq
    have hmem : bq ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, ← hQe]
      exact (hmin Q).mpr dvd_rfl
    exact adim9_vanish_of_mem_span n G rep hrep bq hmem _ hbq.symm
  -- the coordinates are reconstructed on the component
  let bΔ : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ Δ (π z)), _,
    hΔ.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hθδ : θ δ = Ideal.Quotient.mk P bΔ := hcomp δ Δ hΔ hΔrep bΔ rfl
  have hcoordzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, (∀ g ∈ G, rep g z = 0) →
      Δ (π z) * z i - (r i).eval₂ (ev (π z)) (ℓ z) = 0 := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨br, hbr, hRe⟩ := adim9_eval_germ n d P π θ hcomp ℓ v hv (R i) (r i) (hr i)
    have hmem : bΔ * c i - br ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hθδ, hcoord i, hRe,
        sub_self]
    apply adim9_vanish_of_mem_span n G rep hrep _ hmem
    rw [show (bΔ * c i - br).val = bΔ.val * (c i).val - br.val from rfl, hbr]
    rfl
  -- the Bezout identity holds near the origin
  have hbezout : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ s : ℂ,
      b.eval₂ (ev w) s * q.eval₂ (ev w) s + cb.eval₂ (ev w) s * q.derivative.eval₂ (ev w) s =
        Δ w := by
    have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (T : Polynomial (AnalyticGerm d))
        (hFT : ∀ i, AnalyticAt ℂ (F.coeff i) 0 ∧ Germ.ofFun (F.coeff i) = (T.coeff i).val) :
        F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
          T.map (analyticGermSubring d).subtype := by
      ext i
      simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
        (hFT i).2
    have heq : (b * q + cb * q.derivative).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        (Polynomial.C Δ).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        ← Polynomial.derivative_map, hmap b B hb, hmap q Q hq, hmap cb Cb hcb,
        Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
        ← Polynomial.map_add, hbez, Polynomial.map_C, Polynomial.map_C]
      congr 1
      exact hΔrep.symm
    filter_upwards [adim9_polynomial_representatives_eq d _ _ heq] with w hw s
    have := congrArg (fun a : Polynomial ℂ ↦ a.eval s) hw
    simp only [Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C] at this
    exact this
  -- an open parameter neighbourhood with analytic data
  have hnear : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      (∀ s : ℂ, b.eval₂ (ev w) s * q.eval₂ (ev w) s +
        cb.eval₂ (ev w) s * q.derivative.eval₂ (ev w) s = Δ w) ∧
      AnalyticAt ℂ Δ w ∧ (∀ i, AnalyticAt ℂ (q.coeff i) w) ∧
      ∀ j i, AnalyticAt ℂ ((r j).coeff i) w := by
    have hrall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ j i, AnalyticAt ℂ ((r j).coeff i) w := by
      rw [Filter.eventually_all]
      exact fun j ↦ adim9_poly_coeff_analytic_eventually d (r j) (fun i ↦ (hr j i).1)
    filter_upwards [hbezout, hΔ.eventually_analyticAt,
      adim9_poly_coeff_analytic_eventually d q (fun i ↦ (hq i).1), hrall] with w h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp hnear
  let H : Set ((Fin d → ℂ) × ℂ) :=
    {p | p.1 ∈ V ∧ Δ p.1 ≠ 0 ∧ q.eval₂ (ev p.1) p.2 = 0}
  have hHdim : dimH H ≤ ((2 * d : ℕ) : ℝ≥0∞) := by
    apply adim9_dimH_regular_zero_set d (fun p ↦ q.eval₂ (ev p.1) p.2) H
    rintro ⟨w, s⟩ ⟨hwV, hΔw, hqs⟩
    obtain ⟨hB, -, hqa, -⟩ := hVsub hwV
    refine ⟨hqs, (adim9_poly_eval_analyticAt d q (w, s) hqa).hasStrictFDerivAt, ?_⟩
    change deriv (fun s : ℂ ↦ q.eval₂ (ev w) s) s ≠ 0
    rw [adim9_poly_deriv]
    intro h0
    apply hΔw
    rw [← hB s, hqs, h0, mul_zero, mul_zero, add_zero]
  let Gm : (Fin d → ℂ) × ℂ → (Fin n → ℂ) := fun p i ↦ (r i).eval₂ (ev p.1) p.2 / Δ p.1
  have hGm : DifferentiableOn ℂ Gm H := by
    rintro ⟨w, s⟩ ⟨hwV, hΔw, -⟩
    obtain ⟨-, hΔa, -, hra⟩ := hVsub hwV
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_pi]
    intro i
    show DifferentiableAt ℂ (fun p : (Fin d → ℂ) × ℂ ↦ (r i).eval₂ (ev p.1) p.2 / Δ p.1) (w, s)
    exact ((adim9_poly_eval_analyticAt d (r i) (w, s) (hra i)).div
      (hΔa.comp_of_eq analyticAt_fst rfl) hΔw).differentiableAt
  have hW : π ⁻¹' V ∈ 𝓝 (0 : Fin n → ℂ) :=
    π.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hVopen.mem_nhds hV0)
  refine ⟨_, inter_mem (hQzero.and hcoordzero) hW, ?_⟩
  calc
    dimH _ ≤ dimH (Gm '' H) := by
      apply dimH_mono
      rintro z ⟨⟨⟨hzq, hzc⟩, hzV⟩, hzG, hzΔ⟩
      refine ⟨(π z, ℓ z), ⟨hzV, hzΔ, hzq hzG⟩, ?_⟩
      funext i
      have := hzc i hzG
      change (r i).eval₂ (ev (π z)) (ℓ z) / Δ (π z) = z i
      rw [div_eq_iff hzΔ]
      linear_combination -this
    _ ≤ dimH H := hGm.dimH_image_le
    _ ≤ _ := hHdim

private theorem adim9_point_germ (n : ℕ) (A : Set (Fin n → ℂ))
    (P : Ideal (AnalyticGerm n)) (hP : P ∈ (adim2_ideal n (adim2_germ n A 0)).minimalPrimes)
    (hdim : ringKrullDim (AnalyticGerm n ⧸ P) < 1) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ A → z = 0 := by
  classical
  let I := adim2_ideal n (adim2_germ n A 0)
  let : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro a b hab
    rw [analyticGerm_isUnit_iff] at hab
    simp only [map_add] at hab
    by_cases ha : analyticGermValue n a = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [ha] using hab
    · left
      rwa [analyticGerm_isUnit_iff]
  let : P.IsPrime := hP.isPrime
  have hPm : P.IsMaximal := by
    apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr
    let : Ring.KrullDimLE 0 (AnalyticGerm n ⧸ P) := Ring.krullDimLE_iff.mpr <|
      le_of_not_gt (fun hpos ↦
        not_lt_of_ge ((WithBot.one_le_iff_pos _).mpr hpos) hdim)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hPeq : P = IsLocalRing.maximalIdeal (AnalyticGerm n) :=
    IsLocalRing.eq_maximalIdeal hPm
  have hIP : I = P := by
    have hunique : ∀ Q ∈ I.minimalPrimes, Q = P := by
      intro Q hQ
      have hQP : Q ≤ P := hPeq.symm ▸ IsLocalRing.le_maximalIdeal hQ.isPrime.ne_top
      exact hQP.antisymm (hP.2 hQ.1 hQP)
    have hrad : I.radical = I := adim2_radical n _
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    apply le_antisymm (sInf_le hP)
    exact le_sInf fun Q hQ ↦ (hunique Q hQ).ge
  have hmax : (analyticGermMaximalIdeal n).IsMaximal := by
    apply RingHom.ker_isMaximal_of_surjective
    intro c
    exact ⟨⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩
  have hPval : P = analyticGermMaximalIdeal n :=
    hPeq.trans (IsLocalRing.eq_maximalIdeal hmax).symm
  have hcoord : ∀ i : Fin n, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ A → z i = 0 := by
    intro i
    let c : AnalyticGerm n := ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
    have hc : c ∈ I := by
      rw [hIP, hPval]
      exact rfl
    change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), 0 + z ∈ A → z i = 0 at hc
    simpa using hc
  filter_upwards [Filter.eventually_all.mpr hcoord] with z hz hzA
  funext i
  exact hz i hzA

private theorem adim9_zeroSet_eq (n : ℕ) (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ)
    (hrep : ∀ g, Germ.ofFun (rep g) = g.val) (P : Ideal (AnalyticGerm n)) :
    adim2_zeroSet n P = Germ.ofFun (fun z ↦ ∀ g ∈ adim2_generators n P, rep g z = 0) := by
  classical
  unfold adim2_zeroSet
  induction adim2_generators n P using Finset.induction_on with
  | empty => simp; rfl
  | insert g s hg ih =>
    rw [Finset.inf_insert, ih]
    have hz : adim2_zero n g = Germ.ofFun (fun z ↦ rep g z = 0) := by
      unfold adim2_zero
      rw [← hrep g]
      rfl
    rw [hz]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp

private theorem adim9_sup_zeroSet_eq (n : ℕ) (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ)
    (hrep : ∀ g, Germ.ofFun (rep g) = g.val) (F : Finset (Ideal (AnalyticGerm n))) :
    F.sup (adim2_zeroSet n) = Germ.ofFun (fun z ↦
      ∃ P ∈ F, ∀ g ∈ adim2_generators n P, rep g z = 0) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp; rfl
  | insert P s hP ih =>
    rw [Finset.sup_insert, ih, adim9_zeroSet_eq n rep hrep P]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp

private theorem adim9_span_generators (n : ℕ) (P : Ideal (AnalyticGerm n)) :
    Ideal.span (adim2_generators n P : Set (AnalyticGerm n)) = P :=
  ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) P).choose_spec

private theorem adim9_mem_ideal_of_vanish (n : ℕ) (A : Set (Fin n → ℂ)) (g : AnalyticGerm n)
    (G : (Fin n → ℂ) → ℂ) (hG : Germ.ofFun G = g.val) (h : ∀ z ∈ A, G z = 0) :
    g ∈ adim2_ideal n (adim2_germ n A 0) := by
  change adim2_germ n A 0 ≤ g.val.map (· = 0)
  rw [← hG]
  apply Germ.coe_le.mpr
  exact Eventually.of_forall fun z hz ↦ h z (by simpa using hz)

private theorem adim9_local_dimH (n e : ℕ) : ∀ (A : Set (Fin (n + 1) → ℂ)),
    (∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
      ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ f ∈ s, f z = 0)) →
    (∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ (e : WithBot ℕ∞)) →
    ∃ W ∈ 𝓝 (0 : Fin (n + 1) → ℂ), dimH (A ∩ W) ≤ ((2 * e : ℕ) : ℝ≥0∞) := by
  classical
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro A ⟨U, hU, hU0, s, hs, hAs⟩ hdim
  choose rep hrepa hrep using fun g : AnalyticGerm (n + 1) ↦ g.property
  -- away from the set
  by_cases hA0 : (0 : Fin (n + 1) → ℂ) ∉ A
  · obtain ⟨f, hf, hf0⟩ : ∃ f ∈ s, f 0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hA0 ((hAs 0 hU0).mpr hcon)
    have hev : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), f z ≠ 0 :=
      ((hs f hf 0 hU0).continuousAt).eventually_ne hf0
    refine ⟨_, inter_mem hev (hU.mem_nhds hU0), ?_⟩
    have hempty : A ∩ ({z | f z ≠ 0} ∩ U) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hzA hfz hzU
      exact hfz ((hAs z hzU).mp hzA f hf)
    rw [hempty, dimH_empty]
    exact bot_le
  push Not at hA0
  -- a zero-dimensional component makes the germ a point
  by_cases hpt : ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) < 1
  · obtain ⟨P, hP, hlt⟩ := hpt
    refine ⟨_, adim9_point_germ (n + 1) A P hP hlt, ?_⟩
    calc
      dimH (A ∩ {z | z ∈ A → z = 0}) ≤ dimH ({0} : Set (Fin (n + 1) → ℂ)) :=
        dimH_mono fun z hz ↦ hz.2 hz.1
      _ = 0 := dimH_singleton _
      _ ≤ _ := bot_le
  push Not at hpt
  -- component comparison
  let m := s.card
  let f : Fin m → (Fin (n + 1) → ℂ) → ℂ := fun j ↦ (s.equivFin.symm j).val
  have hf : ∀ j, AnalyticOnNhd ℂ (f j) U := fun j ↦ hs _ (s.equivFin.symm j).property
  have hAf : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0) := by
    intro z hz
    rw [hAs z hz]
    constructor
    · intro h j
      exact h _ (s.equivFin.symm j).property
    · intro h g hg
      have := h (s.equivFin ⟨g, hg⟩)
      simpa [f] using this
  obtain ⟨F, hF, hcover, hcomp⟩ :=
    adim7_component_comparison n A 0 hA0 U hU hU0 m f hf hAf hpt
  rw [adim9_sup_zeroSet_eq (n + 1) rep hrep F] at hcover
  have hcov : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z ∈ A →
      ∃ P ∈ F, ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0 := by
    have h := Germ.coe_eq.mp hcover
    filter_upwards [h] with z hz hzA
    have : (0 : Fin (n + 1) → ℂ) + z ∈ A := by simpa using hzA
    exact (show _ = _ from hz) ▸ this
  -- each component has small dimension near the origin
  have hpiece : ∀ P ∈ F, ∃ W ∈ 𝓝 (0 : Fin (n + 1) → ℂ),
      dimH ({z | ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0} ∩ W) ≤
        ((2 * e : ℕ) : ℝ≥0∞) := by
    intro P hPF
    have hPmin : P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes := by
      rw [← hF]
      exact hPF
    have hPprime : P.IsPrime := hPmin.isPrime
    obtain ⟨-, d, π, θ, hd1, -, hfin, hinj, hcompat, hdimP⟩ := hcomp P hPF
    have hde : d ≤ e := by
      have h := hdim P hPmin
      rw [hdimP] at h
      exact_mod_cast h
    set Gs := adim2_generators (n + 1) P with hGs
    obtain ⟨δ, Δ, hδ, hΔ, hΔrep, W₁, hW₁, hW₁dim⟩ :=
      adim9_off_discriminant_dimH (n + 1) d P hPprime π θ hfin hinj hcompat Gs
        (adim9_span_generators (n + 1) P) rep hrep
    -- an open neighbourhood where the equations are analytic
    have hΔπ : AnalyticAt ℂ (fun z ↦ Δ (π z)) (0 : Fin (n + 1) → ℂ) :=
      hΔ.comp_of_eq (π.analyticAt 0) (map_zero π)
    have hnear : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ),
        AnalyticAt ℂ (fun z ↦ Δ (π z)) z ∧ ∀ g ∈ Gs, AnalyticAt ℂ (rep g) z := by
      refine hΔπ.eventually_analyticAt.and ?_
      rw [Finset.eventually_all]
      exact fun g _ ↦ (hrepa g).eventually_analyticAt
    obtain ⟨U₀, hU₀sub, hU₀, hU₀0⟩ := mem_nhds_iff.mp hnear
    let D : Set (Fin (n + 1) → ℂ) :=
      {z | z ∈ U₀ ∧ (∀ g ∈ Gs, rep g z = 0) ∧ Δ (π z) = 0}
    let bΔ : AnalyticGerm (n + 1) := ⟨Germ.ofFun (fun z ↦ Δ (π z)), _, hΔπ, rfl⟩
    have hθδ : θ δ = Ideal.Quotient.mk P bΔ := hcompat δ Δ hΔ hΔrep bΔ rfl
    have hbΔP : bΔ ∉ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hθδ]
      intro h0
      exact hδ (hinj (h0.trans (map_zero θ).symm))
    have hPD : P ≤ adim2_ideal (n + 1) (adim2_germ (n + 1) D 0) := by
      rw [← adim9_span_generators (n + 1) P, Ideal.span_le]
      intro g hg
      exact adim9_mem_ideal_of_vanish (n + 1) D g (rep g) (hrep g)
        (fun z hz ↦ hz.2.1 g hg)
    have hbΔD : bΔ ∈ adim2_ideal (n + 1) (adim2_germ (n + 1) D 0) :=
      adim9_mem_ideal_of_vanish (n + 1) D bΔ _ rfl (fun z hz ↦ hz.2.2)
    have hDdim : ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) D 0)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
      intro Q hQ
      apply adim9_le_pred_of_succ_le
      rw [Nat.sub_add_cancel hd1, ← hdimP]
      exact adim9_krullDim_drop P Q (hPD.trans hQ.1.2) bΔ hbΔP (hQ.1.2 hbΔD)
    have hDloc : ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
        ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f U) ∧
          ∀ z ∈ U, (z ∈ D ↔ ∀ f ∈ s, f z = 0) := by
      refine ⟨U₀, hU₀, hU₀0, insert (fun z ↦ Δ (π z)) (Gs.image rep), ?_, ?_⟩
      · intro φ hφ z hz
        rcases Finset.mem_insert.mp hφ with rfl | hφ
        · exact (hU₀sub hz).1
        · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hφ
          exact (hU₀sub hz).2 g hg
      · intro z hz
        simp only [D, Finset.forall_mem_insert, Finset.forall_mem_image, mem_ofPred_eq]
        tauto
    obtain ⟨W₂, hW₂, hW₂dim⟩ := ih (d - 1) (by omega) D hDloc hDdim
    refine ⟨W₁ ∩ W₂ ∩ U₀, inter_mem (inter_mem hW₁ hW₂) (hU₀.mem_nhds hU₀0), ?_⟩
    calc
      dimH ({z | ∀ g ∈ Gs, rep g z = 0} ∩ (W₁ ∩ W₂ ∩ U₀)) ≤
          dimH ({z | z ∈ W₁ ∧ (∀ g ∈ Gs, rep g z = 0) ∧ Δ (π z) ≠ 0} ∪ D ∩ W₂) := by
        apply dimH_mono
        rintro z ⟨hzG, ⟨hz₁, hz₂⟩, hz₀⟩
        by_cases hzΔ : Δ (π z) = 0
        · exact Or.inr ⟨⟨hz₀, hzG, hzΔ⟩, hz₂⟩
        · exact Or.inl ⟨hz₁, hzG, hzΔ⟩
      _ = max (dimH {z | z ∈ W₁ ∧ (∀ g ∈ Gs, rep g z = 0) ∧ Δ (π z) ≠ 0})
          (dimH (D ∩ W₂)) := dimH_union _ _
      _ ≤ ((2 * e : ℕ) : ℝ≥0∞) := by
        apply max_le
        · exact hW₁dim.trans (by exact_mod_cast (by omega : 2 * d ≤ 2 * e))
        · exact hW₂dim.trans (by exact_mod_cast (by omega : 2 * (d - 1) ≤ 2 * e))
  choose! W hW hWdim using hpiece
  refine ⟨(⋂ P ∈ F, W P) ∩ {z | z ∈ A → ∃ P ∈ F, ∀ g ∈ adim2_generators (n + 1) P,
      rep g z = 0}, inter_mem ((Filter.biInter_finset_mem F).mpr hW) hcov, ?_⟩
  calc
    dimH (A ∩ ((⋂ P ∈ F, W P) ∩ {z | z ∈ A → ∃ P ∈ F,
        ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0})) ≤
        dimH (⋃ P ∈ (F : Set (Ideal (AnalyticGerm (n + 1)))),
          {z | ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0} ∩ W P) := by
      apply dimH_mono
      rintro z ⟨hzA, hzW, hzc⟩
      obtain ⟨P, hPF, hzP⟩ := hzc hzA
      exact mem_biUnion (Finset.mem_coe.mpr hPF) ⟨hzP, mem_iInter₂.mp hzW P hPF⟩
    _ = ⨆ P ∈ (F : Set (Ideal (AnalyticGerm (n + 1)))),
        dimH ({z | ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0} ∩ W P) :=
      dimH_bUnion F.countable_toSet _
    _ ≤ _ := iSup₂_le fun P hP ↦ hWdim P hP

private theorem adim9_analytic_dimH_le (n e : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (hbound : ∀ x ∈ A,
        ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ (e : WithBot ℕ∞)) :
    dimH A ≤ ((2 * e : ℕ) : ℝ≥0∞) := by
  classical
  apply adim9_dimH_le_of_local
  intro x hx
  obtain ⟨U, hU, hxU, m, f, hf, hCf⟩ := hloc x hx
  let A' : Set (Fin (n + 1) → ℂ) := {z | x + z ∈ A}
  have htrans : Continuous (fun z : Fin (n + 1) → ℂ ↦ x + z) := continuous_const.add continuous_id
  have hAloc : ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
      ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f U) ∧
        ∀ z ∈ U, (z ∈ A' ↔ ∀ f ∈ s, f z = 0) := by
    refine ⟨(fun z ↦ x + z) ⁻¹' U, hU.preimage htrans, by simpa using hxU,
      Finset.univ.image (fun j z ↦ f j (x + z)), ?_, ?_⟩
    · intro φ hφ z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hφ
      exact (hf j (x + z) hz).comp_of_eq (analyticAt_const.add analyticAt_id) rfl
    · intro z hz
      simp only [A', mem_ofPred_eq, Finset.mem_image, Finset.mem_univ, true_and,
        forall_exists_index, forall_apply_eq_imp_iff]
      exact hCf (x + z) hz
  have hgerm : adim2_germ (n + 1) A' 0 = adim2_germ (n + 1) A x := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp [A']
  obtain ⟨W, hW, hWdim⟩ := adim9_local_dimH n e A' hAloc (by rw [hgerm]; exact hbound x hx)
  refine ⟨(fun y ↦ y - x) ⁻¹' W,
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
  have himg : A ∩ (fun y ↦ y - x) ⁻¹' W = (fun z ↦ x + z) '' (A' ∩ W) := by
    ext y
    constructor
    · rintro ⟨hyC, hyW⟩
      exact ⟨y - x, ⟨by simpa [A'] using hyC, hyW⟩, by simp⟩
    · rintro ⟨z, ⟨hzA, hzW⟩, rfl⟩
      exact ⟨hzA, by simpa using hzW⟩
  have hiso : Isometry (fun z : Fin (n + 1) → ℂ ↦ x + z) := (IsometryEquiv.addLeft x).isometry
  rw [himg, hiso.dimH_image]
  exact hWdim

private theorem adim9_cone_dimH_le (n r : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hbound : ∀ x ∈ C,
        ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) :
    dimH (insert 0 C) ≤ ((2 * (r + 1) : ℕ) : ℝ≥0∞) := by
  have hC := adim9_analytic_dimH_le n (r + 1) C (fun x hx ↦ by
    obtain ⟨U, hU, hxU, -, h⟩ := hloc x hx
    exact ⟨U, hU, hxU, h⟩) hbound
  rw [insert_eq, dimH_union, dimH_singleton]
  exact max_le bot_le hC

private theorem adim9_volume_zero_of_dimH_lt (m : ℕ) (S : Set (Fin m → ℂ))
    (h : dimH S < ((2 * m : ℕ) : ℝ≥0∞)) : MeasureTheory.volume S = 0 := by
  let e : (Fin m → ℂ) ≃L[ℝ] (Fin (2 * m) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [adim9_finrank_real_pi, Module.finrank_fin_fun])
  have h₀ : μH[(((2 * m : ℕ) : ℝ≥0) : ℝ)] (e '' S) = 0 :=
    hausdorffMeasure_of_dimH_lt (by rw [e.dimH_image]; exact_mod_cast h)
  have hpi : (μH[(((2 * m : ℕ) : ℝ≥0) : ℝ)] : MeasureTheory.Measure (Fin (2 * m) → ℝ)) =
      MeasureTheory.volume := by
    have := MeasureTheory.hausdorffMeasure_pi_real (ι := Fin (2 * m))
    simp only [Fintype.card_fin] at this
    simpa using this
  have h₁ : MeasureTheory.volume (e '' S) = 0 := by rw [← hpi]; exact h₀
  let μ : MeasureTheory.Measure (Fin m → ℂ) := MeasureTheory.Measure.map e.symm MeasureTheory.volume
  have hμ : μ.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map _
  have hμS : μ S = 0 := by
    have heq : μ = MeasureTheory.Measure.map e.symm.toHomeomorph.toMeasurableEquiv
        MeasureTheory.volume := rfl
    rw [heq, MeasurableEquiv.map_apply]
    convert h₁ using 2
    exact (e.toEquiv.image_eq_preimage_symm S).symm
  rw [MeasureTheory.Measure.isAddLeftInvariant_eq_smul MeasureTheory.volume μ]
  simp [hμS]

/-- A linear image of an analytic set whose germ components have dimension at most `e`
has Hausdorff dimension at most `2e`. When `e < m` it is Lebesgue null in `ℂ^m`, so its
complement is dense.
Source: Chirka, Complex Analytic Sets, §§3--4, local parametrization and dimension;
Falconer, Fractal Geometry, Corollary 2.4, Lipschitz images and Hausdorff dimension. -/
theorem adim9_analytic_linear_image_null (n e m : ℕ) (he : e < m)
    (A : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      ∃ (k : ℕ) (f : Fin k → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (hbound : ∀ x ∈ A,
        ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ (e : WithBot ℕ∞))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin m → ℂ)) :
    dimH (L '' A) ≤ ((2 * e : ℕ) : ℝ≥0∞) ∧ MeasureTheory.volume (L '' A) = 0 ∧
      Dense (L '' A)ᶜ := by
  have hdim : dimH (L '' A) ≤ ((2 * e : ℕ) : ℝ≥0∞) :=
    (L.lipschitzWith.dimH_image_le A).trans (adim9_analytic_dimH_le n e A hloc hbound)
  have hlt : dimH (L '' A) < ((2 * m : ℕ) : ℝ≥0∞) :=
    hdim.trans_lt (by exact_mod_cast (by omega : 2 * e < 2 * m))
  refine ⟨hdim, adim9_volume_zero_of_dimH_lt m _ hlt, ?_⟩
  apply dense_compl_of_dimH_lt_finrank
  rwa [adim9_finrank_real_pi]

/-- The target dimension is the attained maximum of the local component dimensions.
The projection is defined on the whole cone, including its vertex.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
proof of Chow's theorem by linear projection of a homogeneous cone;
Chirka, Complex Analytic Sets, §§3--4, dimension and generic projections. -/
theorem adim9_cone_finite_projection_aux (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    ∃ r : ℕ, r ≤ n ∧
      (∀ x ∈ C,
        ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      (∃ x ∈ C, ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ),
        Function.Surjective L ∧
        IsProperMap (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
        (∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) ∧
        (L ⁻¹' {0}) ∩ insert 0 C = {0} := by
  obtain ⟨r, hr, hle, hatt⟩ :=
    adim9_cone_dimension_maximum n C hzero hne hclosed hscale hloc
  obtain ⟨K, hK, hKC⟩ := adim9_center_of_dimH (n + 1) (r + 1) (by omega) C hzero hscale
    (adim9_cone_dimH_le n r C hloc hle)
  obtain ⟨L, hsurj, hcentral⟩ := adim9_projection_of_disjoint_center (n + 1) (r + 1) C K hK hKC
  have hproper := adim9_cone_proper_of_central (n + 1) (r + 1) C hzero hne hclosed hscale L hcentral
  exact ⟨r, hr, hle, hatt, L, hsurj, hproper,
    adim9_cone_finite_fibres_of_proper (n + 1) (r + 1) C hloc L hproper hcentral, hcentral⟩

/-- Local irreducible components of a punctured analytic cone have an attained
dimension in the ambient range.
Source: Gunning--Rossi, III.B--C, local parametrization and dimension. -/
theorem adim9_component_dimension_exists_aux (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (x : Fin (n + 1) → ℂ) (hx : x ∈ C)
    (P : Ideal (AnalyticGerm (n + 1)))
    (hP : P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ n + 1 ∧
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) := by
  obtain ⟨U, hU, hxU, -, m, f, hf, hC⟩ := hloc x hx
  have hdim := adim3_cone_lower_bound n C hzero hclosed hscale hloc
  obtain ⟨F, hF, -, hcomponents⟩ :=
    adim7_component_comparison n C x hx U hU hxU m f hf hC (hdim x hx)
  have hPF : P ∈ F := by
    rw [← Finset.mem_coe, hF]
    exact hP
  obtain ⟨-, d, -, -, hdpos, hdle, -, -, -, hdeq⟩ := hcomponents P hPF
  exact ⟨d, hdpos, hdle, hdeq⟩

/-- Only finitely many dimensions occur among the local irreducible components
of a punctured analytic cone.
Source: Gunning--Rossi, III.B--C, local dimension. -/
theorem adim9_component_dimensions_finite_aux (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    {d : ℕ | ∃ x ∈ C,
      ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞)}.Finite := by
  apply (Set.finite_Icc 1 (n + 1)).subset
  rintro d ⟨x, hx, P, hP, hd⟩
  obtain ⟨e, hepos, hele, he⟩ :=
    adim9_component_dimension_exists_aux n C hzero hclosed hscale hloc x hx P hP
  have hed : e = d := by
    exact_mod_cast he.symm.trans hd
  simpa [hed] using And.intro hepos hele

/-- The points where at least one local irreducible component has the given dimension.
Source: Gunning--Rossi, III.B--C, local irreducible components and dimension. -/
def adim9_componentDimensionPart (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (d : ℕ) : Set (Fin (n + 1) → ℂ) :=
  {x | x ∈ C ∧
    ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞)}

theorem adim9_mem_componentDimensionPart_iff (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ)) (d : ℕ) (x : Fin (n + 1) → ℂ) :
    x ∈ adim9_componentDimensionPart n C d ↔
      x ∈ C ∧
        ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) := by
  rfl

theorem adim9_componentDimensionPart_subset (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ)) (d : ℕ) :
    adim9_componentDimensionPart n C d ⊆ C := by
  intro x hx
  exact hx.1

theorem adim9_zero_not_mem_componentDimensionPart (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ)) (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (d : ℕ) :
    (0 : Fin (n + 1) → ℂ) ∉ adim9_componentDimensionPart n C d := by
  exact fun h ↦ hzero h.1

theorem adim9_nonempty_componentDimensionParts_finite (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    {d : ℕ | (adim9_componentDimensionPart n C d).Nonempty}.Finite := by
  apply (adim9_component_dimensions_finite_aux n C hzero hclosed hscale hloc).subset
  rintro d ⟨x, hx⟩
  exact ⟨x, hx.1, hx.2⟩

theorem adim9_nonempty_componentDimensionPart_bounds (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (hd : (adim9_componentDimensionPart n C d).Nonempty) :
    1 ≤ d ∧ d ≤ n + 1 := by
  obtain ⟨x, hxC, P, hP, hdim⟩ := hd
  obtain ⟨e, hepos, hele, hedim⟩ :=
    adim9_component_dimension_exists_aux n C hzero hclosed hscale hloc x hxC P hP
  have hed : e = d := by
    exact_mod_cast hedim.symm.trans hdim
  simpa [hed] using And.intro hepos hele

private theorem adim9b_dimH_le_of_local {X : Type*} [EMetricSpace X] [SecondCountableTopology X]
    (S : Set X) (a : ℝ≥0∞) (h : ∀ x ∈ S, ∃ U ∈ 𝓝 x, dimH (S ∩ U) ≤ a) :
    dimH S ≤ a := by
  choose! U hU hdim using h
  obtain ⟨t, hts, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x ↦ S ∩ U x) (s := S) (fun x hx ↦ inter_mem_nhdsWithin S (hU x hx))
  calc
    dimH S ≤ dimH (⋃ x ∈ t, S ∩ U x) := dimH_mono hcover
    _ = ⨆ x ∈ t, dimH (S ∩ U x) := dimH_bUnion htc _
    _ ≤ a := iSup₂_le fun x hx ↦ hdim x (hts hx)

private theorem adim9b_dimH_le_of_approximatesLinearOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {f' : E ≃L[ℂ] F} {s : Set E} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (f' : E →L[ℂ] F) s c)
    (hc : Subsingleton E ∨ c < ‖(f'.symm : F →L[ℂ] E)‖₊⁻¹) (t : Set E) (hts : t ⊆ s) :
    dimH t ≤ dimH (f '' t) := by
  have hanti := hf.antilipschitzWith hc
  have h := hanti.le_dimH_image {p : s | p.val ∈ t}
  have hval : Subtype.val '' {p : s | p.val ∈ t} = t := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨⟨x, hts hx⟩, hx, rfl⟩
  have himg : s.domRestrict f '' {p : s | p.val ∈ t} = f '' t := by
    conv_rhs => rw [← hval, image_image]
    rfl
  calc
    dimH t = dimH {p : s | p.val ∈ t} := by
      rw [← (isometry_subtype_coe (s := s)).dimH_image, hval]
    _ ≤ dimH (s.domRestrict f '' {p : s | p.val ∈ t}) := h
    _ = dimH (f '' t) := by rw [himg]

private theorem adim9b_finrank_real_pi (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  simp [finrank_real_of_complex]

private theorem adim9b_dimH_regular_zero_set (d : ℕ) (F : (Fin d → ℂ) × ℂ → ℂ)
    (H : Set ((Fin d → ℂ) × ℂ))
    (hH : ∀ p ∈ H, F p = 0 ∧ HasStrictFDerivAt F (fderiv ℂ F p) p ∧
      deriv (fun t ↦ F (p.1, t)) p.2 ≠ 0) :
    dimH H ≤ ((2 * d : ℕ) : ℝ≥0∞) := by
  apply adim9b_dimH_le_of_local
  intro p hp
  obtain ⟨_, hF, hD⟩ := hH p hp
  set A := fderiv ℂ F p with hA
  set b := A (0, 1) with hbdef
  have hb : b ≠ 0 := by
    have h1 : HasDerivAt (fun t : ℂ ↦ ((p.1, t) : (Fin d → ℂ) × ℂ)) ((0 : Fin d → ℂ), (1 : ℂ)) p.2 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have h2 := hF.hasFDerivAt.comp_hasDerivAt p.2 h1
    have h3 : deriv (fun t ↦ F (p.1, t)) p.2 = b := h2.deriv
    rwa [h3] at hD
  have hsplit : ∀ u : Fin d → ℂ, ∀ s : ℂ, A (u, s) = A (u, 0) + s * b := by
    intro u s
    have : ((u, s) : (Fin d → ℂ) × ℂ) = (u, 0) + s • ((0 : Fin d → ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  let f₁ : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).prod A
  let f₂ : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).prod (b⁻¹ • (ContinuousLinearMap.snd ℂ _ _ -
      (A.comp (ContinuousLinearMap.inl ℂ _ _)).comp (ContinuousLinearMap.fst ℂ _ _)))
  have h21 : ∀ q, f₂ (f₁ q) = q := by
    intro q
    obtain ⟨u, s⟩ := q
    simp only [f₁, f₂, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [hsplit u s]
    ext
    · rfl
    · simp only
      field_simp
      ring
  have h12 : ∀ q, f₁ (f₂ q) = q := by
    intro q
    obtain ⟨u, y⟩ := q
    simp only [f₁, f₂, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [hsplit]
    ext
    · rfl
    · simp only
      field_simp
      ring
  let Φ' := ContinuousLinearEquiv.equivOfInverse f₁ f₂ h21 h12
  let Φ : (Fin d → ℂ) × ℂ → (Fin d → ℂ) × ℂ := fun q ↦ (q.1, F q)
  have hΦ : HasStrictFDerivAt Φ (Φ' : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ)) p :=
    hasStrictFDerivAt_fst.prodMk hF
  set N := ‖(Φ'.symm : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ))‖₊ with hN
  have hN0 : N ≠ 0 := by
    intro h0
    have h := congrArg (fun T : ((Fin d → ℂ) × ℂ) →L[ℂ] ((Fin d → ℂ) × ℂ) ↦
      T ((0 : Fin d → ℂ), (1 : ℂ))) (nnnorm_eq_zero.mp h0)
    simp only [ContinuousLinearEquiv.coe_coe] at h
    have := congrArg Prod.snd (Φ'.symm.injective (h.trans (map_zero Φ'.symm).symm))
    simp at this
  have hcpos : 0 < N⁻¹ / 2 := by
    apply div_pos (inv_pos.mpr (pos_iff_ne_zero.mpr hN0)) two_pos
  obtain ⟨s, hs, happrox⟩ := hΦ.approximates_deriv_on_nhds (Or.inr hcpos)
  refine ⟨s, hs, ?_⟩
  calc
    dimH (H ∩ s) ≤ dimH (Φ '' (H ∩ s)) :=
      adim9b_dimH_le_of_approximatesLinearOn happrox
        (Or.inr (NNReal.half_lt_self (inv_pos.mpr (pos_iff_ne_zero.mpr hN0)).ne')) _
        inter_subset_right
    _ ≤ dimH (range (ContinuousLinearMap.inl ℝ (Fin d → ℂ) ℂ)) := by
      apply dimH_mono
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q.1, by simp [Φ, (hH q hq.1).1]⟩
    _ ≤ Module.finrank ℝ (Fin d → ℂ) :=
      (ContinuousLinearMap.inl ℝ (Fin d → ℂ) ℂ).differentiable.dimH_range_le
    _ = ((2 * d : ℕ) : ℝ≥0∞) := by rw [adim9b_finrank_real_pi]

private theorem adim9b_krullDim_drop {R : Type*} [CommRing R] (P Q : Ideal R) [P.IsPrime]
    (hPQ : P ≤ Q) (b : R) (hbP : b ∉ P) (hbQ : b ∈ Q) :
    ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  have hb : Ideal.Quotient.mk P b ∈ nonZeroDivisors (R ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  let f : (R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P b} →+* R ⧸ Q :=
    Ideal.Quotient.lift _ (Ideal.Quotient.factor hPQ) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hbQ, mul_zero])
  have hf : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hPQ)
  calc
    ringKrullDim (R ⧸ Q) + 1 ≤
        ringKrullDim ((R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P b}) + 1 := by
      gcongr
      exact ringKrullDim_le_of_surjective f hf
    _ ≤ ringKrullDim (R ⧸ P) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hb

private theorem adim9b_le_pred_of_succ_le (x : WithBot ℕ∞) (d : ℕ) (h : x + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    x ≤ (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe] at h'
      simp at h'
    | coe k =>
      have : k + 1 ≤ d + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ d)

private theorem adim9b_vanish_of_mem_span (n : ℕ) (G : Finset (AnalyticGerm n))
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ g, Germ.ofFun (rep g) = g.val)
    (b : AnalyticGerm n) (hb : b ∈ Ideal.span (G : Set (AnalyticGerm n)))
    (B : (Fin n → ℂ) → ℂ) (hB : Germ.ofFun B = b.val) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ g ∈ G, rep g z = 0) → B z = 0 := by
  classical
  obtain ⟨f, -, hsum⟩ := Submodule.mem_span_finset.mp hb
  have hval : b.val = Germ.ofFun (fun z ↦ ∑ g ∈ G, rep (f g) z * rep g z) := by
    rw [← hsum]
    change (analyticGermSubring n).subtype (∑ g ∈ G, f g • g) = _
    rw [map_sum]
    simp only [smul_eq_mul, map_mul, Subring.subtype_apply, ← hrep]
    change (∑ g ∈ G, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (rep (f g)) *
      Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (rep g)) = Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) _
    simp only [← map_mul, ← map_sum]
    congr 1
    funext z
    simp [Finset.sum_apply]
  have heq : B =ᶠ[𝓝 (0 : Fin n → ℂ)] fun z ↦ ∑ g ∈ G, rep (f g) z * rep g z :=
    Germ.coe_eq.mp (hB.trans hval)
  filter_upwards [heq] with z hz hzero
  rw [hz]
  exact Finset.sum_eq_zero fun g hg ↦ by rw [hzero g hg, mul_zero]

private theorem adim9b_poly_rep (d : ℕ) (T : Polynomial (AnalyticGerm d)) :
    ∃ t : Polynomial ((Fin d → ℂ) → ℂ), ∀ i, AnalyticAt ℂ (t.coeff i) 0 ∧
      Germ.ofFun (t.coeff i) = (T.coeff i).val := by
  classical
  choose a ha hrep using fun i ↦ (T.coeff i).property
  refine ⟨T.sum fun i _ ↦ Polynomial.monomial i (a i), fun i ↦ ?_⟩
  by_cases hi : i ∈ T.support
  · simpa [Polynomial.sum, Polynomial.coeff_monomial, hi] using And.intro (ha i) (hrep i)
  · have hTi : T.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
    simpa [Polynomial.sum, Polynomial.coeff_monomial, hi, hTi] using
      (And.intro (show AnalyticAt ℂ (0 : (Fin d → ℂ) → ℂ) 0 from analyticAt_const)
        (rfl : Germ.ofFun (0 : (Fin d → ℂ) → ℂ) = (0 : AnalyticGerm d).val))

private theorem adim9b_eval_germ (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (T : Polynomial (AnalyticGerm d)) (t : Polynomial ((Fin d → ℂ) → ℂ))
    (ht : ∀ i, AnalyticAt ℂ (t.coeff i) 0 ∧ Germ.ofFun (t.coeff i) = (T.coeff i).val) :
    ∃ b : AnalyticGerm n, b.val = Germ.ofFun (fun z ↦
        t.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (ℓ z)) ∧
      T.eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b := by
  classical
  set N := max T.natDegree t.natDegree + 1 with hN
  let bi : ℕ → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z ↦ t.coeff i (π z)), _,
      (ht i).1.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  refine ⟨∑ i ∈ Finset.range N, bi i * v ^ i, ?_, ?_⟩
  · change (analyticGermSubring n).subtype (∑ i ∈ Finset.range N, bi i * v ^ i) = _
    rw [map_sum]
    simp only [map_mul, map_pow, Subring.subtype_apply, hv]
    change (∑ i ∈ Finset.range N, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))
      (fun z ↦ t.coeff i (π z)) * (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ ℓ z)) ^ i) =
        Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) _
    simp only [← map_mul, ← map_pow, ← map_sum]
    congr 1
    funext z
    rw [Polynomial.eval₂_eq_sum_range' _ (by omega : t.natDegree < N)]
    simp [Finset.sum_apply]
  · rw [Polynomial.eval₂_eq_sum_range' _ (by omega : T.natDegree < N), map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_pow,
      hcomp (T.coeff i) (t.coeff i) (ht i).1 (ht i).2 (bi i) rfl]

private theorem adim9b_polynomial_representatives_eq (d : ℕ)
    (p q : Polynomial ((Fin d → ℂ) → ℂ))
    (h : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)))) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      p.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) =
        q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) := by
  classical
  have hc (i : ℕ) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), p.coeff i w = q.coeff i w := by
    apply Germ.coe_eq.mp
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom] using congrArg (fun a ↦ a.coeff i) h
  have hs : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ i ∈ p.support ∪ q.support, p.coeff i w = q.coeff i w := by
    rw [Finset.eventually_all]
    exact fun i _ ↦ hc i
  filter_upwards [hs] with w hw
  ext i
  simp only [Polynomial.coeff_map, Pi.evalRingHom_apply]
  by_cases hi : i ∈ p.support ∪ q.support
  · exact hw i hi
  · have hp : p.coeff i = 0 := Polynomial.notMem_support_iff.mp
      (fun hip ↦ hi (Finset.mem_union_left _ hip))
    have hq : q.coeff i = 0 := Polynomial.notMem_support_iff.mp
      (fun hiq ↦ hi (Finset.mem_union_right _ hiq))
    rw [hp, hq]

private theorem adim9b_poly_coeff_analytic_eventually (d : ℕ) (t : Polynomial ((Fin d → ℂ) → ℂ))
    (ht : ∀ i, AnalyticAt ℂ (t.coeff i) 0) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ i, AnalyticAt ℂ (t.coeff i) w := by
  classical
  have hs : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ i ∈ t.support, AnalyticAt ℂ (t.coeff i) w := by
    rw [Finset.eventually_all]
    exact fun i _ ↦ (ht i).eventually_analyticAt
  filter_upwards [hs] with w hw i
  by_cases hi : i ∈ t.support
  · exact hw i hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    exact analyticAt_const

private theorem adim9b_poly_eval_analyticAt (d : ℕ) (t : Polynomial ((Fin d → ℂ) → ℂ))
    (p₀ : (Fin d → ℂ) × ℂ) (h : ∀ i, AnalyticAt ℂ (t.coeff i) p₀.1) :
    AnalyticAt ℂ (fun p : (Fin d → ℂ) × ℂ ↦
      t.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) p.1) p.2) p₀ := by
  simp only [Polynomial.eval₂_eq_sum_range, Pi.evalRingHom_apply]
  have := Finset.analyticAt_sum (f := fun i (p : (Fin d → ℂ) × ℂ) ↦ t.coeff i p.1 * p.2 ^ i)
    (c := p₀) (Finset.range (t.natDegree + 1))
    (fun i _ ↦ ((h i).comp analyticAt_fst).mul (analyticAt_snd.pow i))
  convert this using 1
  funext p
  simp [Finset.sum_apply]

private theorem adim9b_poly_deriv (d : ℕ) (t : Polynomial ((Fin d → ℂ) → ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    deriv (fun s : ℂ ↦ t.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) s) s =
      t.derivative.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) s := by
  simp only [← Polynomial.eval_map, Polynomial.deriv, Polynomial.derivative_map]

private theorem adim9b_off_discriminant_dimH (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (G : Finset (AnalyticGerm n)) (hG : Ideal.span (G : Set (AnalyticGerm n)) = P)
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ g, Germ.ofFun (rep g) = g.val) :
    ∃ (δ : AnalyticGerm d) (Δ : (Fin d → ℂ) → ℂ), δ ≠ 0 ∧ AnalyticAt ℂ Δ 0 ∧
      Germ.ofFun Δ = δ.val ∧ ∃ W ∈ 𝓝 (0 : Fin n → ℂ),
        dimH {z | z ∈ W ∧ (∀ g ∈ G, rep g z = 0) ∧ Δ (π z) ≠ 0} ≤
          ((2 * d : ℕ) : ℝ≥0∞) := by
  classical
  let ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun w ↦
    Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  obtain ⟨ℓ, v, Q, δ, R, B, Cb, hv, -, -, hδ, hbez, hmin, hcoord⟩ :=
    adim7_primitive_form n d P hP π θ hfinite hinj hcomp c hc
  obtain ⟨q, hq⟩ := adim9b_poly_rep d Q
  obtain ⟨b, hb⟩ := adim9b_poly_rep d B
  obtain ⟨cb, hcb⟩ := adim9b_poly_rep d Cb
  choose r hr using fun i ↦ adim9b_poly_rep d (R i)
  obtain ⟨Δ, hΔ, hΔrep⟩ := δ.property
  refine ⟨δ, Δ, hδ, hΔ, hΔrep, ?_⟩
  -- the primitive relation vanishes on the component
  have hQzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ g ∈ G, rep g z = 0) →
      q.eval₂ (ev (π z)) (ℓ z) = 0 := by
    obtain ⟨bq, hbq, hQe⟩ := adim9b_eval_germ n d P π θ hcomp ℓ v hv Q q hq
    have hmem : bq ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, ← hQe]
      exact (hmin Q).mpr dvd_rfl
    exact adim9b_vanish_of_mem_span n G rep hrep bq hmem _ hbq.symm
  -- the coordinates are reconstructed on the component
  let bΔ : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ Δ (π z)), _,
    hΔ.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hθδ : θ δ = Ideal.Quotient.mk P bΔ := hcomp δ Δ hΔ hΔrep bΔ rfl
  have hcoordzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, (∀ g ∈ G, rep g z = 0) →
      Δ (π z) * z i - (r i).eval₂ (ev (π z)) (ℓ z) = 0 := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨br, hbr, hRe⟩ := adim9b_eval_germ n d P π θ hcomp ℓ v hv (R i) (r i) (hr i)
    have hmem : bΔ * c i - br ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hθδ, hcoord i, hRe,
        sub_self]
    apply adim9b_vanish_of_mem_span n G rep hrep _ hmem
    rw [show (bΔ * c i - br).val = bΔ.val * (c i).val - br.val from rfl, hbr]
    rfl
  -- the Bezout identity holds near the origin
  have hbezout : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ s : ℂ,
      b.eval₂ (ev w) s * q.eval₂ (ev w) s + cb.eval₂ (ev w) s * q.derivative.eval₂ (ev w) s =
        Δ w := by
    have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (T : Polynomial (AnalyticGerm d))
        (hFT : ∀ i, AnalyticAt ℂ (F.coeff i) 0 ∧ Germ.ofFun (F.coeff i) = (T.coeff i).val) :
        F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
          T.map (analyticGermSubring d).subtype := by
      ext i
      simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
        (hFT i).2
    have heq : (b * q + cb * q.derivative).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        (Polynomial.C Δ).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        ← Polynomial.derivative_map, hmap b B hb, hmap q Q hq, hmap cb Cb hcb,
        Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
        ← Polynomial.map_add, hbez, Polynomial.map_C, Polynomial.map_C]
      congr 1
      exact hΔrep.symm
    filter_upwards [adim9b_polynomial_representatives_eq d _ _ heq] with w hw s
    have := congrArg (fun a : Polynomial ℂ ↦ a.eval s) hw
    simp only [Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C] at this
    exact this
  -- an open parameter neighbourhood with analytic data
  have hnear : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      (∀ s : ℂ, b.eval₂ (ev w) s * q.eval₂ (ev w) s +
        cb.eval₂ (ev w) s * q.derivative.eval₂ (ev w) s = Δ w) ∧
      AnalyticAt ℂ Δ w ∧ (∀ i, AnalyticAt ℂ (q.coeff i) w) ∧
      ∀ j i, AnalyticAt ℂ ((r j).coeff i) w := by
    have hrall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ j i, AnalyticAt ℂ ((r j).coeff i) w := by
      rw [Filter.eventually_all]
      exact fun j ↦ adim9b_poly_coeff_analytic_eventually d (r j) (fun i ↦ (hr j i).1)
    filter_upwards [hbezout, hΔ.eventually_analyticAt,
      adim9b_poly_coeff_analytic_eventually d q (fun i ↦ (hq i).1), hrall] with w h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp hnear
  let H : Set ((Fin d → ℂ) × ℂ) :=
    {p | p.1 ∈ V ∧ Δ p.1 ≠ 0 ∧ q.eval₂ (ev p.1) p.2 = 0}
  have hHdim : dimH H ≤ ((2 * d : ℕ) : ℝ≥0∞) := by
    apply adim9b_dimH_regular_zero_set d (fun p ↦ q.eval₂ (ev p.1) p.2) H
    rintro ⟨w, s⟩ ⟨hwV, hΔw, hqs⟩
    obtain ⟨hB, -, hqa, -⟩ := hVsub hwV
    refine ⟨hqs, (adim9b_poly_eval_analyticAt d q (w, s) hqa).hasStrictFDerivAt, ?_⟩
    change deriv (fun s : ℂ ↦ q.eval₂ (ev w) s) s ≠ 0
    rw [adim9b_poly_deriv]
    intro h0
    apply hΔw
    rw [← hB s, hqs, h0, mul_zero, mul_zero, add_zero]
  let Gm : (Fin d → ℂ) × ℂ → (Fin n → ℂ) := fun p i ↦ (r i).eval₂ (ev p.1) p.2 / Δ p.1
  have hGm : DifferentiableOn ℂ Gm H := by
    rintro ⟨w, s⟩ ⟨hwV, hΔw, -⟩
    obtain ⟨-, hΔa, -, hra⟩ := hVsub hwV
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_pi]
    intro i
    show DifferentiableAt ℂ (fun p : (Fin d → ℂ) × ℂ ↦ (r i).eval₂ (ev p.1) p.2 / Δ p.1) (w, s)
    exact ((adim9b_poly_eval_analyticAt d (r i) (w, s) (hra i)).div
      (hΔa.comp_of_eq analyticAt_fst rfl) hΔw).differentiableAt
  have hW : π ⁻¹' V ∈ 𝓝 (0 : Fin n → ℂ) :=
    π.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hVopen.mem_nhds hV0)
  refine ⟨_, inter_mem (hQzero.and hcoordzero) hW, ?_⟩
  calc
    dimH _ ≤ dimH (Gm '' H) := by
      apply dimH_mono
      rintro z ⟨⟨⟨hzq, hzc⟩, hzV⟩, hzG, hzΔ⟩
      refine ⟨(π z, ℓ z), ⟨hzV, hzΔ, hzq hzG⟩, ?_⟩
      funext i
      have := hzc i hzG
      change (r i).eval₂ (ev (π z)) (ℓ z) / Δ (π z) = z i
      rw [div_eq_iff hzΔ]
      linear_combination -this
    _ ≤ dimH H := hGm.dimH_image_le
    _ ≤ _ := hHdim

private theorem adim9b_point_germ (n : ℕ) (A : Set (Fin n → ℂ))
    (P : Ideal (AnalyticGerm n)) (hP : P ∈ (adim2_ideal n (adim2_germ n A 0)).minimalPrimes)
    (hdim : ringKrullDim (AnalyticGerm n ⧸ P) < 1) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ A → z = 0 := by
  classical
  let I := adim2_ideal n (adim2_germ n A 0)
  let : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro a b hab
    rw [analyticGerm_isUnit_iff] at hab
    simp only [map_add] at hab
    by_cases ha : analyticGermValue n a = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [ha] using hab
    · left
      rwa [analyticGerm_isUnit_iff]
  let : P.IsPrime := hP.isPrime
  have hPm : P.IsMaximal := by
    apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr
    let : Ring.KrullDimLE 0 (AnalyticGerm n ⧸ P) := Ring.krullDimLE_iff.mpr <|
      le_of_not_gt (fun hpos ↦
        not_lt_of_ge ((WithBot.one_le_iff_pos _).mpr hpos) hdim)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hPeq : P = IsLocalRing.maximalIdeal (AnalyticGerm n) :=
    IsLocalRing.eq_maximalIdeal hPm
  have hIP : I = P := by
    have hunique : ∀ Q ∈ I.minimalPrimes, Q = P := by
      intro Q hQ
      have hQP : Q ≤ P := hPeq.symm ▸ IsLocalRing.le_maximalIdeal hQ.isPrime.ne_top
      exact hQP.antisymm (hP.2 hQ.1 hQP)
    have hrad : I.radical = I := adim2_radical n _
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    apply le_antisymm (sInf_le hP)
    exact le_sInf fun Q hQ ↦ (hunique Q hQ).ge
  have hmax : (analyticGermMaximalIdeal n).IsMaximal := by
    apply RingHom.ker_isMaximal_of_surjective
    intro c
    exact ⟨⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩
  have hPval : P = analyticGermMaximalIdeal n :=
    hPeq.trans (IsLocalRing.eq_maximalIdeal hmax).symm
  have hcoord : ∀ i : Fin n, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ A → z i = 0 := by
    intro i
    let c : AnalyticGerm n := ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
    have hc : c ∈ I := by
      rw [hIP, hPval]
      exact rfl
    change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), 0 + z ∈ A → z i = 0 at hc
    simpa using hc
  filter_upwards [Filter.eventually_all.mpr hcoord] with z hz hzA
  funext i
  exact hz i hzA

private theorem adim9b_zeroSet_eq (n : ℕ) (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ)
    (hrep : ∀ g, Germ.ofFun (rep g) = g.val) (P : Ideal (AnalyticGerm n)) :
    adim2_zeroSet n P = Germ.ofFun (fun z ↦ ∀ g ∈ adim2_generators n P, rep g z = 0) := by
  classical
  unfold adim2_zeroSet
  induction adim2_generators n P using Finset.induction_on with
  | empty => simp; rfl
  | insert g s hg ih =>
    rw [Finset.inf_insert, ih]
    have hz : adim2_zero n g = Germ.ofFun (fun z ↦ rep g z = 0) := by
      unfold adim2_zero
      rw [← hrep g]
      rfl
    rw [hz]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp

private theorem adim9b_sup_zeroSet_eq (n : ℕ) (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ)
    (hrep : ∀ g, Germ.ofFun (rep g) = g.val) (F : Finset (Ideal (AnalyticGerm n))) :
    F.sup (adim2_zeroSet n) = Germ.ofFun (fun z ↦
      ∃ P ∈ F, ∀ g ∈ adim2_generators n P, rep g z = 0) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp; rfl
  | insert P s hP ih =>
    rw [Finset.sup_insert, ih, adim9b_zeroSet_eq n rep hrep P]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp

private theorem adim9b_span_generators (n : ℕ) (P : Ideal (AnalyticGerm n)) :
    Ideal.span (adim2_generators n P : Set (AnalyticGerm n)) = P :=
  ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) P).choose_spec

private theorem adim9b_mem_ideal_of_vanish (n : ℕ) (A : Set (Fin n → ℂ)) (g : AnalyticGerm n)
    (G : (Fin n → ℂ) → ℂ) (hG : Germ.ofFun G = g.val) (h : ∀ z ∈ A, G z = 0) :
    g ∈ adim2_ideal n (adim2_germ n A 0) := by
  change adim2_germ n A 0 ≤ g.val.map (· = 0)
  rw [← hG]
  apply Germ.coe_le.mpr
  exact Eventually.of_forall fun z hz ↦ h z (by simpa using hz)

private theorem adim9b_local_dimH (n e : ℕ) : ∀ (A : Set (Fin (n + 1) → ℂ)),
    (∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
      ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ f ∈ s, f z = 0)) →
    (∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ (e : WithBot ℕ∞)) →
    ∃ W ∈ 𝓝 (0 : Fin (n + 1) → ℂ), dimH (A ∩ W) ≤ ((2 * e : ℕ) : ℝ≥0∞) := by
  classical
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro A ⟨U, hU, hU0, s, hs, hAs⟩ hdim
  choose rep hrepa hrep using fun g : AnalyticGerm (n + 1) ↦ g.property
  -- away from the set
  by_cases hA0 : (0 : Fin (n + 1) → ℂ) ∉ A
  · obtain ⟨f, hf, hf0⟩ : ∃ f ∈ s, f 0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hA0 ((hAs 0 hU0).mpr hcon)
    have hev : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), f z ≠ 0 :=
      ((hs f hf 0 hU0).continuousAt).eventually_ne hf0
    refine ⟨_, inter_mem hev (hU.mem_nhds hU0), ?_⟩
    have hempty : A ∩ ({z | f z ≠ 0} ∩ U) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hzA hfz hzU
      exact hfz ((hAs z hzU).mp hzA f hf)
    rw [hempty, dimH_empty]
    exact bot_le
  push Not at hA0
  -- a zero-dimensional component makes the germ a point
  by_cases hpt : ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) < 1
  · obtain ⟨P, hP, hlt⟩ := hpt
    refine ⟨_, adim9b_point_germ (n + 1) A P hP hlt, ?_⟩
    calc
      dimH (A ∩ {z | z ∈ A → z = 0}) ≤ dimH ({0} : Set (Fin (n + 1) → ℂ)) :=
        dimH_mono fun z hz ↦ hz.2 hz.1
      _ = 0 := dimH_singleton _
      _ ≤ _ := bot_le
  push Not at hpt
  -- component comparison
  let m := s.card
  let f : Fin m → (Fin (n + 1) → ℂ) → ℂ := fun j ↦ (s.equivFin.symm j).val
  have hf : ∀ j, AnalyticOnNhd ℂ (f j) U := fun j ↦ hs _ (s.equivFin.symm j).property
  have hAf : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0) := by
    intro z hz
    rw [hAs z hz]
    constructor
    · intro h j
      exact h _ (s.equivFin.symm j).property
    · intro h g hg
      have := h (s.equivFin ⟨g, hg⟩)
      simpa [f] using this
  obtain ⟨F, hF, hcover, hcomp⟩ :=
    adim7_component_comparison n A 0 hA0 U hU hU0 m f hf hAf hpt
  rw [adim9b_sup_zeroSet_eq (n + 1) rep hrep F] at hcover
  have hcov : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z ∈ A →
      ∃ P ∈ F, ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0 := by
    have h := Germ.coe_eq.mp hcover
    filter_upwards [h] with z hz hzA
    have : (0 : Fin (n + 1) → ℂ) + z ∈ A := by simpa using hzA
    exact (show _ = _ from hz) ▸ this
  -- each component has small dimension near the origin
  have hpiece : ∀ P ∈ F, ∃ W ∈ 𝓝 (0 : Fin (n + 1) → ℂ),
      dimH ({z | ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0} ∩ W) ≤
        ((2 * e : ℕ) : ℝ≥0∞) := by
    intro P hPF
    have hPmin : P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes := by
      rw [← hF]
      exact hPF
    have hPprime : P.IsPrime := hPmin.isPrime
    obtain ⟨-, d, π, θ, hd1, -, hfin, hinj, hcompat, hdimP⟩ := hcomp P hPF
    have hde : d ≤ e := by
      have h := hdim P hPmin
      rw [hdimP] at h
      exact_mod_cast h
    set Gs := adim2_generators (n + 1) P with hGs
    obtain ⟨δ, Δ, hδ, hΔ, hΔrep, W₁, hW₁, hW₁dim⟩ :=
      adim9b_off_discriminant_dimH (n + 1) d P hPprime π θ hfin hinj hcompat Gs
        (adim9b_span_generators (n + 1) P) rep hrep
    -- an open neighbourhood where the equations are analytic
    have hΔπ : AnalyticAt ℂ (fun z ↦ Δ (π z)) (0 : Fin (n + 1) → ℂ) :=
      hΔ.comp_of_eq (π.analyticAt 0) (map_zero π)
    have hnear : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ),
        AnalyticAt ℂ (fun z ↦ Δ (π z)) z ∧ ∀ g ∈ Gs, AnalyticAt ℂ (rep g) z := by
      refine hΔπ.eventually_analyticAt.and ?_
      rw [Finset.eventually_all]
      exact fun g _ ↦ (hrepa g).eventually_analyticAt
    obtain ⟨U₀, hU₀sub, hU₀, hU₀0⟩ := mem_nhds_iff.mp hnear
    let D : Set (Fin (n + 1) → ℂ) :=
      {z | z ∈ U₀ ∧ (∀ g ∈ Gs, rep g z = 0) ∧ Δ (π z) = 0}
    let bΔ : AnalyticGerm (n + 1) := ⟨Germ.ofFun (fun z ↦ Δ (π z)), _, hΔπ, rfl⟩
    have hθδ : θ δ = Ideal.Quotient.mk P bΔ := hcompat δ Δ hΔ hΔrep bΔ rfl
    have hbΔP : bΔ ∉ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hθδ]
      intro h0
      exact hδ (hinj (h0.trans (map_zero θ).symm))
    have hPD : P ≤ adim2_ideal (n + 1) (adim2_germ (n + 1) D 0) := by
      rw [← adim9b_span_generators (n + 1) P, Ideal.span_le]
      intro g hg
      exact adim9b_mem_ideal_of_vanish (n + 1) D g (rep g) (hrep g)
        (fun z hz ↦ hz.2.1 g hg)
    have hbΔD : bΔ ∈ adim2_ideal (n + 1) (adim2_germ (n + 1) D 0) :=
      adim9b_mem_ideal_of_vanish (n + 1) D bΔ _ rfl (fun z hz ↦ hz.2.2)
    have hDdim : ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) D 0)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
      intro Q hQ
      apply adim9b_le_pred_of_succ_le
      rw [Nat.sub_add_cancel hd1, ← hdimP]
      exact adim9b_krullDim_drop P Q (hPD.trans hQ.1.2) bΔ hbΔP (hQ.1.2 hbΔD)
    have hDloc : ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
        ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f U) ∧
          ∀ z ∈ U, (z ∈ D ↔ ∀ f ∈ s, f z = 0) := by
      refine ⟨U₀, hU₀, hU₀0, insert (fun z ↦ Δ (π z)) (Gs.image rep), ?_, ?_⟩
      · intro φ hφ z hz
        rcases Finset.mem_insert.mp hφ with rfl | hφ
        · exact (hU₀sub hz).1
        · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hφ
          exact (hU₀sub hz).2 g hg
      · intro z hz
        simp only [D, Finset.forall_mem_insert, Finset.forall_mem_image, mem_ofPred_eq]
        tauto
    obtain ⟨W₂, hW₂, hW₂dim⟩ := ih (d - 1) (by omega) D hDloc hDdim
    refine ⟨W₁ ∩ W₂ ∩ U₀, inter_mem (inter_mem hW₁ hW₂) (hU₀.mem_nhds hU₀0), ?_⟩
    calc
      dimH ({z | ∀ g ∈ Gs, rep g z = 0} ∩ (W₁ ∩ W₂ ∩ U₀)) ≤
          dimH ({z | z ∈ W₁ ∧ (∀ g ∈ Gs, rep g z = 0) ∧ Δ (π z) ≠ 0} ∪ D ∩ W₂) := by
        apply dimH_mono
        rintro z ⟨hzG, ⟨hz₁, hz₂⟩, hz₀⟩
        by_cases hzΔ : Δ (π z) = 0
        · exact Or.inr ⟨⟨hz₀, hzG, hzΔ⟩, hz₂⟩
        · exact Or.inl ⟨hz₁, hzG, hzΔ⟩
      _ = max (dimH {z | z ∈ W₁ ∧ (∀ g ∈ Gs, rep g z = 0) ∧ Δ (π z) ≠ 0})
          (dimH (D ∩ W₂)) := dimH_union _ _
      _ ≤ ((2 * e : ℕ) : ℝ≥0∞) := by
        apply max_le
        · exact hW₁dim.trans (by exact_mod_cast (by omega : 2 * d ≤ 2 * e))
        · exact hW₂dim.trans (by exact_mod_cast (by omega : 2 * (d - 1) ≤ 2 * e))
  choose! W hW hWdim using hpiece
  refine ⟨(⋂ P ∈ F, W P) ∩ {z | z ∈ A → ∃ P ∈ F, ∀ g ∈ adim2_generators (n + 1) P,
      rep g z = 0}, inter_mem ((Filter.biInter_finset_mem F).mpr hW) hcov, ?_⟩
  calc
    dimH (A ∩ ((⋂ P ∈ F, W P) ∩ {z | z ∈ A → ∃ P ∈ F,
        ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0})) ≤
        dimH (⋃ P ∈ (F : Set (Ideal (AnalyticGerm (n + 1)))),
          {z | ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0} ∩ W P) := by
      apply dimH_mono
      rintro z ⟨hzA, hzW, hzc⟩
      obtain ⟨P, hPF, hzP⟩ := hzc hzA
      exact mem_biUnion (Finset.mem_coe.mpr hPF) ⟨hzP, mem_iInter₂.mp hzW P hPF⟩
    _ = ⨆ P ∈ (F : Set (Ideal (AnalyticGerm (n + 1)))),
        dimH ({z | ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0} ∩ W P) :=
      dimH_bUnion F.countable_toSet _
    _ ≤ _ := iSup₂_le fun P hP ↦ hWdim P hP

/-- Pullback of analytic function germs along an analytic map fixing the origin. -/
def adim9b_germPullback {n d : ℕ} (g : (Fin d → ℂ) → (Fin n → ℂ))
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) : AnalyticGerm n →+* AnalyticGerm d where
  toFun a := ⟨a.val.compTendsto g (hg0 ▸ hg.continuousAt), by
    obtain ⟨f, hf, hfa⟩ := a.property
    refine ⟨f ∘ g, hf.comp_of_eq hg hg0, ?_⟩
    rw [← hfa]
    rfl⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_mul' a b := by
    apply Subtype.ext
    change (a.val * b.val).compTendsto g (hg0 ▸ hg.continuousAt) =
      a.val.compTendsto g (hg0 ▸ hg.continuousAt) * b.val.compTendsto g (hg0 ▸ hg.continuousAt)
    exact Germ.inductionOn a.val fun _ ↦ Germ.inductionOn b.val fun _ ↦ rfl
  map_add' a b := by
    apply Subtype.ext
    change (a.val + b.val).compTendsto g (hg0 ▸ hg.continuousAt) =
      a.val.compTendsto g (hg0 ▸ hg.continuousAt) + b.val.compTendsto g (hg0 ▸ hg.continuousAt)
    exact Germ.inductionOn a.val fun _ ↦ Germ.inductionOn b.val fun _ ↦ rfl

theorem adim9b_germPullback_rep {n d : ℕ} (g : (Fin d → ℂ) → (Fin n → ℂ))
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (a : AnalyticGerm n)
    (f : (Fin n → ℂ) → ℂ) (hf : Germ.ofFun f = a.val) :
    (adim9b_germPullback g hg hg0 a).val = Germ.ofFun (f ∘ g) := by
  change a.val.compTendsto g (hg0 ▸ hg.continuousAt) = _
  rw [← hf]
  rfl

theorem adim9b_germPullback_surjective {n d : ℕ}
    (g : (Fin d → ℂ) → (Fin n → ℂ)) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (π : (Fin n → ℂ) → (Fin d → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (hsection : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), π (g w) = w) :
    Function.Surjective (adim9b_germPullback g hg hg0) := by
  intro a
  refine ⟨adim9b_germPullback π hπ hπ0 a, ?_⟩
  obtain ⟨f, hf, hfa⟩ := a.property
  apply Subtype.ext
  rw [adim9b_germPullback_rep g hg hg0 _ (f ∘ π)
    (adim9b_germPullback_rep π hπ hπ0 a f hfa).symm, ← hfa]
  apply Germ.coe_eq.mpr
  filter_upwards [hsection] with w hw
  exact congrArg f hw

theorem adim9b_germPullback_ker {n d : ℕ}
    (g : (Fin d → ℂ) → (Fin n → ℂ)) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (π : (Fin n → ℂ) → (Fin d → ℂ)) (hπ : ContinuousAt π 0) (hπ0 : π 0 = 0)
    (V : Set (Fin n → ℂ))
    (himage : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), g w ∈ V)
    (hretract : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ V → g (π z) = z) :
    RingHom.ker (adim9b_germPullback g hg hg0) = adim2_ideal n (adim2_germ n V 0) := by
  ext a
  obtain ⟨f, hf, hfa⟩ := a.property
  have hker : a ∈ RingHom.ker (adim9b_germPullback g hg hg0) ↔
      ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), f (g w) = 0 := by
    rw [RingHom.mem_ker, Subtype.ext_iff, adim9b_germPullback_rep g hg hg0 a f hfa]
    exact Germ.coe_eq
  have hideal : a ∈ adim2_ideal n (adim2_germ n V 0) ↔
      ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ V → f z = 0 := by
    change (adim2_germ n V 0 ≤ a.val.map (· = 0)) ↔ _
    rw [← hfa]
    change (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), 0 + z ∈ V → f z = 0) ↔ _
    simp only [zero_add]
  rw [hker, hideal]
  constructor
  · intro h
    filter_upwards [(show Tendsto π (𝓝 0) (𝓝 0) from hπ0 ▸ hπ).eventually h, hretract] with z hz hr hzV
    simpa only [hr hzV] using hz
  · intro h
    filter_upwards [(show Tendsto g (𝓝 0) (𝓝 0) from hg0 ▸ hg.continuousAt).eventually h, himage] with w hw hV
    exact hw hV

/-- The local coordinate ring of an analytic retract is its parameter germ ring. -/
def adim9b_retractGermEquiv {n d : ℕ}
    (g : (Fin d → ℂ) → (Fin n → ℂ)) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (π : (Fin n → ℂ) → (Fin d → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (V : Set (Fin n → ℂ))
    (hsection : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), π (g w) = w)
    (himage : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), g w ∈ V)
    (hretract : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ V → g (π z) = z) :
    (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n V 0)) ≃+* AnalyticGerm d :=
  (Ideal.quotEquivOfEq (adim9b_germPullback_ker g hg hg0 π hπ.continuousAt hπ0 V
    himage hretract).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (adim9b_germPullback_surjective g hg hg0 π hπ hπ0 hsection))

theorem adim9b_retractGerm_dimension {n d : ℕ}
    (g : (Fin d → ℂ) → (Fin n → ℂ)) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (π : (Fin n → ℂ) → (Fin d → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (V : Set (Fin n → ℂ))
    (hsection : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), π (g w) = w)
    (himage : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), g w ∈ V)
    (hretract : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ V → g (π z) = z) :
    ringKrullDim (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n V 0)) =
      (d : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv
    (adim9b_retractGermEquiv g hg hg0 π hπ hπ0 V hsection himage hretract)]
  exact adim6_parameter_dimension d

theorem adim9b_retractGerm_prime {n d : ℕ}
    (g : (Fin d → ℂ) → (Fin n → ℂ)) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (π : (Fin n → ℂ) → (Fin d → ℂ)) (hπ : ContinuousAt π 0) (hπ0 : π 0 = 0)
    (V : Set (Fin n → ℂ))
    (himage : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), g w ∈ V)
    (hretract : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ V → g (π z) = z) :
    (adim2_ideal n (adim2_germ n V 0)).IsPrime := by
  letI := spec_analyticGerm_ufd d
  letI : IsDomain (AnalyticGerm d) := {}
  rw [← adim9b_germPullback_ker g hg hg0 π hπ hπ0 V himage hretract]
  exact RingHom.ker_isPrime _

theorem adim9b_parameter_dimension_le_of_dimH {n d e : ℕ}
    (A : Set (Fin n → ℂ)) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (hdim : dimH A ≤ ((2 * e : ℕ) : ℝ≥0∞))
    (hinterior : (interior (π '' A)).Nonempty) : d ≤ e := by
  have h : ((2 * d : ℕ) : ℝ≥0∞) ≤ ((2 * e : ℕ) : ℝ≥0∞) := by
    calc
      ((2 * d : ℕ) : ℝ≥0∞) = dimH (π '' A) := by
        rw [Real.dimH_of_nonempty_interior hinterior, adim9b_finrank_real_pi]
      _ ≤ dimH A := π.lipschitzWith.dimH_image_le A
      _ ≤ _ := hdim
  have hnat : 2 * d ≤ 2 * e := by exact_mod_cast h
  omega

theorem adim9b_germ_ideal_ne_top (n : ℕ) (A : Set (Fin n → ℂ))
    (x : Fin n → ℂ) (hx : x ∈ A) : adim2_ideal n (adim2_germ n A x) ≠ ⊤ := by
  intro htop
  have h : (1 : AnalyticGerm n) ∈ adim2_ideal n (adim2_germ n A x) := by
    rw [htop]
    trivial
  change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ A → (1 : ℂ) = 0 at h
  exact one_ne_zero (h.self_of_nhds (by simpa only [add_zero] using hx))

theorem adim9b_componentDimensionParts_cover (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    C = ⋃ d ∈ Set.Icc 1 (n + 1), adim9_componentDimensionPart n C d := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes (adim9b_germ_ideal_ne_top (n + 1) C x hx)
    obtain ⟨d, hd1, hdn, hdim⟩ :=
      adim9_component_dimension_exists_aux n C hzero hclosed hscale hloc x hx P hP
    exact mem_iUnion₂.mpr ⟨d, ⟨hd1, hdn⟩, hx, P, hP, hdim⟩
  · intro hx
    obtain ⟨d, -, hd⟩ := mem_iUnion₂.mp hx
    exact hd.1

theorem adim9b_germPullback_leftInverse {n d : ℕ}
    (g : (Fin d → ℂ) → (Fin n → ℂ)) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (π : (Fin n → ℂ) → (Fin d → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (h : ∀ z, g (π z) = z) :
    Function.LeftInverse (adim9b_germPullback π hπ hπ0) (adim9b_germPullback g hg hg0) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := a.property
  apply Subtype.ext
  rw [adim9b_germPullback_rep π hπ hπ0 _ (f ∘ g)
    (adim9b_germPullback_rep g hg hg0 a f hfa).symm, ← hfa]
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun z ↦ congrArg f (h z)

/-- Linear changes of coordinates act contravariantly on analytic germs. -/
def adim9b_germLinearEquiv {n : ℕ} (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) :
    AnalyticGerm n ≃+* AnalyticGerm n :=
  RingEquiv.ofBijective (adim9b_germPullback L (L.analyticAt 0) (map_zero L))
    ⟨(adim9b_germPullback_leftInverse L (L.analyticAt 0) (map_zero L)
      L.symm (L.symm.analyticAt 0) (map_zero L.symm) L.apply_symm_apply).injective,
      adim9b_germPullback_surjective L (L.analyticAt 0) (map_zero L)
        L.symm (L.symm.analyticAt 0) (map_zero L.symm)
        (Eventually.of_forall L.symm_apply_apply)⟩

theorem adim9b_minimalPrime_comap_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I P : Ideal S) (hP : P ∈ I.minimalPrimes) :
    P.comap e ∈ (I.comap e).minimalPrimes := by
  letI : P.IsPrime := hP.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono hP.le⟩, ?_⟩
  intro Q hQ hQP
  letI : Q.IsPrime := hQ.1
  have hIQ : I ≤ Q.map e := by
    apply e.idealComapOrderIso.le_iff_le.mp
    simpa only [RingEquiv.idealComapOrderIso_apply,
      Ideal.comap_map_of_bijective _ e.bijective] using hQ.2
  have hPQ : P ≤ Q.map e :=
    hP.2 ⟨inferInstance, hIQ⟩ (Ideal.map_le_iff_le_comap.mpr hQP)
  simpa only [Ideal.comap_map_of_bijective _ e.bijective] using
    (Ideal.comap_mono (f := e) hPQ)

theorem adim9b_quotient_dimension_comap_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Ideal S) :
    ringKrullDim (R ⧸ P.comap e) = ringKrullDim (S ⧸ P) := by
  symm
  exact ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv P (P.comap e) e.symm (Ideal.map_comap_of_equiv e.symm).symm)

theorem adim9b_ideal_linear_change {n : ℕ}
    (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ))
    (A B : Set (Fin n → ℂ)) (hAB : ∀ z, L z ∈ B ↔ z ∈ A) (x : Fin n → ℂ) :
    adim2_ideal n (adim2_germ n B (L x)) =
      (adim2_ideal n (adim2_germ n A x)).comap (adim9b_germLinearEquiv L) := by
  ext a
  obtain ⟨f, hf, hfa⟩ := a.property
  have hrep : (adim9b_germLinearEquiv L a).val = Germ.ofFun (f ∘ L) :=
    adim9b_germPullback_rep L (L.analyticAt 0) (map_zero L) a f hfa
  change (adim2_germ n B (L x) ≤ a.val.map (· = 0)) ↔
    (adim2_germ n A x ≤ (adim9b_germLinearEquiv L a).val.map (· = 0))
  rw [← hfa, hrep]
  change (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), L x + z ∈ B → f z = 0) ↔
    (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ A → f (L z) = 0)
  constructor
  · intro h
    have ht : Tendsto L (𝓝 0) (𝓝 0) := by
      have ht := L.continuous.continuousAt (x := (0 : Fin n → ℂ))
      change Tendsto L (𝓝 0) (𝓝 (L 0)) at ht
      rw [map_zero] at ht
      exact ht
    filter_upwards [ht.eventually h] with z hz hzA
    exact hz (by rw [← map_add, hAB]; exact hzA)
  · intro h
    have ht : Tendsto L.symm (𝓝 0) (𝓝 0) := by
      have ht := L.symm.continuous.continuousAt (x := (0 : Fin n → ℂ))
      change Tendsto L.symm (𝓝 0) (𝓝 (L.symm 0)) at ht
      rw [map_zero] at ht
      exact ht
    filter_upwards [ht.eventually h] with z hz hzB
    have hzA : x + L.symm z ∈ A := by
      rw [← hAB, map_add, L.apply_symm_apply]
      exact hzB
    simpa only [L.apply_symm_apply] using hz hzA

theorem adim9b_componentDimensionPart_linear_change (n d : ℕ)
    (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ))
    (A B : Set (Fin (n + 1) → ℂ)) (hAB : ∀ z, L z ∈ B ↔ z ∈ A)
    (x : Fin (n + 1) → ℂ) (hx : x ∈ adim9_componentDimensionPart n A d) :
    L x ∈ adim9_componentDimensionPart n B d := by
  obtain ⟨hxA, P, hP, hdim⟩ := hx
  refine ⟨(hAB x).mpr hxA, P.comap (adim9b_germLinearEquiv L), ?_, ?_⟩
  · rw [adim9b_ideal_linear_change L A B hAB x]
    exact adim9b_minimalPrime_comap_equiv (adim9b_germLinearEquiv L) _ P hP
  · rw [adim9b_quotient_dimension_comap_equiv]
    exact hdim

theorem adim9b_componentDimensionPart_scale (n d : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (t : ℂ) (ht : t ≠ 0) (x : Fin (n + 1) → ℂ)
    (hx : x ∈ adim9_componentDimensionPart n C d) :
    t • x ∈ adim9_componentDimensionPart n C d := by
  let L := (LinearEquiv.smulOfNeZero ℂ (Fin (n + 1) → ℂ) t ht).toContinuousLinearEquiv
  have hL : ∀ z, L z ∈ C ↔ z ∈ C := by
    intro z
    change t • z ∈ C ↔ z ∈ C
    constructor
    · intro hz
      simpa only [inv_smul_smul₀ ht] using hscale t⁻¹ (inv_ne_zero ht) (t • z) hz
    · exact hscale t ht z
  exact adim9b_componentDimensionPart_linear_change n d L C C hL x hx

/-- A locally analytic set with an open projected piece in every neighbourhood
has at least the parameter dimension in every bounding quotient. -/
theorem adim9b_dimension_lower_of_open_projection (n d e : ℕ)
    (A : Set (Fin (n + 1) → ℂ)) (P : Ideal (AnalyticGerm (n + 1)))
    (hP : P ≤ adim2_ideal (n + 1) (adim2_germ (n + 1) A 0))
    (hdim : ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (e : WithBot ℕ∞))
    (hloc : ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
      ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ f ∈ s, f z = 0))
    (π : (Fin (n + 1) → ℂ) →L[ℂ] (Fin d → ℂ))
    (hopen : ∀ W ∈ 𝓝 (0 : Fin (n + 1) → ℂ), (interior (π '' (A ∩ W))).Nonempty) :
    d ≤ e := by
  have hbound : ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) ≤ (e : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hP.trans hQ.le))
      (Ideal.Quotient.factor_surjective (hP.trans hQ.le))
  obtain ⟨W, hW, hWdim⟩ := adim9b_local_dimH n e A hloc hbound
  exact adim9b_parameter_dimension_le_of_dimH (A ∩ W) π hWdim (hopen W hW)

/-- A finite parameter algebra has dimension bounded by its parameter germ ring. -/
theorem adim9b_dimension_le_of_finite_parameters (n d : ℕ)
    (P : Ideal (AnalyticGerm n))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite) :
    ringKrullDim (AnalyticGerm n ⧸ P) ≤ (d : WithBot ℕ∞) := by
  letI : Algebra (AnalyticGerm d) (AnalyticGerm n ⧸ P) := θ.toAlgebra
  letI : Algebra.IsIntegral (AnalyticGerm d) (AnalyticGerm n ⧸ P) :=
    ⟨hfinite.to_isIntegral⟩
  rw [← adim6_parameter_dimension d]
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap θ) fun I J hIJ ↦ by
    change Ideal.under (AnalyticGerm d) I.asIdeal < Ideal.under (AnalyticGerm d) J.asIdeal
    exact Ideal.IsIntegral.under_lt_under hIJ


/-- Coefficient and reconstruction facts for the primitive-root model. -/
private theorem adim9b_polynomial_roots_of_germ_dvd (d : ℕ)
    (p q : Polynomial ((Fin d → ℂ) → ℂ))
    (h : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) ∣
      p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)))) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ,
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        p.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 := by
  obtain ⟨S, hS⟩ := h
  have hsurj : Function.Surjective (Germ.coeRingHom (R := ℂ) (𝓝 (0 : Fin d → ℂ))) :=
    Quot.mk_surjective
  obtain ⟨s, hs⟩ := Polynomial.map_surjective _ hsurj S
  have heq : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      (q * s).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
    rw [Polynomial.map_mul, hs, hS]
  filter_upwards [adim9b_polynomial_representatives_eq d p (q * s) heq] with w hw
  intro t ht
  have := congrArg (fun a : Polynomial ℂ ↦ a.eval t) hw
  simpa only [Polynomial.eval_map, Polynomial.eval₂_mul, ht, zero_mul] using this

private theorem adim9b_polynomial_roots_of_relation (d : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q T : Polynomial (AnalyticGerm d))
    (hmin : ∀ S : Polynomial (AnalyticGerm d), S.eval₂ θ v = 0 ↔ Q ∣ S)
    (hT : T.eval₂ θ v = 0)
    (q p : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ,
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        p.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 := by
  apply adim9b_polynomial_roots_of_germ_dvd d p q
  have hqmap : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      Q.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hq i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hp i
  rw [hqmap, hpmap]
  obtain ⟨S, hS⟩ := (hmin T).mp hT
  exact ⟨S.map (analyticGermSubring d).subtype, by rw [hS, Polynomial.map_mul]⟩

private theorem adim9b_linear_relation {A B : Type*} [CommRing A] [CommRing B]
    (n : ℕ) (θ : A →+* B) (v : B) (δ : A) (c : Fin n → B)
    (R : Fin n → Polynomial A) (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin n → A) (S : Polynomial A)
    (hlinear : ∑ i, θ (a i) * c i = S.eval₂ θ v) :
    (∑ i, C (a i) * R i - C δ * S).eval₂ θ v = 0 := by
  rw [Polynomial.eval₂_sub, sub_eq_zero]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rw [← hlinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hcoord i]
  ring

private theorem adim9b_clear_monomial {A : Type*} [CommRing A]
    (n N : ℕ) (a δ : A) (x : Fin n → A) (e : Fin n → ℕ)
    (hN : ∑ i, e i ≤ N) :
    a * δ ^ (N - ∑ i, e i) * ∏ i, (δ * x i) ^ e i =
      δ ^ N * (a * ∏ i, x i ^ e i) := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  calc
    a * δ ^ (N - ∑ i, e i) * (δ ^ (∑ i, e i) * ∏ i, x i ^ e i) =
        a * (δ ^ (N - ∑ i, e i) * δ ^ (∑ i, e i)) * ∏ i, x i ^ e i := by ring
    _ = δ ^ N * (a * ∏ i, x i ^ e i) := by
      rw [← pow_add, Nat.sub_add_cancel hN]
      ring

private theorem adim9b_polynomial_equations_at_roots (n d k N : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (c : Fin n → B) (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin k → AnalyticGerm d) (e : Fin k → Fin n → ℕ)
    (hN : ∀ j, ∑ i, e j i ≤ N)
    (hF : ∑ j, θ (a j) * ∏ i, c i ^ e j i = 0)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (a₀ : Fin k → (Fin d → ℂ) → ℂ)
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ha : ∀ j, Germ.ofFun (a₀ j) = (a j).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∑ j, a₀ j w * ∏ i,
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) ^ e j i = 0 := by
  classical
  let T := ∑ j, C (a j * δ ^ (N - ∑ i, e j i)) * ∏ i, R i ^ e j i
  let p := ∑ j, C (a₀ j * Δ ^ (N - ∑ i, e j i)) * ∏ i, r i ^ e j i
  have hT : T.eval₂ θ v = 0 := by
    simp only [T, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, map_mul, map_pow]
    simp_rw [← hcoord, adim9b_clear_monomial n N _ _ _ _ (hN _)]
    rw [← Finset.mul_sum, hF, mul_zero]
  have hrmap (j : Fin n) : (r j).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      (R j).map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hr j i
  have ha' (j : Fin k) : Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)) (a₀ j) =
      (analyticGermSubring d).subtype (a j) := ha j
  have hΔ' : Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)) Δ =
      (analyticGermSubring d).subtype δ := hΔ
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    simp only [p, T, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_prod, Polynomial.map_pow, map_mul, map_pow, ha', hΔ', hrmap]
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  filter_upwards [adim9b_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have hz := hw t ht
  simp only [p, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Pi.evalRingHom_apply,
    Pi.mul_apply, Pi.pow_apply] at hz
  have hcoordw (i : Fin n) : Δ w *
      ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t :=
    mul_div_cancel₀ _ hΔw
  have hclear (j : Fin k) : a₀ j w * Δ w ^ (N - ∑ i, e j i) *
      ∏ i, (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t ^ e j i =
      Δ w ^ N * (a₀ j w * ∏ i,
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) ^ e j i) := by
    simpa only [hcoordw] using adim9b_clear_monomial n N (a₀ j w) (Δ w)
      (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w)
      (e j) (hN j)
  simp_rw [hclear] at hz
  rw [← Finset.mul_sum] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hΔw)

private theorem adim9b_linear_reconstruction (n d : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (c : Fin n → B) (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin n → AnalyticGerm d) (S : Polynomial (AnalyticGerm d))
    (hlinear : ∑ i, θ (a i) * c i = S.eval₂ θ v)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (a₀ : Fin n → (Fin d → ℂ) → ℂ) (s : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ha : ∀ i, Germ.ofFun (a₀ i) = (a i).val)
    (hs : ∀ i, Germ.ofFun (s.coeff i) = (S.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∑ i, a₀ i w *
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
          s.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t := by
  classical
  let T := ∑ i, C (a i) * R i - C δ * S
  let p := ∑ i, C (a₀ i) * r i - C Δ * s
  have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (G : Polynomial (AnalyticGerm d))
      (hFG : ∀ i, Germ.ofFun (F.coeff i) = (G.coeff i).val) :
      F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        G.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hFG i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    simp only [p, T, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Germ.coe_coeRingHom, Subring.subtype_apply, hΔ, ha,
      hmap s S hs, hmap _ _ (hr _)]
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  have hT := adim9b_linear_relation n θ v δ c R hcoord a S hlinear
  filter_upwards [adim9b_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have heq := hw t ht
  simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Pi.evalRingHom_apply, sub_eq_zero] at heq
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, heq, mul_div_cancel_left₀ _ hΔw]

private theorem adim9b_linear_germ_identity (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (L : (Fin n → ℂ) →L[ℂ] ℂ) (b : AnalyticGerm n)
    (hb : b.val = Germ.ofFun (fun z ↦ L z))
    (a : Fin n → AnalyticGerm d)
    (ha : ∀ i, Germ.ofFun (fun _ : Fin d → ℂ ↦ L (Pi.single i 1)) = (a i).val) :
    ∑ i, θ (a i) * Ideal.Quotient.mk P (c i) = Ideal.Quotient.mk P b := by
  classical
  let a' : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun _ ↦ L (Pi.single i 1)), _, analyticAt_const, rfl⟩
  have hθ (i : Fin n) : θ (a i) = Ideal.Quotient.mk P (a' i) :=
    hcomp (a i) (fun _ ↦ L (Pi.single i 1)) analyticAt_const (ha i) (a' i) rfl
  simp_rw [hθ, ← map_mul, ← map_sum]
  congr 1
  apply Subtype.ext
  change (analyticGermSubring n).subtype (∑ i, a' i * c i) = b.val
  rw [map_sum, hb]
  simp only [map_mul, Subring.subtype_apply, hc]
  change (∑ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun _ ↦ L (Pi.single i 1)) *
    Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ z i)) =
      Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ L z)
  simp only [← map_mul, ← map_sum]
  congr 1
  funext z
  simp only [Finset.sum_apply, Pi.mul_apply]
  conv_rhs => rw [pi_eq_sum_univ' z]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

private theorem adim9b_linear_form_reconstruction (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (L : (Fin n → ℂ) →L[ℂ] ℂ) (b : AnalyticGerm n)
    (hb : b.val = Germ.ofFun (fun z ↦ L z))
    (S : Polynomial (AnalyticGerm d)) (s : Polynomial ((Fin d → ℂ) → ℂ))
    (hS : S.eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b)
    (hs : ∀ i, Germ.ofFun (s.coeff i) = (S.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      L (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
        s.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t := by
  classical
  let a : Fin n → AnalyticGerm d := fun i ↦
    ⟨Germ.ofFun (fun _ ↦ L (Pi.single i 1)), _, analyticAt_const, rfl⟩
  have hlinear : ∑ i, θ (a i) * Ideal.Quotient.mk P (c i) =
      S.eval₂ θ (Ideal.Quotient.mk P v) := by
    rw [hS]
    exact adim9b_linear_germ_identity n d P π θ hcomp c hc L b hb a (fun _ ↦ rfl)
  filter_upwards [adim9b_linear_reconstruction n d θ (Ideal.Quotient.mk P v) Q δ
    (fun i ↦ Ideal.Quotient.mk P (c i)) R hmin hcoord a S hlinear q Δ r
    (fun i _ ↦ L (Pi.single i 1)) s hq hΔ hr (fun _ ↦ rfl) hs] with w hw
  intro t hΔw ht
  rw [← hw t hΔw ht]
  conv_lhs => rw [pi_eq_sum_univ'
    (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w)]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

theorem adim9b_reconstructed_projection_and_primitive (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z)) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin n → ℂ := fun i ↦
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
      π z = w ∧ ℓ z = t := by
  classical
  have hX : ∀ i : ℕ,
      Germ.ofFun ((X : Polynomial ((Fin d → ℂ) → ℂ)).coeff i) =
        ((X : Polynomial (AnalyticGerm d)).coeff i).val := by
    intro i
    simp only [Polynomial.coeff_X]
    split_ifs <;> rfl
  have hℓ := adim9b_linear_form_reconstruction n d P π θ hcomp c hc v Q δ R
    hmin hcoord q Δ r hq hΔ hr ℓ v hv X X (by simp only [Polynomial.eval₂_X]) hX
  have hπ (k : Fin d) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      (π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t /
        Δ w)) k = w k := by
    let L := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).comp π
    let b : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ L z), _, L.analyticAt 0, rfl⟩
    let a : AnalyticGerm d := ⟨Germ.ofFun (fun w ↦ w k), _,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).analyticAt 0, rfl⟩
    have hS : (C a).eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b := by
      rw [Polynomial.eval₂_C]
      exact hcomp a (fun w ↦ w k)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).analyticAt 0)
          (by rfl) b rfl
    have hs : ∀ i, Germ.ofFun ((C (fun w : Fin d → ℂ ↦ w k)).coeff i) =
        ((C a).coeff i).val := by
      intro i
      simp only [Polynomial.coeff_C]
      split_ifs <;> rfl
    simpa only [Polynomial.eval₂_C, Pi.evalRingHom_apply, L,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      adim9b_linear_form_reconstruction n d P π θ hcomp c hc v Q δ R hmin hcoord
        q Δ r hq hΔ hr L b rfl (C a) (C (fun w ↦ w k)) hS hs
  have hπall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ k : Fin d, ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      (π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t /
        Δ w)) k = w k := by
    rw [Filter.eventually_all]
    exact hπ
  filter_upwards [hℓ, hπall] with w hwℓ hwπ
  intro t hΔw ht
  refine ⟨funext (fun k ↦ hwπ k t hΔw ht), ?_⟩
  simpa only [Polynomial.eval₂_X] using hwℓ t hΔw ht

private theorem adim9b_monic_representative (d : ℕ) (Q : Polynomial (AnalyticGerm d))
    (hQ : Q.Monic) :
    ∃ q : Polynomial ((Fin d → ℂ) → ℂ), q.Monic ∧
      ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧ Germ.ofFun (q.coeff i) = (Q.coeff i).val := by
  classical
  let k := Q.natDegree
  choose a ha hrep using fun i : Fin k ↦ (Q.coeff i).property
  let q : Polynomial ((Fin d → ℂ) → ℂ) := X ^ k + ∑ i : Fin k, C (a i) * X ^ (i : ℕ)
  have hmonic : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt a)
  have hform : Q = X ^ k + ∑ i : Fin k, C (Q.coeff i) * X ^ (i : ℕ) := by
    simpa only [← Fin.sum_univ_eq_sum_range] using hQ.as_sum
  have hcoeff (i : ℕ) : q.coeff i =
      (if i = k then 1 else 0) + ∑ j : Fin k, if (j : ℕ) = i then a j else 0 := by
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, eq_comm]
  have hmap : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      Q.map (analyticGermSubring d).subtype := by
    conv_rhs => rw [hform]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Germ.coe_coeRingHom, Subring.subtype_apply, hrep]
  refine ⟨q, hmonic, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [hcoeff]
    apply AnalyticAt.add
    · split_ifs <;> exact analyticAt_const
    · apply Finset.analyticAt_sum
      intro j _
      split_ifs <;> first | exact ha j | exact analyticAt_const
  · simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hmap

private theorem adim9b_coordinate_relation (d : ℕ) {B : Type*} [CommRing B]
    (θ : AnalyticGerm d →+* B) (v x : B)
    (Q W R : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : θ δ * x = R.eval₂ θ v) (hW : W.Monic) (hWx : W.eval₂ θ x = 0)
    (q u r : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hu : ∀ i, Germ.ofFun (u.coeff i) = (W.coeff i).val) (humonic : u.Monic)
    (hr : ∀ i, Germ.ofFun (r.coeff i) = (R.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
        (r.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) = 0 := by
  let T := (W.scaleRoots δ).comp R
  let p := (u.scaleRoots Δ).comp r
  have hT : T.eval₂ θ v = 0 := by
    rw [Polynomial.eval₂_comp, ← hcoord]
    exact Polynomial.scaleRoots_eval₂_eq_zero θ hWx
  have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (G : Polynomial (AnalyticGerm d))
      (hFG : ∀ i, Germ.ofFun (F.coeff i) = (G.coeff i).val) :
      F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        G.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hFG i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    rw [Polynomial.map_comp, Polynomial.map_comp,
      Polynomial.map_scaleRoots u Δ _ (by rw [humonic.leadingCoeff, map_one]; exact one_ne_zero),
      Polynomial.map_scaleRoots W δ _ (by rw [hW.leadingCoeff, map_one]; exact one_ne_zero),
      hmap u W hu, hmap r R hr]
    congr 2
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  filter_upwards [adim9b_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have hz := hw t ht
  rw [Polynomial.eval₂_comp] at hz
  have heq := Polynomial.scaleRoots_eval₂_mul (p := u)
    (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
    (r.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) Δ
  simp only [Pi.evalRingHom_apply, mul_div_cancel₀ _ hΔw] at heq
  rw [hz] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hΔw)

private theorem adim9b_coordinate_weierstrass (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    ∀ i, ∃ W : Polynomial (AnalyticGerm d), IsWeierstrassPolynomial W ∧
      W.eval₂ θ (Ideal.Quotient.mk P (c i)) = 0 := by
  have hlocal : ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b := by
    intro a b hab
    obtain ⟨fa, hfa, hfarep⟩ := a.property
    let b' : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ fa (π z)), _,
      hfa.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
    have hab' : θ a = Ideal.Quotient.mk P b' := hcomp a fa hfa hfarep b' rfl
    have hdiff : b - b' ∈ P :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem b b').mp (hab.symm.trans hab')
    have hzero : analyticGermValue n (b - b') = 0 := by
      by_contra hne
      exact hP (P.eq_top_of_isUnit_mem hdiff ((analyticGerm_isUnit_iff _).mpr hne))
    have hval : analyticGermValue n b = analyticGermValue n b' := by
      simpa only [map_sub, sub_eq_zero] using hzero
    rw [hval]
    change a.val.value = b'.val.value
    rw [← hfarep]
    change (Germ.ofFun fa).value = (Germ.ofFun (fun z ↦ fa (π z))).value
    simp only [Germ.value_ofFun, map_zero]
  intro i
  apply adim5_distinguished_relation n d P hP θ hfinite hlocal (c i)
  change (c i).val.value = 0
  rw [hc i]
  rfl

private theorem adim9b_weierstrass_representative (d : ℕ)
    (Q : Polynomial (AnalyticGerm d)) (q : Polynomial ((Fin d → ℂ) → ℂ))
    (hQ : IsWeierstrassPolynomial Q)
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val) :
    ∃ (k : ℕ) (a : Fin k → (Fin d → ℂ) → ℂ),
      0 < k ∧ (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t =
          AnalyticDivisorAlgebraic4.monicInLast a (w, t) := by
  classical
  let k := Q.natDegree
  let a : Fin k → (Fin d → ℂ) → ℂ := fun i ↦ q.coeff i
  have hk : 0 < k := hQ.2.1
  have ha : ∀ i, AnalyticAt ℂ (a i) 0 := fun i ↦ (hq i).1
  have ha0 : ∀ i, a i 0 = 0 := by
    intro i
    have hi := hQ.2.2 i i.isLt
    change (Q.coeff i).val.value = 0 at hi
    rw [← (hq i).2] at hi
    simpa [a] using hi
  have hlead : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), q.coeff k w = 1 := by
    apply Filter.Germ.coe_eq.mp
    rw [(hq k).2]
    have hcoeff : Q.coeff k = 1 := hQ.1.coeff_natDegree
    rw [hcoeff]
    rfl
  have hkq : k ≤ q.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hw := hlead.self_of_nhds
    rw [hz] at hw
    norm_num at hw
  have hhigh : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ j ∈ Finset.Ioc k q.natDegree, q.coeff j w = 0 := by
    rw [Finset.eventually_all]
    intro j hj
    apply Filter.Germ.coe_eq.mp
    rw [(hq j).2, Polynomial.coeff_eq_zero_of_natDegree_lt (Finset.mem_Ioc.mp hj).1]
    rfl
  refine ⟨k, a, hk, ha, ha0, ?_⟩
  filter_upwards [hlead, hhigh] with w hwlead hwhigh
  intro t
  rw [Polynomial.eval₂_eq_sum_range]
  simp only [Pi.evalRingHom_apply]
  rw [show ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i w * t ^ i =
      t ^ k + ∑ i : Fin k, q.coeff i w * t ^ (i : ℕ) by
    calc
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i w * t ^ i =
          ∑ i ∈ Finset.range (k + 1), q.coeff i w * t ^ i := by
            symm
            apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkq))
            intro j hjbig hjsmall
            rw [hwhigh j]
            · simp
            · simp only [Finset.mem_Ioc]
              simp only [Finset.mem_range, not_lt] at hjsmall
              simp only [Finset.mem_range, Nat.lt_succ_iff] at hjbig
              omega
      _ = (∑ i ∈ Finset.range k, q.coeff i w * t ^ i) +
          q.coeff k w * t ^ k := by rw [Finset.sum_range_succ]
      _ = t ^ k + ∑ i : Fin k, q.coeff i w * t ^ (i : ℕ) := by
          rw [hwlead, one_mul, add_comm, ← Fin.sum_univ_eq_sum_range]]
  rfl

theorem adim9b_reconstructed_coordinates_small (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∀ i, ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w‖ < ε := by
  classical
  have hsmall (i : Fin n) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w‖ < ε := by
    obtain ⟨W, hW, hWx⟩ := adim9b_coordinate_weierstrass n d P hP π θ hfinite hcomp c hc i
    obtain ⟨u, humonic, hu⟩ := adim9b_monic_representative d W hW.1
    obtain ⟨k, a, _, ha, ha0, hform⟩ := adim9b_weierstrass_representative d W u hW hu
    have hbound := AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small
      (fun j ↦ (ha j).continuousAt) ha0 hε
    have hrelation := adim9b_coordinate_relation d θ (Ideal.Quotient.mk P v)
      (Ideal.Quotient.mk P (c i)) Q W (R i) δ hmin (hcoord i) hW.1 hWx
      q u (r i) Δ hq (fun j ↦ (hu j).2) humonic (hr i) hΔ
    filter_upwards [hform, hbound, hrelation] with w hwform hwbound hwrelation
    intro t hΔw ht
    apply hwbound
    rw [← hwform]
    exact hwrelation t hΔw ht
  have hall := Filter.eventually_all.mpr hsmall
  filter_upwards [hall] with w hw
  exact fun t hΔw ht i ↦ hw i t hΔw ht

private theorem adim9b_division_with_parameters
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : E × ℂ → ℂ} {k : ℕ} {a : Fin k → E → ℂ}
    (hg : AnalyticAt ℂ g 0) (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) :
    ∃ q : E × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∃ b : Fin k → E → ℂ, (∀ j, AnalyticAt ℂ (b j) 0) ∧
        g =ᶠ[𝓝 0] fun p ↦ q p * (p.2 ^ k + ∑ j, a j p.1 * p.2 ^ (j : ℕ)) +
          ∑ j, b j p.1 * p.2 ^ (j : ℕ) := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let e' := e.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  obtain ⟨q, hq, b, hb, heq⟩ := AnalyticDivisorAlgebraic4.spec_weierstrass_division
    (hg.comp_of_eq (e'.symm.analyticAt 0) (map_zero _))
    (fun j ↦ (ha j).comp_of_eq (e.symm.analyticAt 0) (map_zero _))
    (fun j ↦ by simpa using ha0 j)
  refine ⟨fun p ↦ q (e' p), hq.comp_of_eq (e'.analyticAt 0) (map_zero _),
    fun j x ↦ b j (e x),
    fun j ↦ (hb j).comp_of_eq (e.analyticAt 0) (map_zero _), ?_⟩
  have ht : Tendsto e' (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using e'.continuous.continuousAt (x := 0)
  filter_upwards [ht.eventually heq] with p hp
  simpa [e', AnalyticDivisorAlgebraic4.monicInLast] using hp

private def adim9b_split_fibre {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (n : ℕ) :
    (E × (Fin (n + 1) → ℂ)) ≃L[ℂ] ((E × (Fin n → ℂ)) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ ((p.1, Fin.tail p.2), p.2 0)
      invFun := fun p ↦ (p.1.1, Fin.cons p.2 p.1.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem adim9b_simultaneous_division
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (k : Fin n → ℕ) (a : (i : Fin n) → Fin (k i) → E → ℂ)
    (ha : ∀ i j, AnalyticAt ℂ (a i j) 0) (ha0 : ∀ i j, a i j 0 = 0)
    (f : E × (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ (q : Fin n → E × (Fin n → ℂ) → ℂ)
      (b : ((i : Fin n) → Fin (k i)) → E → ℂ),
      (∀ i, AnalyticAt ℂ (q i) 0) ∧ (∀ e, AnalyticAt ℂ (b e) 0) ∧
      f =ᶠ[𝓝 0] fun p ↦
        (∑ i, q i p * (p.2 i ^ k i + ∑ j, a i j p.1 * p.2 i ^ (j : ℕ))) +
        ∑ e, b e p.1 * ∏ i, p.2 i ^ (e i : ℕ) := by
  classical
  induction n with
  | zero =>
      refine ⟨Fin.elim0, fun _ x ↦ f (x, 0), (fun i ↦ Fin.elim0 i), ?_, ?_⟩
      · intro e
        exact hf.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
      · exact Filter.Eventually.of_forall fun p ↦ by
          simp only [Fin.sum_univ_zero, Fin.prod_univ_zero, mul_one, zero_add]
          rw [Fintype.sum_unique]
          congr 1
          exact Prod.ext rfl (Subsingleton.elim _ _)
  | succ n ih =>
      let L := adim9b_split_fibre (E := E) n
      obtain ⟨q₀, hq₀, b₀, hb₀, hdiv⟩ := adim9b_division_with_parameters
        (g := fun p ↦ f (L.symm p)) (a := fun j p ↦ a 0 j p.1)
        (hf.comp_of_eq (L.symm.analyticAt 0) (map_zero _))
        (fun j ↦ (ha 0 j).comp_of_eq analyticAt_fst rfl)
        (fun j ↦ ha0 0 j)
      have hrec (j : Fin (k 0)) := ih (fun i ↦ k i.succ) (fun i ↦ a i.succ)
        (fun i ↦ ha i.succ) (fun i ↦ ha0 i.succ) (b₀ j) (hb₀ j)
      choose q b hq hb heq using hrec
      let tailMap : (E × (Fin (n + 1) → ℂ)) →L[ℂ] E × (Fin n → ℂ) :=
        (ContinuousLinearMap.fst ℂ (E × (Fin n → ℂ)) ℂ).comp L.toContinuousLinearMap
      let q' : Fin (n + 1) → E × (Fin (n + 1) → ℂ) → ℂ :=
        Fin.cons (fun p ↦ q₀ (L p))
          (fun i p ↦ ∑ j, q j i (tailMap p) * p.2 0 ^ (j : ℕ))
      let b' : ((i : Fin (n + 1)) → Fin (k i)) → E → ℂ :=
        fun e ↦ b (e 0) (fun i ↦ e i.succ)
      refine ⟨q', b', ?_, fun e ↦ hb _ _, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · exact hq₀.comp_of_eq (L.analyticAt 0) (map_zero _)
        · change AnalyticAt ℂ (fun p ↦ ∑ j, q j i (tailMap p) * p.2 0 ^ (j : ℕ)) 0
          apply Finset.analyticAt_fun_sum
          intro j _
          apply AnalyticAt.mul
          · exact (hq j i).comp_of_eq (tailMap.analyticAt 0) (map_zero _)
          · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
              0).analyticAt 0 |>.comp_of_eq analyticAt_snd rfl).pow _
      · have hL : Tendsto L (𝓝 0) (𝓝 0) := by
          simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := 0)
        have htail : Tendsto tailMap (𝓝 0) (𝓝 0) := by
          simpa only [ContinuousAt, map_zero] using tailMap.continuous.continuousAt (x := 0)
        filter_upwards [hL.eventually hdiv,
          htail.eventually (Filter.eventually_all.mpr heq)] with p hp hr
        rw [L.symm_apply_apply] at hp
        rw [hp]
        change q₀ (L p) * _ + (∑ j, b₀ j (tailMap p) * p.2 0 ^ (j : ℕ)) = _
        simp_rw [hr]
        rw [Fin.sum_univ_succ]
        simp only [q', Fin.cons_zero, Fin.cons_succ]
        have hrem :
            (∑ j : Fin (k 0), (∑ e : (i : Fin n) → Fin (k i.succ),
              b j e p.1 * ∏ i, p.2 i.succ ^ (e i : ℕ)) * p.2 0 ^ (j : ℕ)) =
            ∑ e : (i : Fin (n + 1)) → Fin (k i),
              b' e p.1 * ∏ i, p.2 i ^ (e i : ℕ) := by
          rw [← Equiv.sum_comp (Fin.consEquiv (fun i ↦ Fin (k i)))]
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e _
          simp only [b', Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ,
            Fin.prod_univ_succ]
          ring
        have hcor :
            (∑ j : Fin (k 0), (∑ i : Fin n, q j i (tailMap p) *
              (p.2 i.succ ^ k i.succ + ∑ l, a i.succ l p.1 * p.2 i.succ ^ (l : ℕ))) *
              p.2 0 ^ (j : ℕ)) =
            ∑ i : Fin n, (∑ j : Fin (k 0), q j i (tailMap p) * p.2 0 ^ (j : ℕ)) *
              (p.2 i.succ ^ k i.succ + ∑ l, a i.succ l p.1 * p.2 i.succ ^ (l : ℕ)) := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        simp only [add_mul, Finset.sum_add_distrib]
        change q₀ (L p) * _ +
          ((∑ j : Fin (k 0), (∑ i : Fin n, q j i (tailMap p) *
            (p.2 i.succ ^ k i.succ + ∑ l, a i.succ l p.1 * p.2 i.succ ^ (l : ℕ))) *
            p.2 0 ^ (j : ℕ)) + _) = _
        simp only [show (tailMap p).1 = p.1 from rfl,
          show (tailMap p).2 = Fin.tail p.2 from rfl, Fin.tail]
        rw [hcor, hrem]
        simp only [show (L p).2 = p.2 0 from rfl,
          show (L p).1.1 = p.1 from rfl, add_assoc]

private theorem adim9b_polynomial_simultaneous_division (n d : ℕ)
    (W : Fin n → Polynomial (AnalyticGerm d))
    (u : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hW : ∀ i, IsWeierstrassPolynomial (W i))
    (hu : ∀ i j, AnalyticAt ℂ ((u i).coeff j) 0 ∧
      Germ.ofFun ((u i).coeff j) = ((W i).coeff j).val)
    (f : (Fin d → ℂ) × (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ (k : Fin n → ℕ) (q : Fin n → (Fin d → ℂ) × (Fin n → ℂ) → ℂ)
      (b : ((i : Fin n) → Fin (k i)) → (Fin d → ℂ) → ℂ),
      (∀ i, 0 < k i) ∧ (∀ i, AnalyticAt ℂ (q i) 0) ∧
      (∀ e, AnalyticAt ℂ (b e) 0) ∧
      f =ᶠ[𝓝 0] fun p ↦
        (∑ i, q i p * (u i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) p.1) (p.2 i)) +
        ∑ e, b e p.1 * ∏ i, p.2 i ^ (e i : ℕ) := by
  classical
  have hform (i : Fin n) := adim9b_weierstrass_representative d (W i) (u i) (hW i) (hu i)
  choose k a hk ha ha0 heq using hform
  obtain ⟨q, b, hq, hb, hdiv⟩ := adim9b_simultaneous_division n k a ha ha0 f hf
  refine ⟨k, q, b, hk, hq, hb, ?_⟩
  have ht : Tendsto (Prod.fst : (Fin d → ℂ) × (Fin n → ℂ) → (Fin d → ℂ))
      (𝓝 0) (𝓝 0) := continuous_fst.continuousAt
  filter_upwards [hdiv, ht.eventually (Filter.eventually_all.mpr heq)] with p hp he
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [he i]
  rfl

private def adim9b_parameter_pullback {n d : ℕ}
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) : AnalyticGerm d →+* AnalyticGerm n := by
  have ht : Tendsto π (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using π.continuous.continuousAt (x := 0)
  let t : Germ (𝓝 (0 : Fin d → ℂ)) ℂ →+* Germ (𝓝 (0 : Fin n → ℂ)) ℂ :=
    { toFun := fun g ↦ g.compTendsto π ht
      map_one' := rfl
      map_zero' := rfl
      map_mul' := fun g h ↦ Germ.inductionOn g fun _ ↦ Germ.inductionOn h fun _ ↦ rfl
      map_add' := fun g h ↦ Germ.inductionOn g fun _ ↦ Germ.inductionOn h fun _ ↦ rfl }
  refine
    { toFun := fun a ↦ ⟨t a.val, ?_⟩
      map_one' := Subtype.ext t.map_one
      map_zero' := Subtype.ext t.map_zero
      map_mul' := fun a b ↦ Subtype.ext (t.map_mul a.val b.val)
      map_add' := fun a b ↦ Subtype.ext (t.map_add a.val b.val) }
  obtain ⟨f, hf, hrep⟩ := a.property
  refine ⟨fun z ↦ f (π z), hf.comp_of_eq (π.analyticAt 0) (map_zero _), ?_⟩
  change _ = a.val.compTendsto π ht
  rw [← hrep]
  rfl

private theorem adim9b_parameter_pullback_rep {n d : ℕ}
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ) (hrep : Germ.ofFun f = a.val) :
    Germ.ofFun (fun z ↦ f (π z)) = (adim9b_parameter_pullback π a).val := by
  change _ = a.val.compTendsto π (by
    simpa only [ContinuousAt, map_zero] using π.continuous.continuousAt (x := 0))
  rw [← hrep]
  rfl

private theorem adim9b_parameter_pullback_quotient {n d : ℕ} (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    (Ideal.Quotient.mk P).comp (adim9b_parameter_pullback π) = θ := by
  ext a
  obtain ⟨f, hf, hrep⟩ := a.property
  exact (hcomp a f hf hrep _ (adim9b_parameter_pullback_rep π a f hrep)).symm

private theorem adim9b_polynomial_eval_germ (n : ℕ)
    (p : Polynomial ((Fin n → ℂ) → ℂ)) (x : (Fin n → ℂ) → ℂ) :
    Germ.ofFun (fun z ↦ p.eval₂ (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) z) (x z)) =
      (p.map (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)))).eval (Germ.ofFun x) := by
  have heq : (fun z ↦ p.eval₂ (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) z) (x z)) =
      p.eval x := by
    funext z
    exact Polynomial.eval₂_at_apply _ _
  rw [heq, Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) x).symm

private theorem adim9b_coordinate_polynomial_rep (n d : ℕ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (W : Polynomial (AnalyticGerm d)) (u : Polynomial ((Fin d → ℂ) → ℂ))
    (hu : ∀ j, Germ.ofFun (u.coeff j) = (W.coeff j).val)
    (i : Fin n) (c : AnalyticGerm n)
    (hc : c.val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    Germ.ofFun (fun z ↦ u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i)) =
      (W.eval₂ (adim9b_parameter_pullback π) c).val := by
  let τ : ((Fin d → ℂ) → ℂ) →+* ((Fin n → ℂ) → ℂ) :=
    RingHom.pi (fun z ↦ Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z))
  have hm : (u.map τ).map (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) =
      W.map ((analyticGermSubring n).subtype.comp (adim9b_parameter_pullback π)) := by
    ext j
    simp only [Polynomial.coeff_map, RingHom.comp_apply]
    exact adim9b_parameter_pullback_rep π (W.coeff j) (u.coeff j) (hu j)
  have heq := adim9b_polynomial_eval_germ n (u.map τ) (fun z ↦ z i)
  rw [hm, ← hc] at heq
  have hl : (fun z ↦ (u.map τ).eval₂
      (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) z) (z i)) =
      (fun z ↦ u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i)) := by
    funext z
    rw [Polynomial.eval₂_map]
    rfl
  rw [hl] at heq
  rw [Polynomial.eval_map] at heq
  exact heq.trans (Polynomial.hom_eval₂ W (adim9b_parameter_pullback π)
    (analyticGermSubring n).subtype c).symm

private theorem adim9b_division_remainder_in_quotient (n d : ℕ)
    {ι : Type*} [Fintype ι] (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : (Ideal.Quotient.mk P).comp (adim9b_parameter_pullback π) = θ)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (W : Fin n → Polynomial (AnalyticGerm d))
    (u : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hu : ∀ i j, Germ.ofFun ((u i).coeff j) = ((W i).coeff j).val)
    (hW : ∀ i, (W i).eval₂ θ (Ideal.Quotient.mk P (c i)) = 0)
    (g : AnalyticGerm n) (hg : g ∈ P) (f : (Fin n → ℂ) → ℂ)
    (hf : Germ.ofFun f = g.val)
    (q : Fin n → (Fin n → ℂ) → ℂ) (hq : ∀ i, AnalyticAt ℂ (q i) 0)
    (B : ι → AnalyticGerm d) (b : ι → (Fin d → ℂ) → ℂ)
    (hb : ∀ j, Germ.ofFun (b j) = (B j).val) (e : ι → Fin n → ℕ)
    (hid : f =ᶠ[𝓝 0] fun z ↦
      (∑ i, q i z * (u i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i)) +
      ∑ j, b j (π z) * ∏ i, z i ^ e j i) :
    ∑ j, θ (B j) * ∏ i, Ideal.Quotient.mk P (c i) ^ e j i = 0 := by
  classical
  let qg : Fin n → AnalyticGerm n := fun i ↦ ⟨Germ.ofFun (q i), q i, hq i, rfl⟩
  have heq : g = (∑ i, qg i * (W i).eval₂ (adim9b_parameter_pullback π) (c i)) +
      ∑ j, adim9b_parameter_pullback π (B j) * ∏ i, c i ^ e j i := by
    apply Subtype.ext
    change g.val = (analyticGermSubring n).subtype
      ((∑ i, qg i * (W i).eval₂ (adim9b_parameter_pullback π) (c i)) +
        ∑ j, adim9b_parameter_pullback π (B j) * ∏ i, c i ^ e j i)
    rw [map_add, map_sum, map_sum]
    simp only [map_mul, map_prod, map_pow, Subring.subtype_apply]
    simp_rw [← hf, ← adim9b_coordinate_polynomial_rep n d π _ _ (hu _) _ _ (hc _),
      ← adim9b_parameter_pullback_rep π _ _ (hb _), hc]
    change Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) f =
      (∑ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (q i) *
        Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))
          (fun z ↦ (u i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i))) +
      ∑ j, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ b j (π z)) *
        ∏ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ z i) ^ e j i
    simp only [← map_pow, ← map_prod, ← map_mul, ← map_sum, ← map_add]
    apply Germ.coe_eq.mpr
    filter_upwards [hid] with z hz
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply] using hz
  have hmap := congrArg (Ideal.Quotient.mk P) heq
  simp only [map_add, map_sum, map_mul, map_prod, map_pow] at hmap
  simp_rw [Polynomial.hom_eval₂, hcomp, hW, mul_zero] at hmap
  have hB (j : ι) : Ideal.Quotient.mk P (adim9b_parameter_pullback π (B j)) = θ (B j) :=
    RingHom.congr_fun hcomp (B j)
  simpa only [hB, Finset.sum_const_zero, zero_add,
    Ideal.Quotient.eq_zero_iff_mem.mpr hg] using hmap.symm

theorem adim9b_analytic_equation_at_roots (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (g : AnalyticGerm n) (hg : g ∈ P) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hfrep : Germ.ofFun f = g.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      f (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) = 0 := by
  classical
  choose W hW hWzero using adim9b_coordinate_weierstrass n d P hP π θ hfinite hcomp c hc
  have hurep (i : Fin n) := adim9b_monic_representative d (W i) (hW i).1
  choose u humonic hu using hurep
  obtain ⟨k, a, b, _, ha, hb, hdiv⟩ := adim9b_polynomial_simultaneous_division n d W u hW hu
    (fun p ↦ f p.2) (hf.comp_of_eq analyticAt_snd rfl)
  let B : ((i : Fin n) → Fin (k i)) → AnalyticGerm d :=
    fun e ↦ ⟨Germ.ofFun (b e), b e, hb e, rfl⟩
  have hgraph : Tendsto (fun z ↦ (π z, z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 0) := by
    let L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ) × (Fin n → ℂ) :=
      π.prod (ContinuousLinearMap.id ℂ (Fin n → ℂ))
    have ht : Tendsto L (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := 0)
    exact ht
  have hF := adim9b_division_remainder_in_quotient n d P π θ
    (adim9b_parameter_pullback_quotient P π θ hcomp) c hc W u (fun i j ↦ (hu i j).2)
    hWzero g hg f hfrep (fun i z ↦ a i (π z, z))
    (fun i ↦ (ha i).comp_of_eq ((π.analyticAt 0).prod analyticAt_id) (by simp))
    B b (fun _ ↦ rfl) (fun e i ↦ (e i : ℕ)) (hgraph.eventually hdiv)
  let J := Fintype.equivFin ((i : Fin n) → Fin (k i))
  let N := ∑ j : Fin (Fintype.card ((i : Fin n) → Fin (k i))), ∑ i, (J.symm j i : ℕ)
  have hN (j : Fin (Fintype.card ((i : Fin n) → Fin (k i)))) :
      ∑ i, (J.symm j i : ℕ) ≤ N := Finset.single_le_sum (f := fun j ↦ ∑ i, (J.symm j i : ℕ))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hF' : ∑ j, θ (B (J.symm j)) * ∏ i, Ideal.Quotient.mk P (c i) ^ (J.symm j i : ℕ) = 0 :=
    (Equiv.sum_comp J.symm _).trans hF
  have hrem := adim9b_polynomial_equations_at_roots n d _ N θ (Ideal.Quotient.mk P v)
    Q δ (fun i ↦ Ideal.Quotient.mk P (c i)) R hmin hcoord (fun j ↦ B (J.symm j))
    (fun j i ↦ (J.symm j i : ℕ)) hN hF' q Δ r (fun j ↦ b (J.symm j)) hq hΔ hr (fun _ ↦ rfl)
  have hrelations (i : Fin n) := adim9b_coordinate_relation d θ (Ideal.Quotient.mk P v)
    (Ideal.Quotient.mk P (c i)) Q (W i) (R i) δ hmin (hcoord i) (hW i).1 (hWzero i)
    q (u i) (r i) Δ hq (fun j ↦ (hu i j).2) (humonic i) (hr i) hΔ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hdiv
  have hsmall := adim9b_reconstructed_coordinates_small n d P hP π θ hfinite hcomp c hc v Q δ R
    hmin hcoord q Δ r hq hΔ hr ε hε
  filter_upwards [hrem, Filter.eventually_all.mpr hrelations, hsmall,
    Metric.ball_mem_nhds (0 : Fin d → ℂ) hε] with w hwrem hwrel hwsmall hwnear
  intro t hΔw ht
  let z : Fin n → ℂ := fun i ↦ (r i).eval₂
    (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
  have hz : ‖z‖ < ε := (pi_norm_lt_iff hε).mpr (hwsmall t hΔw ht)
  have hp := hball (show (w, z) ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    exact max_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hwnear) hz)
  have hrzero : ∑ e, b e w * ∏ i, z i ^ (e i : ℕ) = 0 :=
    (Equiv.sum_comp J.symm _).symm.trans (hwrem t hΔw ht)
  change f z = _ at hp
  dsimp only at hp
  rw [hp, hrzero, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  rw [hwrel i t hΔw ht, mul_zero]

/-- Every nearby primitive root reconstructs a point satisfying all defining equations. -/
theorem adim9b_all_roots_off_discriminant (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔrep : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (m : ℕ) (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∀ w ∈ V, ∀ t : ℂ, Δ w ≠ 0 →
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        let z : Fin n → ℂ := fun i ↦
          (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
        z ∈ U ∧ π z = w ∧ ℓ z = t ∧ ∀ j, f j z = 0 := by
  have hzero (j : Fin m) := adim9b_analytic_equation_at_roots n d P hP π θ hfinite
    hcomp c hc v Q δ R hmin hcoord q Δ r hq hΔrep hr (g j)
    (hgen ▸ Ideal.subset_span (Set.mem_range_self j)) (f j) (hf j 0 hU0) (hrep j)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hU0)
  have hsmall := adim9b_reconstructed_coordinates_small n d P hP π θ hfinite
    hcomp c hc v Q δ R hmin hcoord q Δ r hq hΔrep hr ε hε
  have hlinear := adim9b_reconstructed_projection_and_primitive n d P π θ hcomp c hc v
    Q δ R hmin hcoord q Δ r hq hΔrep hr ℓ hv
  obtain ⟨V, hVsub, hVopen, hVzero⟩ :=
    mem_nhds_iff.mp (hsmall.and (hlinear.and (Filter.eventually_all.mpr hzero)))
  refine ⟨V, hVopen, hVzero, ?_⟩
  intro w hw t hΔw ht
  refine ⟨?_, (hVsub hw).2.1 t hΔw ht |>.1,
    (hVsub hw).2.1 t hΔw ht |>.2, fun j ↦ (hVsub hw).2.2 j t hΔw ht⟩
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  exact (pi_norm_lt_iff hε).mpr ((hVsub hw).1 t hΔw ht)

#print axioms adim9b_all_roots_off_discriminant

/-- A regular primitive equation and its reconstruction map produce a local
analytic section, with explicit image and retraction identities. -/
theorem adim9b_section_of_regular_model (n d : ℕ)
    (V : Set (Fin n → ℂ))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (F : (Fin d → ℂ) × ℂ → ℂ) (G : (Fin d → ℂ) × ℂ → (Fin n → ℂ))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0) (hreg : fderiv ℂ F 0 (0, 1) ≠ 0)
    (hmodel : ∀ᶠ p in 𝓝 (0 : (Fin d → ℂ) × ℂ),
      F p = 0 → G p ∈ V ∧ π (G p) = p.1)
    (hreconstruct : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      z ∈ V → F (π z, ℓ z) = 0 ∧ G (π z, ℓ z) = z) :
    ∃ g : (Fin d → ℂ) → (Fin n → ℂ), AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : Fin d → ℂ), π (g w) = w) ∧
      (∀ᶠ w in 𝓝 (0 : Fin d → ℂ), g w ∈ V) ∧
      (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ V → g (π z) = z) := by
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ :=
    AnalyticDivisorAlgebraic3.spec_exists_analytic_implicit hF hF0 hreg
  let k : (Fin d → ℂ) → (Fin d → ℂ) × ℂ := fun w ↦ (w, ψ w)
  have hk : AnalyticAt ℂ k 0 := analyticAt_id.prod hψ
  have hk0 : k 0 = 0 := Prod.ext rfl hψ0
  have hkt : Tendsto k (𝓝 0) (𝓝 0) := by
    have h := hk.continuousAt
    change Tendsto k (𝓝 0) (𝓝 (k 0)) at h
    rw [hk0] at h
    exact h
  let g := G ∘ k
  have hgood : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), g w ∈ V ∧ π (g w) = w := by
    filter_upwards [hkt.eventually hmodel, hkt.eventually hgraph] with w hm hg
    exact hm (hg.mpr rfl)
  refine ⟨g, hG.comp_of_eq hk hk0, ?_, hgood.mono (fun _ h ↦ h.2),
    hgood.mono (fun _ h ↦ h.1), ?_⟩
  · exact (congrArg G hk0).trans hG0
  · have hzt : Tendsto (π.prod ℓ) (𝓝 0) (𝓝 0) := by
      have h := (π.prod ℓ).continuous.continuousAt (x := (0 : Fin n → ℂ))
      change Tendsto (π.prod ℓ) (𝓝 0) (𝓝 ((π.prod ℓ) 0)) at h
      rw [map_zero] at h
      exact h
    filter_upwards [hzt.eventually hgraph, hreconstruct] with z hz hr hzV
    have hψz : ψ (π z) = ℓ z := hz.mp (hr hzV).1
    change G (π z, ψ (π z)) = z
    rw [hψz]
    exact (hr hzV).2

theorem adim9b_regular_model_dimension (n d : ℕ)
    (V : Set (Fin n → ℂ))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (F : (Fin d → ℂ) × ℂ → ℂ) (G : (Fin d → ℂ) × ℂ → (Fin n → ℂ))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0) (hreg : fderiv ℂ F 0 (0, 1) ≠ 0)
    (hmodel : ∀ᶠ p in 𝓝 (0 : (Fin d → ℂ) × ℂ),
      F p = 0 → G p ∈ V ∧ π (G p) = p.1)
    (hreconstruct : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      z ∈ V → F (π z, ℓ z) = 0 ∧ G (π z, ℓ z) = z) :
    (adim2_ideal n (adim2_germ n V 0)).IsPrime ∧
      ringKrullDim (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n V 0)) =
        (d : WithBot ℕ∞) := by
  obtain ⟨g, hg, hg0, hs, hi, hr⟩ :=
    adim9b_section_of_regular_model n d V π ℓ F G hF hG hF0 hG0 hreg hmodel hreconstruct
  exact ⟨adim9b_retractGerm_prime g hg hg0 π π.continuous.continuousAt (map_zero π) V hi hr,
    adim9b_retractGerm_dimension g hg hg0 π (π.analyticAt 0) (map_zero π) V hs hi hr⟩

set_option backward.isDefEq.respectTransparency false in
/-- A regular primitive model at an arbitrary anchor gives a prime germ of the parameter dimension. -/
theorem adim9b_regular_model_dimension_at (n d : ℕ)
    (V : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (F : (Fin d → ℂ) × ℂ → ℂ) (G : (Fin d → ℂ) × ℂ → (Fin n → ℂ))
    (hF : AnalyticAt ℂ F (π x, ℓ x)) (hG : AnalyticAt ℂ G (π x, ℓ x))
    (hF0 : F (π x, ℓ x) = 0) (hG0 : G (π x, ℓ x) = x)
    (hreg : fderiv ℂ F (π x, ℓ x) (0, 1) ≠ 0)
    (hmodel : ∀ᶠ p in 𝓝 (π x, ℓ x),
      F p = 0 → G p ∈ V ∧ π (G p) = p.1)
    (hreconstruct : ∀ᶠ z in 𝓝 x,
      z ∈ V → F (π z, ℓ z) = 0 ∧ G (π z, ℓ z) = z) :
    (adim2_ideal n (adim2_germ n V x)).IsPrime ∧
      ringKrullDim (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n V x)) =
        (d : WithBot ℕ∞) := by
  let a : (Fin d → ℂ) × ℂ := (π x, ℓ x)
  let T : (Fin d → ℂ) × ℂ → (Fin d → ℂ) × ℂ := fun p ↦ a + p
  have hT : AnalyticAt ℂ T 0 := analyticAt_const.add analyticAt_id
  have hT0 : T 0 = a := add_zero a
  have hTt : Tendsto T (𝓝 0) (𝓝 a) := by
    simpa only [ContinuousAt, hT0] using hT.continuousAt
  have hxt : Tendsto (fun z : Fin n → ℂ ↦ x + z) (𝓝 0) (𝓝 x) := by
    have hh : ContinuousAt (fun z : Fin n → ℂ ↦ x + z) 0 :=
      continuousAt_const.add continuousAt_id
    simpa only [ContinuousAt, add_zero] using hh
  have hreg' : fderiv ℂ (fun p ↦ F (T p)) 0 (0, 1) ≠ 0 := by
    have ht : HasFDerivAt T (ContinuousLinearMap.id ℂ ((Fin d → ℂ) × ℂ)) 0 :=
      (hasFDerivAt_id (0 : (Fin d → ℂ) × ℂ)).const_add a
    have hf : HasFDerivAt F (fderiv ℂ F a) (T 0) := by
      rw [hT0]; exact hF.differentiableAt.hasFDerivAt
    have hh : HasFDerivAt (fun p ↦ F (T p)) (fderiv ℂ F a) 0 := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using hf.comp 0 ht
    rw [hh.fderiv]
    exact hreg
  have hm : ∀ᶠ p in 𝓝 (0 : (Fin d → ℂ) × ℂ),
      F (T p) = 0 → x + (G (T p) - x) ∈ V ∧ π (G (T p) - x) = p.1 := by
    filter_upwards [hTt.eventually hmodel] with p hp hFp
    obtain ⟨hv, hπ⟩ := hp hFp
    refine ⟨by rw [show x + (G (T p) - x) = G (T p) by abel]; exact hv, ?_⟩
    rw [map_sub, hπ]
    change (π x + p.1) - π x = p.1
    abel
  have hr : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ V →
      F (T (π z, ℓ z)) = 0 ∧ G (T (π z, ℓ z)) - x = z := by
    filter_upwards [hxt.eventually hreconstruct] with z hz hzV
    have he : T (π z, ℓ z) = (π (x + z), ℓ (x + z)) := by
      simp only [T, a, Prod.add_def, map_add]
    rw [he, (hz hzV).2]
    exact ⟨(hz hzV).1, by abel⟩
  have h := adim9b_regular_model_dimension n d {z | x + z ∈ V} π ℓ
    (fun p ↦ F (T p)) (fun p ↦ G (T p) - x)
    (hF.comp_of_eq hT hT0) ((hG.comp_of_eq hT hT0).sub analyticAt_const)
    (by simpa only [hT0] using hF0) (by change G (T 0) - x = 0; rw [hT0]; exact sub_self x ▸ congrArg (fun z ↦ z - x) hG0) hreg' hm hr
  have he : adim2_germ n {z | x + z ∈ V} 0 = adim2_germ n V x := by
    unfold adim2_germ
    congr 1
    funext z
    simp only [zero_add, Set.mem_setOf_eq]
  rw [he] at h
  exact h

#print axioms adim9b_regular_model_dimension_at

/-- Off a nonzero discriminant, the prime zero set has prime germs of the parameter dimension. -/
theorem adim9b_off_discriminant_germ_dimension (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (G : Finset (AnalyticGerm n)) (hG : Ideal.span (G : Set (AnalyticGerm n)) = P)
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ g, Germ.ofFun (rep g) = g.val) :
    ∃ (δ : AnalyticGerm d) (Δ : (Fin d → ℂ) → ℂ), δ ≠ 0 ∧ AnalyticAt ℂ Δ 0 ∧
      Germ.ofFun Δ = δ.val ∧ ∃ W ∈ 𝓝 (0 : Fin n → ℂ),
        ∀ x ∈ W, (∀ g ∈ G, rep g x = 0) → Δ (π x) ≠ 0 →
          (adim2_ideal n (adim2_germ n {z | ∀ g ∈ G, rep g z = 0} x)).IsPrime ∧
          ringKrullDim (AnalyticGerm n ⧸
            adim2_ideal n (adim2_germ n {z | ∀ g ∈ G, rep g z = 0} x)) =
              (d : WithBot ℕ∞) := by
  classical
  let ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun w ↦
    Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  obtain ⟨ℓ, v, Q, δ, R, B, Cb, hv, -, -, hδ, hbez, hmin, hcoord⟩ :=
    adim7_primitive_form n d P hP π θ hfinite hinj hcomp c hc
  obtain ⟨q, hq⟩ := adim9b_poly_rep d Q
  obtain ⟨b, hb⟩ := adim9b_poly_rep d B
  obtain ⟨cb, hcb⟩ := adim9b_poly_rep d Cb
  choose r hr using fun i ↦ adim9b_poly_rep d (R i)
  obtain ⟨Δ, hΔ, hΔrep⟩ := δ.property
  refine ⟨δ, Δ, hδ, hΔ, hΔrep, ?_⟩
  -- the primitive relation vanishes on the component
  have hQzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ g ∈ G, rep g z = 0) →
      q.eval₂ (ev (π z)) (ℓ z) = 0 := by
    obtain ⟨bq, hbq, hQe⟩ := adim9b_eval_germ n d P π θ hcomp ℓ v hv Q q hq
    have hmem : bq ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, ← hQe]
      exact (hmin Q).mpr dvd_rfl
    exact adim9b_vanish_of_mem_span n G rep hrep bq hmem _ hbq.symm
  -- the coordinates are reconstructed on the component
  let bΔ : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ Δ (π z)), _,
    hΔ.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hθδ : θ δ = Ideal.Quotient.mk P bΔ := hcomp δ Δ hΔ hΔrep bΔ rfl
  have hcoordzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, (∀ g ∈ G, rep g z = 0) →
      Δ (π z) * z i - (r i).eval₂ (ev (π z)) (ℓ z) = 0 := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨br, hbr, hRe⟩ := adim9b_eval_germ n d P π θ hcomp ℓ v hv (R i) (r i) (hr i)
    have hmem : bΔ * c i - br ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hθδ, hcoord i, hRe,
        sub_self]
    apply adim9b_vanish_of_mem_span n G rep hrep _ hmem
    rw [show (bΔ * c i - br).val = bΔ.val * (c i).val - br.val from rfl, hbr]
    rfl
  -- the Bezout identity holds near the origin
  have hbezout : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ s : ℂ,
      b.eval₂ (ev w) s * q.eval₂ (ev w) s + cb.eval₂ (ev w) s * q.derivative.eval₂ (ev w) s =
        Δ w := by
    have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (T : Polynomial (AnalyticGerm d))
        (hFT : ∀ i, AnalyticAt ℂ (F.coeff i) 0 ∧ Germ.ofFun (F.coeff i) = (T.coeff i).val) :
        F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
          T.map (analyticGermSubring d).subtype := by
      ext i
      simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
        (hFT i).2
    have heq : (b * q + cb * q.derivative).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        (Polynomial.C Δ).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        ← Polynomial.derivative_map, hmap b B hb, hmap q Q hq, hmap cb Cb hcb,
        Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
        ← Polynomial.map_add, hbez, Polynomial.map_C, Polynomial.map_C]
      congr 1
      exact hΔrep.symm
    filter_upwards [adim9b_polynomial_representatives_eq d _ _ heq] with w hw s
    have := congrArg (fun a : Polynomial ℂ ↦ a.eval s) hw
    simp only [Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C] at this
    exact this
  -- an open parameter neighbourhood with analytic data
  have hnear : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      (∀ s : ℂ, b.eval₂ (ev w) s * q.eval₂ (ev w) s +
        cb.eval₂ (ev w) s * q.derivative.eval₂ (ev w) s = Δ w) ∧
      AnalyticAt ℂ Δ w ∧ (∀ i, AnalyticAt ℂ (q.coeff i) w) ∧
      ∀ j i, AnalyticAt ℂ ((r j).coeff i) w := by
    have hrall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ j i, AnalyticAt ℂ ((r j).coeff i) w := by
      rw [Filter.eventually_all]
      exact fun j ↦ adim9b_poly_coeff_analytic_eventually d (r j) (fun i ↦ (hr j i).1)
    filter_upwards [hbezout, hΔ.eventually_analyticAt,
      adim9b_poly_coeff_analytic_eventually d q (fun i ↦ (hq i).1), hrall] with w h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hroots : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (ev w) t = 0 →
      (∀ g ∈ G, rep g (fun i ↦ (r i).eval₂ (ev w) t / Δ w) = 0) ∧
      π (fun i ↦ (r i).eval₂ (ev w) t / Δ w) = w := by
    have hz : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ g ∈ G, ∀ t : ℂ, Δ w ≠ 0 →
        q.eval₂ (ev w) t = 0 →
        rep g (fun i ↦ (r i).eval₂ (ev w) t / Δ w) = 0 := by
      rw [Finset.eventually_all]
      intro g hg
      obtain ⟨f, hf, hfrep⟩ := g.property
      have hfa : AnalyticAt ℂ (rep g) 0 :=
        hf.congr (Germ.coe_eq.mp (hfrep.trans (hrep g).symm))
      exact adim9b_analytic_equation_at_roots n d P hP.ne_top π θ hfinite hcomp c hc
        v Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep (fun j i ↦ (hr j i).2)
        g (hG ▸ Ideal.subset_span hg) (rep g) hfa (hrep g)
    have hl := adim9b_reconstructed_projection_and_primitive n d P π θ hcomp c hc
      v Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep (fun j i ↦ (hr j i).2) ℓ hv
    filter_upwards [hz, hl] with w hw hz t hΔw ht
    exact ⟨fun g hg ↦ hw g hg t hΔw ht, (hz t hΔw ht).1⟩
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp (hnear.and hroots)
  let F : (Fin d → ℂ) × ℂ → ℂ := fun p ↦ q.eval₂ (ev p.1) p.2
  let Gm : (Fin d → ℂ) × ℂ → (Fin n → ℂ) :=
    fun p i ↦ (r i).eval₂ (ev p.1) p.2 / Δ p.1
  obtain ⟨W, hWsub, hWopen, hW0⟩ := mem_nhds_iff.mp (hQzero.and hcoordzero)
  refine ⟨W ∩ π ⁻¹' V, inter_mem (hWopen.mem_nhds hW0)
    (π.continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact hVopen.mem_nhds hV0)), ?_⟩
  intro x hx hxG hxΔ
  obtain ⟨hB, hΔa, hqa, hra⟩ := (hVsub hx.2).1
  have hFa : AnalyticAt ℂ F (π x, ℓ x) := adim9b_poly_eval_analyticAt d q _ hqa
  have hGa : AnalyticAt ℂ Gm (π x, ℓ x) := by
    apply AnalyticAt.pi
    intro i
    exact (adim9b_poly_eval_analyticAt d (r i) _ (hra i)).div
      (hΔa.comp_of_eq analyticAt_fst rfl) hxΔ
  have hF0 : F (π x, ℓ x) = 0 := (hWsub hx.1).1 hxG
  have hrec : ∀ z ∈ W, (∀ g ∈ G, rep g z = 0) → Δ (π z) ≠ 0 → Gm (π z, ℓ z) = z := by
    intro z hz hzG hzΔ
    funext i
    change (r i).eval₂ (ev (π z)) (ℓ z) / Δ (π z) = z i
    rw [div_eq_iff hzΔ]
    have hh := (hWsub hz).2 i hzG
    linear_combination -hh
  have hreg : fderiv ℂ F (π x, ℓ x) (0, 1) ≠ 0 := by
    have h1 : HasDerivAt (fun t : ℂ ↦ ((π x, t) : (Fin d → ℂ) × ℂ))
        ((0 : Fin d → ℂ), (1 : ℂ)) (ℓ x) :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have h2 := hFa.differentiableAt.hasFDerivAt.comp_hasDerivAt (ℓ x) h1
    have h3 : deriv (fun t ↦ F (π x, t)) (ℓ x) = fderiv ℂ F (π x, ℓ x) (0, 1) := h2.deriv
    rw [← h3]
    change deriv (fun t ↦ q.eval₂ (ev (π x)) t) (ℓ x) ≠ 0
    rw [adim9b_poly_deriv]
    intro h0
    apply hxΔ
    rw [← hB (ℓ x), show q.eval₂ (ev (π x)) (ℓ x) = 0 from hF0,
      h0, mul_zero, mul_zero, add_zero]
  apply adim9b_regular_model_dimension_at n d {z | ∀ g ∈ G, rep g z = 0} x π ℓ F Gm
    hFa hGa hF0 (hrec x hx.1 hxG hxΔ) hreg
  · have hVp : ∀ᶠ p in 𝓝 (π x, ℓ x), p.1 ∈ V :=
      continuous_fst.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hx.2)
    have hΔp : ∀ᶠ p in 𝓝 (π x, ℓ x), Δ p.1 ≠ 0 :=
      (hΔa.comp_of_eq analyticAt_fst rfl).continuousAt.eventually_ne hxΔ
    filter_upwards [hVp, hΔp] with p hp hδp hFp
    exact (hVsub hp).2 p.2 hδp hFp
  · have hΔz : ∀ᶠ z in 𝓝 x, Δ (π z) ≠ 0 :=
      (hΔa.comp (π.analyticAt x)).continuousAt.eventually_ne hxΔ
    filter_upwards [hWopen.mem_nhds hx.1, hΔz] with z hz hδz hzG
    exact ⟨(hWsub hz).1 hzG, hrec z hz hzG hδz⟩

#print axioms adim9b_off_discriminant_germ_dimension

/-- Vanishing on a finite union is vanishing on every member. -/
theorem adim9b_ideal_finset_sup {ι : Type*} (n : ℕ)
    (F : Finset ι) (S : ι → adim2_SetGerm n) :
    adim2_ideal n (F.sup S) = F.inf (fun i ↦ adim2_ideal n (S i)) := by
  classical
  induction F using Finset.cons_induction with
  | empty =>
    ext f
    change (⊥ ≤ adim2_zero n f) ↔ f ∈ (⊤ : Ideal (AnalyticGerm n))
    simp
  | cons i F hi ih =>
    rw [Finset.sup_cons, Finset.inf_cons, ← ih]
    ext f
    change (S i ⊔ F.sup S ≤ adim2_zero n f) ↔
      (S i ≤ adim2_zero n f) ∧ (F.sup S ≤ adim2_zero n f)
    exact sup_le_iff

#print axioms adim9b_ideal_finset_sup

/-- No minimal-prime zero germ in a finite component cover is redundant. -/
theorem adim9b_minimal_component_not_le_others (n : ℕ)
    (S : adim2_SetGerm n) (F : Finset (Ideal (AnalyticGerm n)))
    (hF : (F : Set (Ideal (AnalyticGerm n))) = (adim2_ideal n S).minimalPrimes)
    (hcover : S = F.sup (adim2_zeroSet n))
    (P : Ideal (AnalyticGerm n)) (hPF : P ∈ F) :
    ¬ adim2_zeroSet n P ≤ (F.erase P).sup (adim2_zeroSet n) := by
  classical
  intro hle
  have hP : P ∈ (adim2_ideal n S).minimalPrimes := hF ▸ hPF
  have hS : S = (F.erase P).sup (adim2_zeroSet n) := by
    rw [← Finset.insert_erase hPF, Finset.sup_insert] at hcover
    exact hcover.trans (sup_eq_right.mpr hle)
  have hI : (F.erase P).inf (fun Q ↦ adim2_ideal n (adim2_zeroSet n Q)) ≤ P := by
    rw [← adim9b_ideal_finset_sup, ← hS]
    exact hP.le
  obtain ⟨Q, hQ, hQP⟩ := hP.isPrime.inf_le'.mp hI
  have hQF : Q ∈ F := Finset.mem_of_mem_erase hQ
  have hQmin : Q ∈ (adim2_ideal n S).minimalPrimes := hF ▸ hQF
  have hQP' : Q ≤ P := ((adim2_galois n _ Q).mp le_rfl).trans hQP
  exact (Finset.mem_erase.mp hQ).1 (hQP'.antisymm (hP.2 hQmin.1 hQP'))

#print axioms adim9b_minimal_component_not_le_others

/-- Every minimal component has points arbitrarily near the anchor outside all the others. -/
theorem adim9b_frequently_outside_other_components (n : ℕ)
    (S : adim2_SetGerm n) (F : Finset (Ideal (AnalyticGerm n)))
    (hF : (F : Set (Ideal (AnalyticGerm n))) = (adim2_ideal n S).minimalPrimes)
    (hcover : S = F.sup (adim2_zeroSet n))
    (P : Ideal (AnalyticGerm n)) (hPF : P ∈ F)
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ)
    (hrep : ∀ g, Germ.ofFun (rep g) = g.val) :
    ∃ᶠ z in 𝓝 (0 : Fin n → ℂ),
      (∀ g ∈ adim2_generators n P, rep g z = 0) ∧
      ∀ Q ∈ F.erase P, ¬ (∀ g ∈ adim2_generators n Q, rep g z = 0) := by
  classical
  change ¬ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ¬ _
  intro hall
  apply adim9b_minimal_component_not_le_others n S F hF hcover P hPF
  rw [adim9b_zeroSet_eq n rep hrep, adim9b_sup_zeroSet_eq n rep hrep]
  change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
    (∀ g ∈ adim2_generators n P, rep g z = 0) →
      ∃ Q ∈ F.erase P, ∀ g ∈ adim2_generators n Q, rep g z = 0
  filter_upwards [hall] with z hz hzP
  by_contra hn
  exact hz ⟨hzP, fun Q hQ hzero ↦ hn ⟨Q, hQ, hzero⟩⟩

#print axioms adim9b_frequently_outside_other_components

/-- Minimal primes of a geometric vanishing ideal are recovered from their zero germs. -/
theorem adim9b_minimal_component_ideal (n : ℕ)
    (S : adim2_SetGerm n) (F : Finset (Ideal (AnalyticGerm n)))
    (hF : (F : Set (Ideal (AnalyticGerm n))) = (adim2_ideal n S).minimalPrimes)
    (hcover : S = F.sup (adim2_zeroSet n))
    (P : Ideal (AnalyticGerm n)) (hPF : P ∈ F) :
    adim2_ideal n (adim2_zeroSet n P) = P := by
  have hP : P ∈ (adim2_ideal n S).minimalPrimes := hF ▸ hPF
  have hI : F.inf (fun Q ↦ adim2_ideal n (adim2_zeroSet n Q)) ≤ P := by
    rw [← adim9b_ideal_finset_sup, ← hcover]
    exact hP.le
  obtain ⟨Q, hQ, hQP⟩ := hP.isPrime.inf_le'.mp hI
  have hQmin : Q ∈ (adim2_ideal n S).minimalPrimes := hF ▸ hQ
  have hQP' : Q ≤ P := ((adim2_galois n _ Q).mp le_rfl).trans hQP
  have heq : Q = P := hQP'.antisymm (hP.2 hQmin.1 hQP')
  exact (heq ▸ hQP).antisymm ((adim2_galois n _ P).mp le_rfl)

#print axioms adim9b_minimal_component_ideal

/-- A prime zero germ lying in a set inherits an upper dimension bound from that set's Hausdorff dimension. -/
theorem adim9b_prime_dimension_le_of_dimH (n e : ℕ)
    (A : Set (Fin n → ℂ)) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (hsub : adim2_zeroSet n P ≤ adim2_germ n A 0)
    (hbound : dimH A ≤ ((2 * e : ℕ) : ℝ≥0∞)) :
    ringKrullDim (AnalyticGerm n ⧸ P) ≤ (e : WithBot ℕ∞) := by
  classical
  obtain ⟨d, π, θ, -, hfinite, hinj, hcomp, hdim⟩ := adim5_finite_parameters n P hP
  choose rep hrepa hrep using fun g : AnalyticGerm n ↦ g.property
  let G := adim2_generators n P
  let g : Fin G.card → AnalyticGerm n := fun j ↦ (G.equivFin.symm j).val
  have hg : Ideal.span (Set.range g) = P := by
    have he : Set.range g = (G : Set (AnalyticGerm n)) := by
      ext b
      constructor
      · rintro ⟨j, rfl⟩
        exact (G.equivFin.symm j).property
      · intro hb
        exact ⟨G.equivFin ⟨b, hb⟩, by simp [g]⟩
    rw [he]
    exact adim9b_span_generators n P
  have hinc : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, rep (g j) z = 0) → z ∈ A := by
    rw [adim9b_zeroSet_eq n rep hrep] at hsub
    change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      (∀ b ∈ G, rep b z = 0) → 0 + z ∈ A at hsub
    filter_upwards [hsub] with z hz hzero
    simpa only [zero_add] using hz (fun b hb ↦ by
      simpa [g] using hzero (G.equivFin ⟨b, hb⟩))
  have han : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, AnalyticAt ℂ (rep (g j)) z :=
    Filter.eventually_all.mpr fun j ↦ (hrepa (g j)).eventually_analyticAt
  obtain ⟨U, hUsub, hUopen, hU0⟩ := mem_nhds_iff.mp (han.and hinc)
  obtain ⟨W, V, -, -, hWU, hVopen, hV0, p, hp, -, -, hsurj, -⟩ :=
    adim7_surjective_projection n d G.card P hP π θ hfinite hinj hcomp g hg
      (fun j ↦ rep (g j)) U hUopen hU0 (fun j z hz ↦ (hUsub hz).1 j)
      (fun j ↦ hrep (g j))
  have hVA : V ⊆ π '' A := by
    intro w hw
    obtain ⟨z, hz⟩ := hsurj ⟨w, hw⟩
    refine ⟨z.val, (hUsub (hWU z.property.1)).2 z.property.2, ?_⟩
    exact (hp z).symm.trans (congrArg Subtype.val hz)
  have hde : d ≤ e := adim9b_parameter_dimension_le_of_dimH A π hbound
    ⟨0, (hVopen.subset_interior_iff.mpr hVA) hV0⟩
  rw [← hdim, adim6_parameter_dimension]
  exact_mod_cast hde

#print axioms adim9b_prime_dimension_le_of_dimH

theorem adim9b_local_equations_of_representatives (n m : ℕ)
    (A : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hxU : x ∈ U)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    ∃ s : Finset (AnalyticGerm n), adim2_germ n A x = s.inf (adim2_zero n) := by
  classical
  let g : Fin m → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z ↦ f i (x + z)), fun z ↦ f i (x + z),
      (hf i x hxU).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp), rfl⟩
  refine ⟨Finset.univ.image g, ?_⟩
  simp only [adim2_germ, adim2_zero, Finset.inf_image, Finset.inf_apply]
  have hinf : ∀ t : Finset (Fin m),
      t.inf (adim2_zero n ∘ g) =
        Filter.Germ.ofFun (fun z ↦ ∀ i ∈ t, f i (x + z) = 0) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        apply Filter.Germ.coe_eq.mpr
        exact Filter.Eventually.of_forall (by simp)
    | @insert a t ha ih =>
        rw [Finset.inf_insert, ih]
        apply Filter.Germ.coe_eq.mpr
        exact Filter.Eventually.of_forall (by simp [adim2_zero, g, ha])
  rw [hinf]
  apply Filter.Germ.coe_eq.mpr
  have hc : ContinuousAt (fun z : Fin n → ℂ ↦ x + z) 0 :=
    continuousAt_const.add continuousAt_id
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds (by simpa using hxU))] with z hz
  simp only [Finset.mem_univ, forall_const, g]
  exact propext (hA (x + z) hz)


/-- Nearby local components cannot exceed a uniform dimension bound at the anchor. -/
theorem adim9b_component_dimension_upper_near (n e m : ℕ)
    (A : Set (Fin (n + 1) → ℂ))
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (hdim : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ (e : WithBot ℕ∞)) :
    ∃ W : Set (Fin (n + 1) → ℂ), IsOpen W ∧ (0 : Fin (n + 1) → ℂ) ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A y)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) ≤ (e : WithBot ℕ∞) := by
  classical
  have hloc : ∃ U' : Set (Fin (n + 1) → ℂ), IsOpen U' ∧ (0 : Fin (n + 1) → ℂ) ∈ U' ∧
      ∃ s : Finset ((Fin (n + 1) → ℂ) → ℂ), (∀ h ∈ s, AnalyticOnNhd ℂ h U') ∧
        ∀ z ∈ U', (z ∈ A ↔ ∀ h ∈ s, h z = 0) := by
    refine ⟨U, hU, hU0, Finset.univ.image f, ?_, ?_⟩
    · intro h hh
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hh
      exact hf j
    · intro z hz
      simpa only [Finset.forall_mem_image, Finset.mem_univ, forall_const] using hA z hz
  obtain ⟨H, hH, hHdim⟩ := adim9b_local_dimH n e A hloc hdim
  obtain ⟨W, hWsub, hWopen, hW0⟩ := mem_nhds_iff.mp (inter_mem hH (hU.mem_nhds hU0))
  refine ⟨W, hWopen, hW0, fun z hz ↦ (hWsub hz).2, ?_⟩
  intro y hy Q hQ
  obtain ⟨s, hs⟩ := adim9b_local_equations_of_representatives (n + 1) m A y U hU
    (hWsub hy).2 f hf hA
  obtain ⟨F, hF, hcover⟩ := adim3_minimal_prime_cover (n + 1) s
  have hQF : Q ∈ F := by
    rw [← hs] at hF
    change Q ∈ (F : Set (Ideal (AnalyticGerm (n + 1))))
    rw [hF]
    exact hQ
  have hsub : adim2_zeroSet (n + 1) Q ≤ adim2_germ (n + 1) A y := by
    rw [hs, hcover]
    exact Finset.le_sup hQF
  let B : Set (Fin (n + 1) → ℂ) := {z | y + z ∈ A ∩ H}
  have hB : adim2_germ (n + 1) B 0 = adim2_germ (n + 1) A y := by
    apply Germ.coe_eq.mpr
    have ht : ContinuousAt (fun z : Fin (n + 1) → ℂ ↦ y + z) 0 :=
      continuousAt_const.add continuousAt_id
    have hHy : H ∈ 𝓝 y := mem_of_superset (hWopen.mem_nhds hy) fun z hz ↦ (hWsub hz).1
    filter_upwards [ht.preimage_mem_nhds (by simpa only [add_zero] using hHy)] with z hz
    apply propext
    rw [zero_add]
    change (y + z ∈ A ∧ y + z ∈ H) ↔ y + z ∈ A
    exact ⟨And.left, fun ha ↦ ⟨ha, hz⟩⟩
  apply adim9b_prime_dimension_le_of_dimH (n + 1) e B Q hQ.isPrime (hB.symm ▸ hsub)
  exact (isometry_add_left y).antilipschitzWith.dimH_preimage_le (A ∩ H) |>.trans hHdim

#print axioms adim9b_component_dimension_upper_near

/-- The upper inequality in local purity follows from the local Hausdorff bound. -/
theorem adim9b_local_purity_upper (n e m : ℕ)
    (P : Ideal (AnalyticGerm (n + 1)))
    (hdim : ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (e : WithBot ℕ∞))
    (g : Fin m → AnalyticGerm (n + 1))
    (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ W : Set (Fin (n + 1) → ℂ), IsOpen W ∧ (0 : Fin (n + 1) → ℂ) ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, ∀ Q ∈ (adim2_ideal (n + 1)
        (adim2_germ (n + 1) {z | ∀ j, f j z = 0} y)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) ≤ (e : WithBot ℕ∞) := by
  have hPI : P ≤ adim2_ideal (n + 1)
      (adim2_germ (n + 1) {z | ∀ j, f j z = 0} 0) := by
    rw [← hgen]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change adim2_germ (n + 1) {z | ∀ j, f j z = 0} 0 ≤ adim2_zero (n + 1) (g j)
    unfold adim2_germ adim2_zero
    rw [← hrep j]
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), (∀ j, f j (0 + z) = 0) → f j z = 0
    filter_upwards with z hz
    simpa only [zero_add] using hz j
  apply adim9b_component_dimension_upper_near n e m {z | ∀ j, f j z = 0}
    U hU hU0 f hf (fun _ _ ↦ Iff.rfl)
  intro Q hQ
  rw [← hdim]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hPI.trans hQ.le))
    (Ideal.Quotient.factor_surjective (hPI.trans hQ.le))

#print axioms adim9b_local_purity_upper

/-- Finite equations for a prime germ are pure of the expected dimension off a nonzero discriminant. -/
theorem adim9b_prime_regular_locus (n e m : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (π : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ))
      (δ : AnalyticGerm e) (Δ : (Fin e → ℂ) → ℂ),
      δ ≠ 0 ∧ AnalyticAt ℂ Δ 0 ∧ Germ.ofFun Δ = δ.val ∧
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) → Δ (π y) ≠ 0 →
          ∀ Q ∈ (adim2_ideal n (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞) := by
  classical
  obtain ⟨d, π, θ, -, hfinite, hinj, hcomp, hparam⟩ := adim5_finite_parameters n P hP
  have hde : d = e := by
    have hh := (adim6_parameter_dimension d).symm.trans (hparam.trans hdim)
    exact_mod_cast hh
  subst d
  choose rep hrepa hr using fun a : AnalyticGerm n ↦ a.property
  let G := Finset.univ.image g
  have hG : Ideal.span (G : Set (AnalyticGerm n)) = P := by
    simpa only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen
  obtain ⟨δ, Δ, hδ, hΔ, hΔrep, H, hH, hgood⟩ :=
    adim9b_off_discriminant_germ_dimension n e P hP π θ hfinite hinj hcomp G hG rep hr
  have hbridge : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, rep (g j) z = f j z :=
    Filter.eventually_all.mpr fun j ↦ Germ.coe_eq.mp ((hr (g j)).trans (hrep j).symm)
  obtain ⟨W, hWsub, hWopen, hW0⟩ :=
    mem_nhds_iff.mp (inter_mem (inter_mem hH (hU.mem_nhds hU0)) hbridge)
  have hzero (z : Fin n → ℂ) (hz : z ∈ W) :
      (∀ j, f j z = 0) ↔ (∀ a ∈ G, rep a z = 0) := by
    simp only [G, Finset.forall_mem_image, Finset.mem_univ, forall_const]
    have he : ∀ j, rep (g j) z = f j z := (hWsub hz).2
    simp only [he]
  refine ⟨π, δ, Δ, hδ, hΔ, hΔrep, W, hWopen, hW0, fun z hz ↦ (hWsub hz).1.2, ?_⟩
  intro y hy hyf hyΔ Q hQ
  have heq : adim2_germ n {z | ∀ j, f j z = 0} y =
      adim2_germ n {z | ∀ a ∈ G, rep a z = 0} y := by
    apply Germ.coe_eq.mpr
    have ht : ContinuousAt (fun z : Fin n → ℂ ↦ y + z) 0 :=
      continuousAt_const.add continuousAt_id
    filter_upwards [ht.preimage_mem_nhds
      (hWopen.mem_nhds (by simpa only [add_zero] using hy))] with z hz
    exact propext (hzero (y + z) hz)
  obtain ⟨hp, hd⟩ := hgood y (hWsub hy).1.1 ((hzero y hy).mp hyf) hyΔ
  rw [heq] at hQ
  have hQI : Q = adim2_ideal n (adim2_germ n {z | ∀ a ∈ G, rep a z = 0} y) :=
    (hQ.2 ⟨hp, le_rfl⟩ hQ.le).antisymm hQ.le
  rw [hQI]
  exact hd

#print axioms adim9b_prime_regular_locus

open IntermediateField in
theorem adim9b_primitive_pair_in_infinite_set {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra K L] [Finite (IntermediateField K L)]
    (ι : k →+* K) (s : Set k) (hs : s.Infinite) (α β : L) :
    ∃ c ∈ s, IntermediateField.adjoin K {α, β} =
      IntermediateField.adjoin K {α + (ι c) • β} := by
  letI : Infinite s := hs.to_subtype
  let f : s → IntermediateField K L := fun c ↦ adjoin K {α + (ι c.val) • β}
  obtain ⟨x, y, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨x.val, x.property, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    have hx : α + (ι x.val) • β ∈ adjoin K {α + (ι x.val) • β} :=
      mem_adjoin_simple_self K _
    have hy : α + (ι y.val) • β ∈ adjoin K {α + (ι x.val) • β} := by
      rw [show adjoin K {α + (ι x.val) • β} = adjoin K {α + (ι y.val) • β} from heq]
      exact mem_adjoin_simple_self K _
    have hβ := sub_mem hx hy
    rw [show (α + (ι x.val) • β) - (α + (ι y.val) • β) =
      (ι x.val - ι y.val) • β by rw [sub_smul]; abel] at hβ
    replace hβ := smul_mem _ hβ (x := (ι x.val - ι y.val)⁻¹)
    have hdiff : ι x.val - ι y.val ≠ 0 :=
      sub_ne_zero.mpr (fun h ↦ hneq (Subtype.ext (ι.injective h)))
    rw [smul_smul, inv_mul_cancel₀ hdiff, one_smul] at hβ
    have hα : α ∈ adjoin K {α + (ι x.val) • β} := by
      simpa using sub_mem hx (smul_mem _ hβ (x := ι x.val))
    rintro z (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    have hα : α ∈ adjoin K {α, β} := subset_adjoin K _ (Set.mem_insert α {β})
    have hβ : β ∈ adjoin K {α, β} := subset_adjoin K _ (Set.mem_insert_of_mem α rfl)
    exact (adjoin K {α, β}).add_mem hα ((adjoin K {α, β}).smul_mem hβ)

/-- Only finitely many scalars fail to generate the two-element intermediate field. -/
theorem adim9b_primitive_pair_cofinite {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra K L] [Finite (IntermediateField K L)]
    (ι : k →+* K) (α β : L) :
    ∀ᶠ c in Filter.cofinite, IntermediateField.adjoin K {α, β} =
      IntermediateField.adjoin K {α + (ι c) • β} := by
  rw [Filter.eventually_cofinite]
  by_contra h
  obtain ⟨c, hc, he⟩ := adim9b_primitive_pair_in_infinite_set ι _ h α β
  exact hc he

/-- Perturbing a primitive element has only finitely many exceptional scalars. -/
theorem adim9b_primitive_perturbation_cofinite {k K L : Type*}
    [Field k] [Field K] [Field L] [Algebra K L]
    [Finite (IntermediateField K L)] (ι : k →+* K) (α β : L)
    (hα : IntermediateField.adjoin K {α} = ⊤) :
    ∀ᶠ c in Filter.cofinite, IntermediateField.adjoin K {α + (ι c) • β} = ⊤ := by
  have hpair : IntermediateField.adjoin K {α, β} = ⊤ := by
    apply top_unique
    rw [← hα]
    apply IntermediateField.adjoin.mono
    exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  filter_upwards [adim9b_primitive_pair_cofinite ι α β] with c hc
  exact hc.symm.trans hpair

#print axioms adim9b_primitive_pair_in_infinite_set
#print axioms adim9b_primitive_pair_cofinite
#print axioms adim9b_primitive_perturbation_cofinite

/-- A nonconstant affine scalar expression vanishes at at most one scalar. -/
theorem adim9b_affine_ne_zero_cofinite (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ c : ℂ in Filter.cofinite, a + c * b ≠ 0 := by
  by_cases hb : b = 0
  · exact Filter.Eventually.of_forall (by simpa [hb] using h.resolve_right (not_not.mpr hb))
  · filter_upwards [Filter.eventually_cofinite_ne (-a / b)] with c hc
    intro hz
    apply hc
    apply (eq_div_iff hb).mpr
    linear_combination hz

/-- Finitely many nonzero linear functionals have a simultaneous nonzero value. -/
theorem adim9b_avoid_finite_linear_kernels {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset (V →ₗ[ℂ] ℂ)) (hs : ∀ e ∈ s, e ≠ 0) :
    ∃ v : V, ∀ e ∈ s, e v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert e s he ih =>
    obtain ⟨v, hv⟩ := ih (fun f hf ↦ hs f (Finset.mem_insert_of_mem hf))
    have hene : e ≠ 0 := hs e (Finset.mem_insert_self _ _)
    obtain ⟨x, hx⟩ : ∃ x, e x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hene (LinearMap.ext h)
    have hold : ∀ᶠ c : ℂ in Filter.cofinite, ∀ f ∈ s, f (v + c • x) ≠ 0 := by
      apply (Filter.eventually_all_finite s.finite_toSet).mpr
      intro f hf
      simpa only [map_add, map_smul, smul_eq_mul] using
        adim9b_affine_ne_zero_cofinite (f v) (f x) (Or.inl (hv f hf))
    have hnew : ∀ᶠ c : ℂ in Filter.cofinite, e (v + c • x) ≠ 0 := by
      simpa only [map_add, map_smul, smul_eq_mul] using
        adim9b_affine_ne_zero_cofinite (e v) (e x) (Or.inr hx)
    obtain ⟨c, hc, hc'⟩ := (hold.and hnew).exists
    exact ⟨v + c • x, fun f hf ↦ (Finset.mem_insert.mp hf).elim
      (fun h ↦ h ▸ hc') (hc f)⟩

/-- Primitive linear combinations can preserve any finite list of nonvanishing constraints. -/
theorem adim9b_linear_primitive_with_constraints
    {K L V : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] L) (E : Finset (V →ₗ[ℂ] ℂ))
    (hE : ∀ e ∈ E, e ≠ 0) (s : Finset V) :
    ∃ v : V, (∀ e ∈ E, e v ≠ 0) ∧
      ∀ x ∈ s, T x ∈ IntermediateField.adjoin K {T v} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv⟩ := adim9b_avoid_finite_linear_kernels E hE
    exact ⟨v, hv, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨v, hv, hmem⟩ := ih
    have hgood : ∀ᶠ c : ℂ in Filter.cofinite, ∀ e ∈ E, e (v + c • x) ≠ 0 := by
      apply (Filter.eventually_all_finite E.finite_toSet).mpr
      intro e he
      simpa only [map_add, map_smul, smul_eq_mul] using
        adim9b_affine_ne_zero_cofinite (e v) (e x) (Or.inl (hv e he))
    obtain ⟨c, hc, hfield⟩ := (hgood.and
      (adim9b_primitive_pair_cofinite (algebraMap ℂ K) (T v) (T x))).exists
    have hTv : T (v + c • x) = T v + (algebraMap ℂ K c) • T x := by
      rw [map_add, map_smul, IsScalarTower.algebraMap_smul]
    refine ⟨v + c • x, hc, ?_⟩
    intro y hy
    rw [hTv, ← hfield]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)
    · apply (show IntermediateField.adjoin K {T v} ≤
          IntermediateField.adjoin K {T v, T x} from ?_) (hmem y hy)
      apply IntermediateField.adjoin.mono
      exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

#print axioms adim9b_affine_ne_zero_cofinite
#print axioms adim9b_avoid_finite_linear_kernels
#print axioms adim9b_linear_primitive_with_constraints

/-- A primitive linear coordinate can avoid finitely many prescribed nonzero vectors. -/
theorem adim9b_primitive_linear_form_avoiding
    {K L : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] (n : ℕ)
    (T : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L)
    (F : Finset (Fin n → ℂ)) (hF : ∀ z ∈ F, z ≠ 0) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ, (∀ z ∈ F, ℓ z ≠ 0) ∧
      ∀ i : Fin n, T (ContinuousLinearMap.proj i) ∈ IntermediateField.adjoin K {T ℓ} := by
  classical
  let ev : (Fin n → ℂ) → (((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] ℂ) := fun z ↦
    { toFun := fun ℓ ↦ ℓ z, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hev : ∀ e ∈ F.image ev, e ≠ 0 := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    intro hez
    apply hF z hz
    funext i
    exact congrArg (fun f : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] ℂ ↦
      f (ContinuousLinearMap.proj i)) hez
  obtain ⟨ℓ, hℓ, hcoords⟩ := adim9b_linear_primitive_with_constraints (K := K) T
    (F.image ev) hev (Finset.univ.image (fun i : Fin n ↦
      (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ)))
  exact ⟨ℓ, fun z hz ↦ hℓ (ev z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩),
    fun i ↦ hcoords _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩

/-- Primitivity, finite-fibre separation and nonvanishing on a projection kernel
can be imposed simultaneously on a linear coordinate. -/
theorem adim9b_primitive_linear_form_separating
    {K L : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] (n d : ℕ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (T : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L)
    (F : Finset (Fin n → ℂ)) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ,
      Set.InjOn ℓ (F : Set (Fin n → ℂ)) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      ∀ i : Fin n, T (ContinuousLinearMap.proj i) ∈ IntermediateField.adjoin K {T ℓ} := by
  classical
  let D := ((F ×ˢ F).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ p.1 - p.2)
  have hD : ∀ z ∈ D, z ≠ 0 := by
    intro z hz
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hxy).2
  have hsep (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (hℓ : ∀ z ∈ D, ℓ z ≠ 0) :
      Set.InjOn ℓ (F : Set (Fin n → ℂ)) := by
    intro x hx y hy heq
    by_contra hne
    have hz : x - y ∈ D := Finset.mem_image.mpr ⟨(x, y),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hne⟩, rfl⟩
    exact hℓ _ hz (by rw [map_sub, heq, sub_self])
  by_cases hnd : d < n
  · have hker : LinearMap.ker π.toLinearMap ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      simpa using hnd
    obtain ⟨z, hzπ, hz⟩ := (Submodule.ne_bot_iff _).mp hker
    obtain ⟨ℓ, hℓ, hc⟩ := adim9b_primitive_linear_form_avoiding (K := K) n T
      (insert z D) (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hz
        · exact hD w hw)
    exact ⟨ℓ, hsep ℓ (fun w hw ↦ hℓ w (Finset.mem_insert_of_mem hw)),
      fun _ ↦ ⟨z, hzπ, hℓ z (Finset.mem_insert_self _ _)⟩, hc⟩
  · obtain ⟨ℓ, hℓ, hc⟩ := adim9b_primitive_linear_form_avoiding (K := K) n T D hD
    exact ⟨ℓ, hsep ℓ hℓ, fun h ↦ (hnd h).elim, hc⟩

#print axioms adim9b_primitive_linear_form_avoiding
#print axioms adim9b_primitive_linear_form_separating

private def adim9b_sep_constantGerm (n : ℕ) : ℂ →+* AnalyticGerm n where
  toFun c := ⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def adim9b_sep_linearGerm {n : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) : AnalyticGerm n :=
  ⟨Germ.ofFun (fun z ↦ ℓ z), fun z ↦ ℓ z, ℓ.analyticAt 0, rfl⟩

private def adim9b_sep_linearGermMap {n : ℕ} {L : Type*} [CommRing L] [Algebra ℂ L]
    (f : AnalyticGerm n →+* L)
    (hconst : ∀ c, f (adim9b_sep_constantGerm n c) = algebraMap ℂ L c) :
    ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L where
  toFun ℓ := f (adim9b_sep_linearGerm ℓ)
  map_add' ℓ m := by
    have h : adim9b_sep_linearGerm (ℓ + m) = adim9b_sep_linearGerm ℓ + adim9b_sep_linearGerm m := rfl
    rw [h, map_add]
  map_smul' c ℓ := by
    have h : adim9b_sep_linearGerm (c • ℓ) =
        adim9b_sep_constantGerm n c * adim9b_sep_linearGerm ℓ := rfl
    rw [h, map_mul, hconst, Algebra.smul_def]
    rfl

private theorem adim9b_sep_finite_fraction_extension
    (A S K L : Type*) [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
    [Field K] [Field L] [CharZero K]
    [Algebra A S] [FaithfulSMul A S] [Module.Finite A S]
    [Algebra A K] [IsFractionRing A K] [Algebra S L] [IsFractionRing S L]
    [Algebra A L] [Algebra K L] [IsScalarTower A S L] [IsScalarTower A K L] :
    Module.Finite K L ∧ Algebra.IsSeparable K L ∧
      ∃ x : L, IntermediateField.adjoin K {x} = ⊤ := by
  letI : Module.Finite K L := Module.Finite.of_isLocalization A S (nonZeroDivisors A)
  exact ⟨inferInstance, inferInstance, Field.exists_primitive_element K L⟩

private theorem adim9b_sep_bezout_of_separable_fraction_map
    {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (Q : Polynomial A) (hdeg : 0 < Q.natDegree)
    (hsep : (Q.map (algebraMap A K)).Separable) :
    ∃ (δ : A) (B C : Polynomial A), δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ := by
  let δ := Q.resultant Q.derivative
  have hinj := IsFractionRing.injective A K
  have hnz : δ ≠ 0 := by
    have h := Polynomial.resultant_ne_zero _ _ hsep
    rw [Polynomial.derivative_map] at h
    simp only [Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.resultant_map_map] at h
    exact fun hz ↦ h (by change algebraMap A K δ = 0; rw [hz, map_zero])
  obtain ⟨B, C, _, _, hBC⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    Q Q.derivative le_rfl le_rfl (Or.inl (Nat.ne_of_gt hdeg))
  exact ⟨δ, B, C, hnz, by simpa only [mul_comm] using hBC⟩

private theorem adim9b_sep_clear_one_coordinate {A S K L : Type*} [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra A S] [Algebra A K] [IsFractionRing A K]
    [Algebra S L] [IsFractionRing S L] [Algebra A L] [Algebra K L]
    [IsScalarTower A S L] [IsScalarTower A K L]
    (v x : S) (hx : algebraMap S L x ∈ Algebra.adjoin K {algebraMap S L v}) :
    ∃ (a : A) (R : Polynomial A), a ≠ 0 ∧
      algebraMap A S a * x = Polynomial.aeval v R := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨a, ha, hR⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  refine ⟨a, IsLocalization.integerNormalization (nonZeroDivisors A) p,
    nonZeroDivisors.ne_zero ha, ?_⟩
  apply IsFractionRing.injective S L
  rw [← IsScalarTower.algebraMap_smul K a p] at hR
  have he := congrArg (Polynomial.aeval (algebraMap S L v)) hR
  simp only [Polynomial.aeval_map_algebraMap, map_smul, hp,
    Polynomial.aeval_algebraMap_apply] at he
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def] using he.symm

private theorem adim9b_sep_clear_coordinates
    {A S K L : Type*} [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra A S] [Algebra A K] [IsFractionRing A K]
    [Algebra S L] [IsFractionRing S L] [Algebra A L] [Algebra K L]
    [IsScalarTower A S L] [IsScalarTower A K L]
    {n : ℕ} (v : S) (x : Fin n → S)
    (hx : ∀ i, algebraMap S L (x i) ∈ Algebra.adjoin K {algebraMap S L v}) :
    ∃ (a : A) (R : Fin n → Polynomial A), a ≠ 0 ∧
      ∀ i, algebraMap A S a * x i = Polynomial.aeval v (R i) := by
  classical
  choose a R ha hR using fun i ↦ adim9b_sep_clear_one_coordinate (A := A) v (x i) (hx i)
  let b : Fin n → A := fun i ↦ ∏ j ∈ Finset.univ.erase i, a j
  refine ⟨∏ i, a i, fun i ↦ Polynomial.C (b i) * R i,
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ha i), fun i ↦ ?_⟩
  have hprod : (∏ j, a j) = b i * a i :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hprod, map_mul, mul_assoc, hR i, map_mul, Polynomial.aeval_C]

private theorem adim9b_sep_weierstrass_of_monic_dvd {d : ℕ}
    {Q W : Polynomial (AnalyticGerm d)} (hW : IsWeierstrassPolynomial W)
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (hdiv : Q ∣ W) :
    IsWeierstrassPolynomial Q := by
  have hWmap : W.map (analyticGermValue d) = X ^ W.natDegree := by
    ext j
    rw [coeff_map, coeff_X_pow]
    split_ifs with hj
    · subst j
      rw [← leadingCoeff, hW.1, map_one]
    · by_cases hjlt : j < W.natDegree
      · exact hW.2.2 j hjlt
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have hmapdiv : Q.map (analyticGermValue d) ∣ X ^ W.natDegree := by
    rw [← hWmap]
    exact Polynomial.map_dvd _ hdiv
  obtain ⟨k, _, hk⟩ := (dvd_prime_pow (prime_X (R := ℂ)) W.natDegree).mp hmapdiv
  have heq : Q.map (analyticGermValue d) = X ^ k :=
    eq_of_monic_of_associated (hQ.map _) (monic_X_pow k) hk
  have hkdeg : k = Q.natDegree := by
    simpa only [hQ.natDegree_map, natDegree_X_pow] using
      (congrArg Polynomial.natDegree heq).symm
  refine ⟨hQ, hdeg, fun j hj ↦ ?_⟩
  change analyticGermValue d (Q.coeff j) = 0
  have hcoeff := congrArg (fun p : Polynomial ℂ ↦ p.coeff j) heq
  simpa only [coeff_map, coeff_X_pow, hkdeg, if_neg (ne_of_lt hj)] using hcoeff

private theorem adim9b_sep_map_preserves_germ_value (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b := by
  letI : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro x y hxy
    rw [analyticGerm_isUnit_iff] at hxy
    simp only [map_add] at hxy
    by_cases hx : analyticGermValue n x = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [hx] using hxy
    · left
      rwa [analyticGerm_isUnit_iff]
  have hmax : IsLocalRing.maximalIdeal (AnalyticGerm n) = analyticGermMaximalIdeal n := by
    symm
    apply IsLocalRing.eq_maximalIdeal
    apply RingHom.ker_isMaximal_of_surjective
    intro z
    exact ⟨⟨Germ.ofFun (fun _ ↦ z), fun _ ↦ z, analyticAt_const, rfl⟩, rfl⟩
  intro a b hab
  obtain ⟨fa, hfa, hfarep⟩ := a.property
  let c : AnalyticGerm n :=
    ⟨Germ.ofFun (fun z ↦ fa (π z)), fun z ↦ fa (π z),
      hfa.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hac : θ a = Ideal.Quotient.mk P c := hcomp a fa hfa hfarep c rfl
  have hbc : b - c ∈ P :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem b c).mp (hab.symm.trans hac)
  have hbc' : b - c ∈ analyticGermMaximalIdeal n := by
    rw [← hmax]
    exact IsLocalRing.le_maximalIdeal hP hbc
  have hval : analyticGermValue n b = analyticGermValue n c := by
    change analyticGermValue n (b - c) = 0 at hbc'
    exact sub_eq_zero.mp (by simpa using hbc')
  rw [hval]
  change a.val.value = c.val.value
  rw [← hfarep]
  change (Germ.ofFun fa).value = (Germ.ofFun (fun z ↦ fa (π z))).value
  simp only [Germ.value_ofFun, map_zero]

private theorem adim9b_sep_distinguished_exact_bezout (n d : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (v : AnalyticGerm n) (hv : analyticGermValue n v = 0) :
    ∃ (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
      (B C : Polynomial (AnalyticGerm d)),
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      ∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T := by
  letI : P.IsPrime := hP
  letI : UniqueFactorizationMonoid (AnalyticGerm d) := spec_analyticGerm_ufd d
  letI : IsDomain (AnalyticGerm d) := {}
  letI : CharZero (AnalyticGerm d) := (analyticGermValue d).charZero
  letI : Algebra (AnalyticGerm d) (AnalyticGerm n ⧸ P) := θ.toAlgebra
  letI : Module.IsTorsionFree (AnalyticGerm d) (AnalyticGerm n ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hvint : IsIntegral (AnalyticGerm d) (Ideal.Quotient.mk P v) := hfinite.to_isIntegral _
  let Q := minpoly (AnalyticGerm d) (Ideal.Quotient.mk P v)
  have hQ : Q.Monic := minpoly.monic hvint
  have hdeg : 0 < Q.natDegree := minpoly.natDegree_pos hvint
  have hmin : ∀ T, T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T :=
    fun T ↦ minpoly.isIntegrallyClosed_dvd_iff hvint T
  have hsep : (Q.map (algebraMap (AnalyticGerm d) (FractionRing (AnalyticGerm d)))).Separable :=
    ((hQ.irreducible_iff_irreducible_map_fraction_map).mp (minpoly.irreducible hvint)).separable
  obtain ⟨δ, B, C, hδ, hBC⟩ := adim9b_sep_bezout_of_separable_fraction_map Q hdeg hsep
  obtain ⟨W, hW, hroot⟩ := adim5_distinguished_relation n d P hP.ne_top θ hfinite
    (adim9b_sep_map_preserves_germ_value n d P hP.ne_top π θ hcomp) v hv
  exact ⟨Q, δ, B, C, adim9b_sep_weierstrass_of_monic_dvd hW hQ hdeg ((hmin W).mp hroot),
    hδ, hBC, hmin⟩

/-- Primitive distinguished relation and reconstruction data with separation of a finite set. -/
theorem adim9b_primitive_form_separating (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (F : Finset (Fin n → ℂ)) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
      (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
      (R : Fin n → Polynomial (AnalyticGerm d))
      (B C : Polynomial (AnalyticGerm d)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      Set.InjOn ℓ (F : Set (Fin n → ℂ)) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      (∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T) ∧
      ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v) := by
  classical
  let A := AnalyticGerm d
  let S := AnalyticGerm n ⧸ P
  letI : P.IsPrime := hP
  letI : UniqueFactorizationMonoid A := spec_analyticGerm_ufd d
  letI : IsDomain A := {}
  letI : CharZero A := (analyticGermValue d).charZero
  letI : Algebra A S := θ.toAlgebra
  letI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  letI : Module.Finite A S := hfinite
  let K := FractionRing A
  let L := FractionRing S
  letI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr
    ((IsFractionRing.injective S L).comp hinj)
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : SMul K L := (inferInstance : Algebra K L).toSMul
  letI : Module K L := Algebra.toModule
  letI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  letI : Algebra ℂ A := (adim9b_sep_constantGerm d).toAlgebra
  letI : Algebra ℂ K := ((algebraMap A K).comp (adim9b_sep_constantGerm d)).toAlgebra
  letI : Algebra ℂ L := ((algebraMap A L).comp (adim9b_sep_constantGerm d)).toAlgebra
  letI : SMul ℂ K := (inferInstance : Algebra ℂ K).toSMul
  letI : Module ℂ K := Algebra.toModule
  letI : SMul ℂ L := (inferInstance : Algebra ℂ L).toSMul
  letI : Module ℂ L := Algebra.toModule
  letI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun z ↦ by
    change algebraMap A L (adim9b_sep_constantGerm d z) =
      algebraMap K L (algebraMap A K (adim9b_sep_constantGerm d z))
    exact IsScalarTower.algebraMap_apply A K L _
  obtain ⟨hfin, hsep, hprim⟩ := adim9b_sep_finite_fraction_extension A S K L
  letI : Module.Finite K L := hfin
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Algebra.IsSeparable K L := hsep
  letI : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L hprim
  let f : AnalyticGerm n →+* L := (algebraMap S L).comp (Ideal.Quotient.mk P)
  have hconst (z : ℂ) : f (adim9b_sep_constantGerm n z) = algebraMap ℂ L z := by
    have hz := hcomp (adim9b_sep_constantGerm d z) (fun _ ↦ z) analyticAt_const rfl
      (adim9b_sep_constantGerm n z) rfl
    change algebraMap S L (Ideal.Quotient.mk P (adim9b_sep_constantGerm n z)) =
      algebraMap S L (θ (adim9b_sep_constantGerm d z))
    rw [hz]
  let T := adim9b_sep_linearGermMap f hconst
  obtain ⟨ℓ, hsepF, hℓ, hcoords⟩ :=
    adim9b_primitive_linear_form_separating (K := K) n d π T F
  let v := adim9b_sep_linearGerm ℓ
  have hcoords' (i : Fin n) : algebraMap S L (Ideal.Quotient.mk P (c i)) ∈
      Algebra.adjoin K {algebraMap S L (Ideal.Quotient.mk P v)} := by
    have hci : c i = adim9b_sep_linearGerm (ContinuousLinearMap.proj i) := Subtype.ext (hc i)
    rw [← IntermediateField.adjoin_toSubalgebra, hci]
    exact hcoords i
  obtain ⟨a, R, ha, hR⟩ := adim9b_sep_clear_coordinates (A := A)
    (Ideal.Quotient.mk P v) (fun i ↦ Ideal.Quotient.mk P (c i)) hcoords'
  have hv : analyticGermValue n v = 0 := by
    change ℓ 0 = 0
    exact map_zero ℓ
  obtain ⟨Q, δ, B, C, hQ, hδ, hBC, hmin⟩ :=
    adim9b_sep_distinguished_exact_bezout n d P hP π θ hfinite hinj hcomp v hv
  refine ⟨ℓ, v, Q, δ * a, fun i ↦ Polynomial.C δ * R i,
    Polynomial.C a * B, Polynomial.C a * C, rfl, hsepF, hℓ, hQ,
    mul_ne_zero hδ ha, ?_, hmin, ?_⟩
  · calc
      Polynomial.C a * B * Q + Polynomial.C a * C * Q.derivative =
          Polynomial.C a * (B * Q + C * Q.derivative) := by ring
      _ = Polynomial.C (δ * a) := by rw [hBC, ← map_mul, mul_comm a δ]
  · intro i
    change θ (δ * a) * Ideal.Quotient.mk P (c i) =
      (Polynomial.C δ * R i).eval₂ θ (Ideal.Quotient.mk P v)
    have hRi : θ a * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v) := by
      simpa only [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hR i
    rw [map_mul, mul_assoc, hRi, Polynomial.eval₂_mul, Polynomial.eval₂_C]


#print axioms adim9b_sep_constantGerm
#print axioms adim9b_sep_linearGerm
#print axioms adim9b_sep_linearGermMap
#print axioms adim9b_sep_finite_fraction_extension
#print axioms adim9b_sep_bezout_of_separable_fraction_map
#print axioms adim9b_sep_clear_one_coordinate
#print axioms adim9b_sep_clear_coordinates
#print axioms adim9b_sep_weierstrass_of_monic_dvd
#print axioms adim9b_sep_map_preserves_germ_value
#print axioms adim9b_sep_distinguished_exact_bezout
#print axioms adim9b_primitive_form_separating

/-- Small evaluation of a monic complex polynomial forces a nearby root. -/
theorem adim9b_root_near_of_eval_small (q : Polynomial ℂ) (hq : q.Monic)
    (a : ℂ) (ε : ℝ) (hε : 0 < ε) (hsmall : ‖q.eval a‖ < ε ^ q.natDegree) :
    ∃ b : ℂ, q.eval b = 0 ∧ ‖a - b‖ < ε := by
  classical
  have hs := IsAlgClosed.splits q
  by_contra h
  push_neg at h
  have hfar (b : ℂ) (hb : b ∈ q.roots) : ε ≤ ‖a - b‖ :=
    h b ((Polynomial.mem_roots hq.ne_zero).mp hb)
  have hprod := Multiset.prod_map_le_prod_map₀ (fun _ : ℂ ↦ ε)
    (fun b ↦ ‖a - b‖) (fun _ _ ↦ hε.le) hfar
  have hnorm : (q.roots.map (fun b ↦ ‖a - b‖)).prod = ‖q.eval a‖ := by
    change (q.roots.map (fun b ↦ NormedField.toMulRingNorm ℂ (a - b))).prod = _
    rw [q.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun b ↦ a - b)]
    change ‖(q.roots.map (fun b ↦ a - b)).prod‖ = _
    rw [← hs.eval_eq_prod_roots_of_monic hq]
  rw [hnorm, Multiset.map_const', Multiset.prod_replicate,
    ← hs.natDegree_eq_card_roots] at hprod
  exact (not_lt_of_ge hprod) hsmall

/-- Roots of a continuous monic family of fixed degree persist near every root. -/
theorem adim9b_roots_eventually_near {W : Type*} [TopologicalSpace W]
    (q : W → Polynomial ℂ) (w₀ : W) (a : ℂ) (N : ℕ)
    (ha : (q w₀).eval a = 0)
    (hcont : ContinuousAt (fun w ↦ (q w).eval a) w₀)
    (hmonic : ∀ᶠ w in 𝓝 w₀, (q w).Monic)
    (hdegree : ∀ᶠ w in 𝓝 w₀, (q w).natDegree = N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 w₀, ∃ b : ℂ, (q w).eval b = 0 ∧ ‖a - b‖ < ε := by
  have hsmall : ∀ᶠ w in 𝓝 w₀, ‖(q w).eval a‖ < ε ^ N :=
    hcont.norm.eventually (gt_mem_nhds (by simpa only [ha, norm_zero] using pow_pos hε N))
  filter_upwards [hmonic, hdegree, hsmall] with w hm hd hs
  exact adim9b_root_near_of_eval_small (q w) hm a ε hε (by simpa only [hd] using hs)

#print axioms adim9b_root_near_of_eval_small
#print axioms adim9b_roots_eventually_near

/-- On a compact set, approximation of an image lifts at a singleton fibre. -/
theorem adim9b_mem_closure_of_compact_fibre {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (K S : Set X) (hK : IsCompact K) (hSK : S ⊆ K)
    (f : X → Y) (hf : Continuous f) (y : X)
    (hunique : ∀ z ∈ K, f z = f y → z = y)
    (himage : f y ∈ closure (f '' S)) : y ∈ closure S := by
  have hc : IsClosed (f '' (K ∩ closure S)) :=
    ((hK.inter_right isClosed_closure).image hf).isClosed
  have hsub : f '' S ⊆ f '' (K ∩ closure S) :=
    Set.image_mono (fun z hz ↦ ⟨hSK hz, subset_closure hz⟩)
  obtain ⟨z, hz, heq⟩ := (closure_minimal hsub hc) himage
  exact hunique z hz.1 heq ▸ hz.2

/-- Realization of nearby roots in a compact set gives density at a separated fibre. -/
theorem adim9b_density_of_compact_root_realization
    {X W : Type*} [TopologicalSpace X] [TopologicalSpace W] [T2Space W]
    (K : Set X) (hK : IsCompact K) (π : X → W) (ℓ : X → ℂ)
    (hπ : Continuous π) (hℓ : Continuous ℓ) (y : X)
    (hunique : ∀ z ∈ K, π z = π y → ℓ z = ℓ y → z = y)
    (G : Set W) (hG : π y ∈ closure G)
    (q : W → Polynomial ℂ) (N : ℕ)
    (hroot : (q (π y)).eval (ℓ y) = 0)
    (hcont : ContinuousAt (fun w ↦ (q w).eval (ℓ y)) (π y))
    (hmonic : ∀ᶠ w in 𝓝 (π y), (q w).Monic)
    (hdegree : ∀ᶠ w in 𝓝 (π y), (q w).natDegree = N)
    (hreal : ∀ᶠ w in 𝓝 (π y), w ∈ G → ∀ t : ℂ, (q w).eval t = 0 →
      ∃ z ∈ K, π z = w ∧ ℓ z = t) :
    y ∈ closure {z | z ∈ K ∧ π z ∈ G} := by
  let f : X → W × ℂ := fun z ↦ (π z, ℓ z)
  apply adim9b_mem_closure_of_compact_fibre K {z | z ∈ K ∧ π z ∈ G} hK
    (fun _ hz ↦ hz.1) f (hπ.prodMk hℓ) y
  · intro z hz heq
    exact hunique z hz (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  · apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hO
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
    have hnear := adim9b_roots_eventually_near q (π y) (ℓ y) N hroot hcont
      hmonic hdegree ε hε
    obtain ⟨w, hw, hwG⟩ := mem_closure_iff_nhds.mp hG _
      (inter_mem hU (inter_mem hreal hnear))
    obtain ⟨t, ht, htdist⟩ := hw.2.2
    obtain ⟨z, hzK, hzπ, hzℓ⟩ := hw.2.1 hwG t ht
    refine ⟨f z, ?_, ⟨z, ⟨hzK, hzπ ▸ hwG⟩, rfl⟩⟩
    apply hUV
    change π z ∈ U ∧ ℓ z ∈ V
    rw [hzπ, hzℓ]
    exact ⟨hw.1, hεV (by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using htdist)⟩

#print axioms adim9b_mem_closure_of_compact_fibre
#print axioms adim9b_density_of_compact_root_realization

/-- A finite family of primitive forms suffices for every tuple of a fixed length
of nonzero vectors. The family is chosen before the tuple. -/
theorem adim9b_finite_primitive_forms_avoiding_tuples
    {K L : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] (n k : ℕ)
    (T : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L) :
    ∃ F : Finset ((Fin n → ℂ) →L[ℂ] ℂ),
      (∀ ℓ ∈ F, ∀ i : Fin n,
        T (ContinuousLinearMap.proj i) ∈ IntermediateField.adjoin K {T ℓ}) ∧
      ∀ v : Fin k → (Fin n → ℂ), (∀ i, v i ≠ 0) →
        ∃ ℓ ∈ F, ∀ i, ℓ (v i) ≠ 0 := by
  classical
  let A : Set (Fin k → (Fin n → ℂ)) := {v | ∀ i, v i ∈ Metric.sphere 0 1}
  have hA : IsCompact A := isCompact_pi_infinite (fun _ ↦ isCompact_sphere 0 1)
  have hex (a : A) : ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ,
      (∀ i, ℓ (a.val i) ≠ 0) ∧ ∀ i : Fin n,
        T (ContinuousLinearMap.proj i) ∈ IntermediateField.adjoin K {T ℓ} := by
    obtain ⟨ℓ, hℓ, hc⟩ := adim9b_primitive_linear_form_avoiding (K := K) n T
      (Finset.univ.image a.val) (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        have hi := a.property i
        intro hzero
        simpa only [hzero, Metric.mem_sphere, dist_self, zero_ne_one] using hi)
    exact ⟨ℓ, fun i ↦ hℓ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hc⟩
  choose ℓ hℓ hc using hex
  let U : A → Set (Fin k → (Fin n → ℂ)) := fun a ↦ {v | ∀ i, ℓ a (v i) ≠ 0}
  have hU (a : A) : IsOpen (U a) := by
    change IsOpen {v : Fin k → (Fin n → ℂ) | ∀ i, ℓ a (v i) ≠ 0}
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i ↦ isOpen_ne.preimage
      ((ℓ a).continuous.comp (continuous_apply i)))
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover U hU (by
    intro a ha
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hℓ ⟨a, ha⟩⟩)
  refine ⟨s.image ℓ, ?_, ?_⟩
  · intro l hl
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
    exact hc a
  · intro v hv
    let u : Fin k → (Fin n → ℂ) := fun i ↦ (‖v i‖⁻¹ : ℂ) • v i
    have hu : u ∈ A := by
      intro i
      change dist ((‖v i‖⁻¹ : ℂ) • v i) 0 = 1
      rw [dist_zero_right]
      exact norm_smul_inv_norm (hv i)
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hs hu)
    obtain ⟨has, hau⟩ := Set.mem_iUnion.mp ha
    refine ⟨ℓ a, Finset.mem_image.mpr ⟨a, has, rfl⟩, ?_⟩
    intro i hzero
    apply hau i
    change ℓ a ((‖v i‖⁻¹ : ℂ) • v i) = 0
    rw [map_smul, hzero, smul_zero]

#print axioms adim9b_finite_primitive_forms_avoiding_tuples

/-- For a fixed cardinal bound, finitely many primitive forms separate every
finite set of at most that cardinality. -/
theorem adim9b_finite_primitive_forms_separating
    {K L : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] (n N : ℕ)
    (T : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L) :
    ∃ F : Finset ((Fin n → ℂ) →L[ℂ] ℂ), F.Nonempty ∧
      (∀ ℓ ∈ F, ∀ i : Fin n,
        T (ContinuousLinearMap.proj i) ∈ IntermediateField.adjoin K {T ℓ}) ∧
      ∀ S : Finset (Fin n → ℂ), S.card ≤ N →
        ∃ ℓ ∈ F, Set.InjOn ℓ (S : Set (Fin n → ℂ)) := by
  classical
  obtain ⟨F, hF, havoid⟩ := adim9b_finite_primitive_forms_avoiding_tuples (K := K) n (N * N) T
  obtain ⟨ℓ₀, _, hℓ₀⟩ := adim9b_primitive_linear_form_avoiding (K := K) n T ∅ (by simp)
  refine ⟨insert ℓ₀ F, Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro ℓ hℓ
    rcases Finset.mem_insert.mp hℓ with rfl | hℓ
    · exact hℓ₀
    · exact hF ℓ hℓ
  · intro S hS
    let D := ((S ×ˢ S).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ p.1 - p.2)
    have hD : ∀ z ∈ D, z ≠ 0 := by
      intro z hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      exact sub_ne_zero.mpr (Finset.mem_filter.mp hxy).2
    have hcard : D.card ≤ N * N := calc
      D.card ≤ ((S ×ˢ S).filter (fun p ↦ p.1 ≠ p.2)).card := Finset.card_image_le
      _ ≤ (S ×ˢ S).card := Finset.card_filter_le _ _
      _ = S.card * S.card := Finset.card_product _ _
      _ ≤ N * N := Nat.mul_le_mul hS hS
    by_cases hne : D.Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      let v : Fin (N * N) → (Fin n → ℂ) := fun i ↦
        if hi : i.val < D.card then (D.equivFin.symm ⟨i.val, hi⟩).val else z₀
      have hv : ∀ i, v i ≠ 0 := by
        intro i
        dsimp only [v]
        split_ifs with hi
        · exact hD _ (D.equivFin.symm ⟨i.val, hi⟩).property
        · exact hD z₀ hz₀
      obtain ⟨ℓ, hℓ, hℓv⟩ := havoid v hv
      have hav : ∀ z ∈ D, ℓ z ≠ 0 := by
        intro z hz
        let j := D.equivFin ⟨z, hz⟩
        have h := hℓv (Fin.castLE hcard j)
        have hj : (Fin.castLE hcard j).val < D.card := j.isLt
        simpa only [v, dif_pos hj, Fin.coe_castLE, Fin.eta, j,
          Equiv.symm_apply_apply] using h
      refine ⟨ℓ, Finset.mem_insert_of_mem hℓ, ?_⟩
      intro x hx y hy heq
      by_contra hxy
      apply hav (x - y) (Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩)
      rw [map_sub, heq, sub_self]
    · refine ⟨ℓ₀, Finset.mem_insert_self _ _, ?_⟩
      intro x hx y hy _
      by_contra hxy
      exact hne ⟨x - y, Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩⟩

#print axioms adim9b_finite_primitive_forms_separating

/-- A finite family of primitive reconstruction presentations separates all fibres
with a prescribed cardinal bound. -/
theorem adim9b_uniform_primitive_reconstruction (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (N : ℕ) :
    ∃ F : Finset ((Fin n → ℂ) →L[ℂ] ℂ), F.Nonempty ∧
      (∀ S : Finset (Fin n → ℂ), S.card ≤ N →
        ∃ ℓ ∈ F, Set.InjOn ℓ (S : Set (Fin n → ℂ))) ∧
      ∀ ℓ ∈ F, ∃ (v : AnalyticGerm n)
        (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
        (R : Fin n → Polynomial (AnalyticGerm d))
        (B C : Polynomial (AnalyticGerm d)),
        v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
        IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
        B * Q + C * Q.derivative = Polynomial.C δ ∧
        (∀ H : Polynomial (AnalyticGerm d),
          H.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ H) ∧
        ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
          (R i).eval₂ θ (Ideal.Quotient.mk P v) := by
  classical
  let A := AnalyticGerm d
  let S := AnalyticGerm n ⧸ P
  letI : P.IsPrime := hP
  letI : UniqueFactorizationMonoid A := spec_analyticGerm_ufd d
  letI : IsDomain A := {}
  letI : CharZero A := (analyticGermValue d).charZero
  letI : Algebra A S := θ.toAlgebra
  letI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  letI : Module.Finite A S := hfinite
  let K := FractionRing A
  let L := FractionRing S
  letI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr
    ((IsFractionRing.injective S L).comp hinj)
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : SMul K L := (inferInstance : Algebra K L).toSMul
  letI : Module K L := Algebra.toModule
  letI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  letI : Algebra ℂ A := (adim9b_sep_constantGerm d).toAlgebra
  letI : Algebra ℂ K := ((algebraMap A K).comp (adim9b_sep_constantGerm d)).toAlgebra
  letI : Algebra ℂ L := ((algebraMap A L).comp (adim9b_sep_constantGerm d)).toAlgebra
  letI : SMul ℂ K := (inferInstance : Algebra ℂ K).toSMul
  letI : Module ℂ K := Algebra.toModule
  letI : SMul ℂ L := (inferInstance : Algebra ℂ L).toSMul
  letI : Module ℂ L := Algebra.toModule
  letI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun z ↦ by
    change algebraMap A L (adim9b_sep_constantGerm d z) =
      algebraMap K L (algebraMap A K (adim9b_sep_constantGerm d z))
    exact IsScalarTower.algebraMap_apply A K L _
  obtain ⟨hfin, hsep, hprim⟩ := adim9b_sep_finite_fraction_extension A S K L
  letI : Module.Finite K L := hfin
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Algebra.IsSeparable K L := hsep
  letI : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L hprim
  let f : AnalyticGerm n →+* L := (algebraMap S L).comp (Ideal.Quotient.mk P)
  have hconst (z : ℂ) : f (adim9b_sep_constantGerm n z) = algebraMap ℂ L z := by
    have hz := hcomp (adim9b_sep_constantGerm d z) (fun _ ↦ z) analyticAt_const rfl
      (adim9b_sep_constantGerm n z) rfl
    change algebraMap S L (Ideal.Quotient.mk P (adim9b_sep_constantGerm n z)) =
      algebraMap S L (θ (adim9b_sep_constantGerm d z))
    rw [hz]
  let T := adim9b_sep_linearGermMap f hconst
  obtain ⟨F, hF, hcoordsF, hsepF⟩ :=
    adim9b_finite_primitive_forms_separating (K := K) n N T
  refine ⟨F, hF, hsepF, ?_⟩
  intro ℓ hℓ
  have hcoords := hcoordsF ℓ hℓ
  let v := adim9b_sep_linearGerm ℓ
  have hcoords' (i : Fin n) : algebraMap S L (Ideal.Quotient.mk P (c i)) ∈
      Algebra.adjoin K {algebraMap S L (Ideal.Quotient.mk P v)} := by
    have hci : c i = adim9b_sep_linearGerm (ContinuousLinearMap.proj i) := Subtype.ext (hc i)
    rw [← IntermediateField.adjoin_toSubalgebra, hci]
    exact hcoords i
  obtain ⟨a, R, ha, hR⟩ := adim9b_sep_clear_coordinates (A := A)
    (Ideal.Quotient.mk P v) (fun i ↦ Ideal.Quotient.mk P (c i)) hcoords'
  have hv : analyticGermValue n v = 0 := by
    change ℓ 0 = 0
    exact map_zero ℓ
  obtain ⟨Q, δ, B, C, hQ, hδ, hBC, hmin⟩ :=
    adim9b_sep_distinguished_exact_bezout n d P hP π θ hfinite hinj hcomp v hv
  refine ⟨v, Q, δ * a, fun i ↦ Polynomial.C δ * R i,
    Polynomial.C a * B, Polynomial.C a * C, rfl, hQ,
    mul_ne_zero hδ ha, ?_, hmin, ?_⟩
  · calc
      Polynomial.C a * B * Q + Polynomial.C a * C * Q.derivative =
          Polynomial.C a * (B * Q + C * Q.derivative) := by ring
      _ = Polynomial.C (δ * a) := by rw [hBC, ← map_mul, mul_comm a δ]
  · intro i
    change θ (δ * a) * Ideal.Quotient.mk P (c i) =
      (Polynomial.C δ * R i).eval₂ θ (Ideal.Quotient.mk P v)
    have hRi : θ a * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v) := by
      simpa only [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hR i
    rw [map_mul, mul_assoc, hRi, Polynomial.eval₂_mul, Polynomial.eval₂_C]


#print axioms adim9b_uniform_primitive_reconstruction

/-- Separate monic equations bound the number of simultaneous coordinate roots. -/
theorem adim9b_finite_coordinate_roots (n : ℕ) (p : Fin n → Polynomial ℂ)
    (hp : ∀ i, p i ≠ 0) :
    ∃ B : Finset (Fin n → ℂ), B.card ≤ ∏ i, (p i).natDegree ∧
      ∀ z : Fin n → ℂ, z ∈ B ↔ ∀ i, (p i).eval (z i) = 0 := by
  classical
  refine ⟨Fintype.piFinset (fun i ↦ (p i).roots.toFinset), ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    exact Finset.prod_le_prod' (fun i _ ↦
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' (p i)))
  · intro z
    simp only [Fintype.mem_piFinset, Multiset.mem_toFinset, Polynomial.mem_roots (hp _), Polynomial.IsRoot.def]

/-- Coordinate equations with uniform degree bounds give a uniform finite fibre bound. -/
theorem adim9b_finite_fibre_of_coordinate_equations {W : Type*} (n : ℕ)
    (S : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → W)
    (p : W → Fin n → Polynomial ℂ) (N : Fin n → ℕ)
    (w : W) (hp : ∀ i, p w i ≠ 0) (hdeg : ∀ i, (p w i).natDegree ≤ N i)
    (hrel : ∀ z ∈ S, π z = w → ∀ i, (p w i).eval (z i) = 0) :
    ∃ F : Finset (Fin n → ℂ), F.card ≤ ∏ i, N i ∧
      ∀ z : Fin n → ℂ, z ∈ F ↔ z ∈ S ∧ π z = w := by
  classical
  obtain ⟨B, hB, hroots⟩ := adim9b_finite_coordinate_roots n (p w) hp
  refine ⟨B.filter (fun z ↦ z ∈ S ∧ π z = w),
    (Finset.card_filter_le _ _).trans (hB.trans (Finset.prod_le_prod' (fun i _ ↦ hdeg i))), ?_⟩
  intro z
  simp only [Finset.mem_filter]
  exact ⟨fun hz ↦ hz.2, fun hz ↦ ⟨(hroots z).mpr (hrel z hz.1 hz.2), hz⟩⟩

#print axioms adim9b_finite_coordinate_roots
#print axioms adim9b_finite_fibre_of_coordinate_equations

/-- Finite analytic parameters give a uniform cardinal bound for nearby fibres. -/
theorem adim9b_uniform_fibre_bound (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (G : Finset (AnalyticGerm n)) (hG : Ideal.span (G : Set (AnalyticGerm n)) = P)
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ g, Germ.ofFun (rep g) = g.val) :
    ∃ (N : ℕ) (W : Set (Fin n → ℂ)), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧
      ∀ w : Fin d → ℂ, ∃ F : Finset (Fin n → ℂ), F.card ≤ N ∧
        ∀ z : Fin n → ℂ,
          z ∈ F ↔ z ∈ W ∧ (∀ g ∈ G, rep g z = 0) ∧ π z = w := by
  classical
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  choose Q hQ hQrel using fun i ↦
    adim9b_coordinate_weierstrass n d P hP π θ hfinite hcomp c hc i
  choose q hqm hqr using fun i ↦ adim9b_monic_representative d (Q i) (hQ i).1
  let ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun w ↦
    Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w
  have hnear : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i : Fin n,
      (∀ g ∈ G, rep g z = 0) → ((q i).map (ev (π z))).eval (z i) = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨b, hb, hbe⟩ := adim9b_eval_germ n d P π θ hcomp
      (ContinuousLinearMap.proj i) (c i) rfl (Q i) (q i) (hqr i)
    have hmem : b ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, ← hbe]
      exact hQrel i
    filter_upwards [adim9b_vanish_of_mem_span n G rep hrep b hmem _ hb.symm] with z hz
    simpa only [Polynomial.eval_map, ContinuousLinearMap.proj_apply] using hz
  obtain ⟨W, hWsub, hWopen, hW0⟩ := mem_nhds_iff.mp hnear
  refine ⟨∏ i, (q i).natDegree, W, hWopen, hW0, ?_⟩
  intro w
  obtain ⟨F, hF, hFm⟩ := adim9b_finite_fibre_of_coordinate_equations n
    {z | z ∈ W ∧ ∀ g ∈ G, rep g z = 0} π
    (fun w i ↦ (q i).map (ev w)) (fun i ↦ (q i).natDegree) w
    (fun i ↦ ((hqm i).map (ev w)).ne_zero)
    (fun i ↦ Polynomial.natDegree_map_le) (by
      intro z hz heq i
      rw [← heq]
      exact hWsub hz.1 i hz.2)
  exact ⟨F, hF, fun z ↦ (hFm z).trans (by simp only [Set.mem_setOf_eq, and_assoc])⟩

#print axioms adim9b_uniform_fibre_bound

/-- A nonzero analytic germ has dense nonvanishing locus on a connected representative. -/
theorem adim9b_dense_nonvanishing_on (d : ℕ)
    (V : Set (Fin d → ℂ)) (hV : IsOpen V) (hV0 : (0 : Fin d → ℂ) ∈ V)
    (hconn : IsPreconnected V) (δ : AnalyticGerm d) (hδ : δ ≠ 0)
    (Δ : (Fin d → ℂ) → ℂ) (hΔ : AnalyticOnNhd ℂ Δ V)
    (hrep : Germ.ofFun Δ = δ.val) :
    V ⊆ closure {w | w ∈ V ∧ Δ w ≠ 0} := by
  intro w hw
  apply mem_closure_iff_nhds.mpr
  intro O hO
  obtain ⟨B, hBO, hB, hwB⟩ := mem_nhds_iff.mp hO
  by_contra hn
  have hz : ∀ x ∈ B ∩ V, Δ x = 0 := by
    intro x hx
    by_contra hne
    exact hn ⟨x, hBO hx.1, hx.2, hne⟩
  have he : Δ =ᶠ[𝓝 w] fun _ ↦ 0 := by
    filter_upwards [(hB.inter hV).mem_nhds ⟨hwB, hw⟩] with x hx
    exact hz x hx
  have hall := hΔ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw he
  apply hδ
  apply Subtype.ext
  rw [← hrep]
  apply Germ.coe_eq.mpr
  filter_upwards [hV.mem_nhds hV0] with x hx
  exact hall hx

#print axioms adim9b_dense_nonvanishing_on

/-- The good locus of finite parameters is dense on a neighbourhood of a prime zero germ. -/
theorem adim9b_good_locus_dense_near (n d m : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n)
    (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val)
    (δ : AnalyticGerm d) (hδ : δ ≠ 0)
    (Δ : (Fin d → ℂ) → ℂ) (hΔ : AnalyticAt ℂ Δ 0)
    (hΔrep : Germ.ofFun Δ = δ.val) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, (∀ j, f j y = 0) →
        y ∈ closure {z | z ∈ W ∧ (∀ j, f j z = 0) ∧ Δ (π z) ≠ 0} := by
  classical
  choose rep hrepa hr using fun a : AnalyticGerm n ↦ a.property
  let G := Finset.univ.image g
  have hG : Ideal.span (G : Set (AnalyticGerm n)) = P := by
    simpa only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen
  have hbridge : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j, rep (g j) z = f j z :=
    Filter.eventually_all.mpr fun j ↦ Germ.coe_eq.mp ((hr (g j)).trans (hrep j).symm)
  obtain ⟨O, hOsub, hOo, hO0⟩ := mem_nhds_iff.mp hbridge
  have hzbridge (z : Fin n → ℂ) (hz : z ∈ O) :
      (∀ j, f j z = 0) ↔ (∀ a ∈ G, rep a z = 0) := by
    simp only [G, Finset.forall_mem_image, Finset.mem_univ, forall_const]
    have he : ∀ j, rep (g j) z = f j z := hOsub hz
    simp only [he]
  obtain ⟨N, H, hHo, hH0, hbound⟩ :=
    adim9b_uniform_fibre_bound n d P hP.ne_top π θ hfinite hcomp G hG rep hr
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  obtain ⟨L, -, hsep, hdata⟩ :=
    adim9b_uniform_primitive_reconstruction n d P hP π θ hfinite hinj hcomp c hc N
  let I := {ℓ // ℓ ∈ L}
  choose v Q D R B C hv hQ hD hBC hmin hcoord using fun i : I ↦ hdata i.val i.property
  choose q hqm hqr using fun i : I ↦ adim9b_monic_representative d (Q i) (hQ i).1
  choose r hrr using fun (i : I) (j : Fin n) ↦ adim9b_poly_rep d (R i j)
  choose E hEa hEr using fun i : I ↦ (D i).property
  let ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun w ↦
    Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w
  have hrelation : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i : I,
      (∀ a ∈ G, rep a z = 0) → (q i).eval₂ (ev (π z)) (i.val z) = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨b, hb, hbe⟩ := adim9b_eval_germ n d P π θ hcomp i.val (v i) (hv i)
      (Q i) (q i) (hqr i)
    have hmem : b ∈ Ideal.span (G : Set (AnalyticGerm n)) := by
      rw [hG, ← Ideal.Quotient.eq_zero_iff_mem, ← hbe]
      exact (hmin i (Q i)).mpr dvd_rfl
    exact adim9b_vanish_of_mem_span n G rep hr b hmem _ hb.symm
  obtain ⟨J, hJsub, hJo, hJ0⟩ := mem_nhds_iff.mp hrelation
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter (hHo.inter (hOo.inter hJo))).mem_nhds ⟨hU0, hH0, hO0, hJ0⟩)
  let a := ρ / 2
  have ha : 0 < a := half_pos hρ
  have hball : Metric.closedBall (0 : Fin n → ℂ) a ⊆ U ∩ (H ∩ (O ∩ J)) := by
    intro z hz
    apply hρsub
    exact lt_of_le_of_lt hz (half_lt_self hρ)
  let K := {z : Fin n → ℂ | z ∈ Metric.closedBall 0 a ∧ ∀ j, f j z = 0}
  have hK : IsCompact K := by
    have hfc : ContinuousOn (fun z ↦ fun j ↦ f j z) (Metric.closedBall 0 a) :=
      continuousOn_pi.mpr fun j ↦ (hf j).continuousOn.mono (fun z hz ↦ (hball hz).1)
    have hclosed := Metric.isClosed_closedBall.isClosed_eq hfc
      (continuousOn_const : ContinuousOn (fun _ : Fin n → ℂ ↦ (0 : Fin m → ℂ)) _)
    have hclosedK : IsClosed K := by
      simpa only [K, funext_iff, Pi.zero_apply] using hclosed
    exact (isCompact_closedBall (0 : Fin n → ℂ) a).of_isClosed_subset hclosedK
      (fun z hz ↦ hz.1)
  have hinner : Metric.ball (0 : Fin n → ℂ) a ⊆ U :=
    fun z hz ↦ (hball (Metric.ball_subset_closedBall hz)).1
  choose V hVo hV0 hroots using fun i : I ↦
    adim9b_all_roots_off_discriminant n d P hP.ne_top π θ hfinite hcomp c hc
      i.val (v i) (hv i) (Q i) (D i) (R i) (hmin i) (hcoord i)
      (q i) (E i) (r i) (fun j ↦ (hqr i j).2) (hEr i)
      (fun j k ↦ (hrr i j k).2) m g hgen f (Metric.ball 0 a)
      Metric.isOpen_ball (Metric.mem_ball_self ha) (fun j ↦ (hf j).mono hinner) hrep
  have hbase : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), AnalyticAt ℂ Δ w ∧
      ∀ i : I, w ∈ V i ∧ AnalyticAt ℂ (E i) w ∧ ∀ k, AnalyticAt ℂ ((q i).coeff k) w := by
    apply hΔ.eventually_analyticAt.and
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [(hVo i).mem_nhds (hV0 i), (hEa i).eventually_analyticAt,
      adim9b_poly_coeff_analytic_eventually d (q i) (fun k ↦ (hqr i k).1)] with w hw he hq
    exact ⟨hw, he, hq⟩
  obtain ⟨b, hb, hbsub⟩ := Metric.mem_nhds_iff.mp hbase
  let T := Metric.ball (0 : Fin d → ℂ) b
  have hTo : IsOpen T := Metric.isOpen_ball
  have hT0 : (0 : Fin d → ℂ) ∈ T := Metric.mem_ball_self hb
  let W := Metric.ball (0 : Fin n → ℂ) a ∩ π ⁻¹' T
  have hWo : IsOpen W := Metric.isOpen_ball.inter (hTo.preimage π.continuous)
  have hW0 : (0 : Fin n → ℂ) ∈ W := ⟨Metric.mem_ball_self ha, by simpa using hT0⟩
  refine ⟨W, hWo, hW0, fun z hz ↦ hinner hz.1, ?_⟩
  intro y hy hyf
  have hyK : y ∈ K := ⟨Metric.ball_subset_closedBall hy.1, hyf⟩
  obtain ⟨S, hSN, hS⟩ := hbound (π y)
  obtain ⟨ℓ, hℓ, hℓinj⟩ := hsep S hSN
  let i : I := ⟨ℓ, hℓ⟩
  have hmemS (z : Fin n → ℂ) (hz : z ∈ K) (hp : π z = π y) : z ∈ S :=
    (hS z).mpr ⟨(hball hz.1).2.1, (hzbridge z (hball hz.1).2.2.1).mp hz.2, hp⟩
  let Good := {w | w ∈ T ∧ (Δ w * E i w) ≠ 0}
  have hdense : T ⊆ closure Good := by
    apply adim9b_dense_nonvanishing_on d T hTo hT0 (convex_ball 0 b).isPreconnected
      (δ * D i) (mul_ne_zero hδ (hD i)) (fun w ↦ Δ w * E i w)
    · intro w hw
      exact (hbsub hw).1.mul ((hbsub hw).2 i).2.1
    · change Germ.ofFun (fun w ↦ Δ w * E i w) = δ.val * (D i).val
      rw [← hΔrep, ← hEr i]
      rfl
  have hdensity : y ∈ closure {z | z ∈ K ∧ π z ∈ Good} := by
    apply adim9b_density_of_compact_root_realization K hK π ℓ π.continuous ℓ.continuous y
      (fun z hz hp hl ↦ hℓinj (hmemS z hz hp) (hmemS y hyK rfl) hl)
      Good (hdense hy.2) (fun w ↦ (q i).map (ev w)) (q i).natDegree
    · rw [Polynomial.eval_map]
      exact hJsub (hball hyK.1).2.2.2 i ((hzbridge y (hball hyK.1).2.2.1).mp hyf)
    · simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
      apply tendsto_finset_sum
      intro k hk
      exact (((hbsub hy.2).2 i).2.2 k).continuousAt.mul continuousAt_const
    · exact Filter.Eventually.of_forall fun w ↦ (hqm i).map (ev w)
    · exact Filter.Eventually.of_forall fun w ↦ (hqm i).natDegree_map (ev w)
    · apply Filter.Eventually.of_forall
      intro w hw t ht
      have hE : E i w ≠ 0 := (mul_ne_zero_iff.mp hw.2).2
      obtain ⟨hz, hp, hl, hfz⟩ := hroots i w ((hbsub hw.1).2 i).1 t hE
        (by simpa only [Polynomial.eval_map] using ht)
      exact ⟨_, ⟨Metric.ball_subset_closedBall hz, hfz⟩, hp, hl⟩
  apply mem_closure_iff_nhds.mpr
  intro O hO
  obtain ⟨z, hz, hzK, hzG⟩ := mem_closure_iff_nhds.mp hdensity _
    (inter_mem hO (hWo.mem_nhds hy))
  exact ⟨z, hz.1, hz.2, hzK.2, (mul_ne_zero_iff.mp hzG.2).1⟩

#print axioms adim9b_good_locus_dense_near

/-- Dense prime points of fixed dimension bound every local component from below. -/
theorem adim9b_component_lower_of_dense_prime_locus (n e m : ℕ)
    (A Good U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U)
    (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (hdense : ∀ y ∈ U, y ∈ A → y ∈ closure (A ∩ U ∩ Good))
    (hgood : ∀ z ∈ A ∩ U ∩ Good,
      (adim2_ideal (n + 1) (adim2_germ (n + 1) A z)).IsPrime ∧
      ringKrullDim (AnalyticGerm (n + 1) ⧸
        adim2_ideal (n + 1) (adim2_germ (n + 1) A z)) = (e : WithBot ℕ∞))
    (y : Fin (n + 1) → ℂ) (hy : y ∈ U) (hyA : y ∈ A)
    (Q : Ideal (AnalyticGerm (n + 1)))
    (hQ : Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A y)).minimalPrimes) :
    (e : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) := by
  classical
  obtain ⟨s, hs⟩ := adim9b_local_equations_of_representatives (n + 1) m A y U hU hy f hf hA
  obtain ⟨F, hF, hcover⟩ := adim3_minimal_prime_cover (n + 1) s
  rw [← hs] at hF hcover
  have hQF : Q ∈ F := by
    change Q ∈ (F : Set (Ideal (AnalyticGerm (n + 1))))
    rwa [hF]
  choose rep hrepa hrep using fun a : AnalyticGerm (n + 1) ↦ a.property
  let Z : Ideal (AnalyticGerm (n + 1)) → Set (Fin (n + 1) → ℂ) :=
    fun P ↦ {z | ∀ a ∈ adim2_generators (n + 1) P, rep a z = 0}
  have hZ (P : Ideal (AnalyticGerm (n + 1))) :
      adim2_germ (n + 1) (Z P) 0 = adim2_zeroSet (n + 1) P := by
    rw [adim9b_zeroSet_eq (n + 1) rep hrep P]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z ↦ by simp only [zero_add]; rfl
  have hZQ : adim2_ideal (n + 1) (adim2_germ (n + 1) (Z Q) 0) = Q := by
    rw [hZ]
    exact adim9b_minimal_component_ideal (n + 1) _ F hF hcover Q hQF
  obtain ⟨d, π, θ, -, hfinite, hinj, hcomp, hdim⟩ :=
    adim5_finite_parameters (n + 1) Q hQ.isPrime
  have hdimQ : ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) = (d : WithBot ℕ∞) :=
    hdim.symm.trans (adim6_parameter_dimension d)
  let G := adim2_generators (n + 1) Q
  let fQ : Fin G.card → (Fin (n + 1) → ℂ) → ℂ := fun j ↦ rep (G.equivFin.symm j).val
  have han : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ P ∈ F,
      ∀ a ∈ adim2_generators (n + 1) P, AnalyticAt ℂ (rep a) z := by
    rw [Finset.eventually_all]
    intro P hPF
    rw [Finset.eventually_all]
    exact fun a ha ↦ (hrepa a).eventually_analyticAt
  have hcov : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ),
      y + z ∈ A ↔ ∃ P ∈ F, z ∈ Z P := by
    rw [adim9b_sup_zeroSet_eq (n + 1) rep hrep F] at hcover
    exact (Germ.coe_eq.mp hcover).mono fun z hz ↦ Iff.of_eq hz
  have htrans : ContinuousAt (fun z : Fin (n + 1) → ℂ ↦ y + z) 0 :=
    continuousAt_const.add continuousAt_id
  obtain ⟨H, hHsub, hHo, hH0⟩ := mem_nhds_iff.mp
    (han.and (hcov.and (htrans.preimage_mem_nhds (by simpa using hU.mem_nhds hy))))
  have hfQ : ∀ j, AnalyticOnNhd ℂ (fQ j) H :=
    fun j z hz ↦ (hHsub hz).1 Q hQF _ (G.equivFin.symm j).property
  have hAQ : ∀ z ∈ H, (z ∈ Z Q ↔ ∀ j, fQ j z = 0) := by
    intro z hz
    constructor
    · exact fun h j ↦ h _ (G.equivFin.symm j).property
    · intro h a ha
      simpa only [fQ, Equiv.symm_apply_apply] using h (G.equivFin ⟨a, ha⟩)
  obtain ⟨W, hWo, hW0, hWH, hupper⟩ := adim9b_component_dimension_upper_near n d G.card
    (Z Q) H hHo hH0 fQ hfQ hAQ (by
      intro P hP
      rw [hZQ] at hP
      have heq : P = Q := (hP.2 ⟨hQ.isPrime, le_rfl⟩ hP.le).antisymm hP.le
      rw [heq, hdimQ])
  have hfreq := adim9b_frequently_outside_other_components (n + 1) _ F hF hcover Q hQF rep hrep
  obtain ⟨t, ht, htW⟩ := (hfreq.and_eventually (hWo.mem_nhds hW0)).exists
  have htH := hWH htW
  have havoid : ∀ᶠ z in 𝓝 t, ∀ P ∈ F.erase Q, z ∉ Z P := by
    rw [Finset.eventually_all]
    intro P hP
    obtain ⟨a, ha, hane⟩ : ∃ a ∈ adim2_generators (n + 1) P, rep a t ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact ht.2 P hP hn
    have hac := ((hHsub htH).1 P (Finset.mem_of_mem_erase hP) a ha).continuousAt
    filter_upwards [hac.eventually_ne hane] with z hz hzero
    exact hz (hzero a ha)
  obtain ⟨T, hTsub, hTo, htT⟩ := mem_nhds_iff.mp
    (inter_mem (hWo.mem_nhds htW) havoid)
  have hlocal (z : Fin (n + 1) → ℂ) (hz : z ∈ T) : y + z ∈ A ↔ z ∈ Z Q := by
    rw [(hHsub (hWH (hTsub hz).1)).2.1]
    constructor
    · rintro ⟨P, hPF, hzP⟩
      by_cases heq : P = Q
      · simpa only [heq] using hzP
      · exact False.elim ((hTsub hz).2 P (Finset.mem_erase.mpr ⟨heq, hPF⟩) hzP)
    · exact fun hzQ ↦ ⟨Q, hQF, hzQ⟩
  have hytA : y + t ∈ A := (hlocal t htT).mpr ht.1
  have hytU : y + t ∈ U := (hHsub htH).2.2
  have hneigh : {z : Fin (n + 1) → ℂ | z - y ∈ T} ∈ 𝓝 (y + t) := by
    have hc : ContinuousAt (fun z : Fin (n + 1) → ℂ ↦ z - y) (y + t) :=
      continuousAt_id.sub continuousAt_const
    apply hc.preimage_mem_nhds
    simpa only [add_sub_cancel_left] using hTo.mem_nhds htT
  obtain ⟨z, hzT, hzgood⟩ := mem_closure_iff_nhds.mp (hdense (y + t) hytU hytA) _ hneigh
  obtain ⟨hp, hdimz⟩ := hgood z hzgood
  have heq : adim2_germ (n + 1) A z = adim2_germ (n + 1) (Z Q) (z - y) := by
    apply Germ.coe_eq.mpr
    have hc : ContinuousAt (fun w : Fin (n + 1) → ℂ ↦ z - y + w) 0 :=
      continuousAt_const.add continuousAt_id
    filter_upwards [hc.preimage_mem_nhds (by simpa using hTo.mem_nhds hzT)] with w hw
    apply propext
    have hh := hlocal (z - y + w) hw
    have hid : y + (z - y + w) = z + w := by abel
    simpa only [hid] using hh
  have hself : adim2_ideal (n + 1) (adim2_germ (n + 1) A z) ∈
      (adim2_ideal (n + 1) (adim2_germ (n + 1) (Z Q) (z - y))).minimalPrimes := by
    rw [← heq]
    exact ⟨⟨hp, le_rfl⟩, fun _ hI hle ↦ hI.2⟩
  have hb := hupper (z - y) (hTsub hzT).1 _ hself
  rw [hdimz, ← hdimQ] at hb
  exact hb

#print axioms adim9b_component_lower_of_dense_prime_locus

/-- Every nearby minimal component of a prime analytic germ has at least its dimension. -/
theorem adim9b_local_purity_lower (n e m : ℕ)
    (P : Ideal (AnalyticGerm (n + 1))) (hP : P.IsPrime)
    (hdim : ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (e : WithBot ℕ∞))
    (g : Fin m → AnalyticGerm (n + 1))
    (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U)
    (hU0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ W : Set (Fin (n + 1) → ℂ), IsOpen W ∧
      (0 : Fin (n + 1) → ℂ) ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, (∀ j, f j y = 0) →
        ∀ Q ∈ (adim2_ideal (n + 1)
          (adim2_germ (n + 1) {z | ∀ j, f j z = 0} y)).minimalPrimes,
          (e : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) := by
  classical
  obtain ⟨d, π, θ, -, hfinite, hinj, hcomp, hparam⟩ := adim5_finite_parameters (n + 1) P hP
  have hde : d = e := by
    have hh := (adim6_parameter_dimension d).symm.trans (hparam.trans hdim)
    exact_mod_cast hh
  subst d
  choose rep hrepa hr using fun a : AnalyticGerm (n + 1) ↦ a.property
  let G := Finset.univ.image g
  have hG : Ideal.span (G : Set (AnalyticGerm (n + 1))) = P := by
    simpa only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen
  obtain ⟨δ, Δ, hδ, hΔ, hΔrep, H, hH, hgood⟩ :=
    adim9b_off_discriminant_germ_dimension (n + 1) e P hP π θ hfinite hinj hcomp G hG rep hr
  obtain ⟨D, hDo, hD0, hDU, hdense⟩ := adim9b_good_locus_dense_near (n + 1) e m
    P hP π θ hfinite hinj hcomp g hgen f U hU hU0 hf hrep δ hδ Δ hΔ hΔrep
  have hbridge : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ j, rep (g j) z = f j z :=
    Filter.eventually_all.mpr fun j ↦ Germ.coe_eq.mp ((hr (g j)).trans (hrep j).symm)
  obtain ⟨W, hWsub, hWo, hW0⟩ :=
    mem_nhds_iff.mp (inter_mem (inter_mem hH (hDo.mem_nhds hD0)) hbridge)
  have hWD : W ⊆ D := fun z hz ↦ (hWsub hz).1.2
  have hWU : W ⊆ U := hWD.trans hDU
  have hzero (z : Fin (n + 1) → ℂ) (hz : z ∈ W) :
      (∀ j, f j z = 0) ↔ (∀ a ∈ G, rep a z = 0) := by
    simp only [G, Finset.forall_mem_image, Finset.mem_univ, forall_const]
    have he : ∀ j, rep (g j) z = f j z := (hWsub hz).2
    simp only [he]
  refine ⟨W, hWo, hW0, hWU, ?_⟩
  intro y hy hyf Q hQ
  refine adim9b_component_lower_of_dense_prime_locus n e m
    {z | ∀ j, f j z = 0} {z | Δ (π z) ≠ 0} W hWo f
    (fun j ↦ (hf j).mono hWU) (fun _ _ ↦ Iff.rfl) ?_ ?_ y hy hyf Q hQ
  · intro y hy hyf
    apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨z, hz, hzD, hzf, hzΔ⟩ := mem_closure_iff_nhds.mp (hdense y (hWD hy) hyf) _
      (inter_mem hO (hWo.mem_nhds hy))
    exact ⟨z, hz.1, ⟨hzf, hz.2⟩, hzΔ⟩
  · intro y hy
    have heq : adim2_germ (n + 1) {z | ∀ j, f j z = 0} y =
        adim2_germ (n + 1) {z | ∀ a ∈ G, rep a z = 0} y := by
      apply Germ.coe_eq.mpr
      have ht : ContinuousAt (fun z : Fin (n + 1) → ℂ ↦ y + z) 0 :=
        continuousAt_const.add continuousAt_id
      filter_upwards [ht.preimage_mem_nhds
        (by simpa using hWo.mem_nhds hy.1.2)] with z hz
      exact propext (hzero (y + z) hz)
    rw [heq]
    exact hgood y (hWsub hy.1.2).1.1 ((hzero y hy.1.2).mp hy.1.1) hy.2

#print axioms adim9b_local_purity_lower

/-- Prime analytic zero germs have representatives with constant local component dimension. -/
theorem adim9b_local_purity (n e m : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
    (g : Fin m → AnalyticGerm n)
    (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, (∀ j, f j y = 0) →
        ∀ Q ∈ (adim2_ideal n
          (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
          ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞) := by
  cases n with
  | zero =>
    have hzero (I : Ideal (AnalyticGerm 0)) (hI : I.IsPrime) :
        ringKrullDim (AnalyticGerm 0 ⧸ I) = 0 := by
      letI : I.IsPrime := hI
      apply le_antisymm
      · calc
          ringKrullDim (AnalyticGerm 0 ⧸ I) ≤ ringKrullDim (AnalyticGerm 0) :=
            ringKrullDim_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
          _ = 0 := adim6_parameter_dimension 0
      · exact ringKrullDim_nonneg_of_nontrivial
    refine ⟨U, hU, hU0, subset_rfl, ?_⟩
    intro y hy hyf Q hQ
    exact (hzero Q hQ.isPrime).trans ((hzero P hP).symm.trans hdim)
  | succ n =>
    obtain ⟨W₁, hW₁o, hW₁0, hW₁U, hupper⟩ :=
      adim9b_local_purity_upper n e m P hdim g hgen f U hU hU0 hf hrep
    obtain ⟨W₂, hW₂o, hW₂0, hW₂U, hlower⟩ :=
      adim9b_local_purity_lower n e m P hP hdim g hgen f U hU hU0 hf hrep
    refine ⟨W₁ ∩ W₂, hW₁o.inter hW₂o, ⟨hW₁0, hW₂0⟩,
      fun z hz ↦ hW₁U hz.1, ?_⟩
    intro y hy hyf Q hQ
    exact (hupper y hy.1 Q hQ).antisymm (hlower y hy.2 hyf Q hQ)

#print axioms adim9b_local_purity

#print axioms adim9b_polynomial_roots_of_germ_dvd
#print axioms adim9b_polynomial_roots_of_relation
#print axioms adim9b_linear_relation
#print axioms adim9b_clear_monomial
#print axioms adim9b_polynomial_equations_at_roots
#print axioms adim9b_linear_reconstruction
#print axioms adim9b_linear_germ_identity
#print axioms adim9b_linear_form_reconstruction
#print axioms adim9b_reconstructed_projection_and_primitive
#print axioms adim9b_monic_representative
#print axioms adim9b_coordinate_relation
#print axioms adim9b_coordinate_weierstrass
#print axioms adim9b_weierstrass_representative
#print axioms adim9b_reconstructed_coordinates_small
#print axioms adim9b_division_with_parameters
#print axioms adim9b_split_fibre
#print axioms adim9b_simultaneous_division
#print axioms adim9b_polynomial_simultaneous_division
#print axioms adim9b_parameter_pullback
#print axioms adim9b_parameter_pullback_rep
#print axioms adim9b_parameter_pullback_quotient
#print axioms adim9b_polynomial_eval_germ
#print axioms adim9b_coordinate_polynomial_rep
#print axioms adim9b_division_remainder_in_quotient
#print axioms adim9b_analytic_equation_at_roots
#print axioms adim9b_local_equations_of_representatives

#print axioms adim9b_dimH_le_of_local
#print axioms adim9b_dimH_le_of_approximatesLinearOn
#print axioms adim9b_finrank_real_pi
#print axioms adim9b_dimH_regular_zero_set
#print axioms adim9b_krullDim_drop
#print axioms adim9b_le_pred_of_succ_le
#print axioms adim9b_vanish_of_mem_span
#print axioms adim9b_poly_rep
#print axioms adim9b_eval_germ
#print axioms adim9b_polynomial_representatives_eq
#print axioms adim9b_poly_coeff_analytic_eventually
#print axioms adim9b_poly_eval_analyticAt
#print axioms adim9b_poly_deriv
#print axioms adim9b_off_discriminant_dimH
#print axioms adim9b_point_germ
#print axioms adim9b_zeroSet_eq
#print axioms adim9b_sup_zeroSet_eq
#print axioms adim9b_span_generators
#print axioms adim9b_mem_ideal_of_vanish
#print axioms adim9b_local_dimH
#print axioms adim9b_germPullback
#print axioms adim9b_germPullback_rep
#print axioms adim9b_germPullback_surjective
#print axioms adim9b_germPullback_ker
#print axioms adim9b_retractGermEquiv
#print axioms adim9b_retractGerm_dimension
#print axioms adim9b_retractGerm_prime
#print axioms adim9b_parameter_dimension_le_of_dimH
#print axioms adim9b_germ_ideal_ne_top
#print axioms adim9b_componentDimensionParts_cover
#print axioms adim9b_germPullback_leftInverse
#print axioms adim9b_germLinearEquiv
#print axioms adim9b_minimalPrime_comap_equiv
#print axioms adim9b_quotient_dimension_comap_equiv
#print axioms adim9b_ideal_linear_change
#print axioms adim9b_componentDimensionPart_linear_change
#print axioms adim9b_componentDimensionPart_scale
#print axioms adim9b_dimension_lower_of_open_projection
#print axioms adim9b_dimension_le_of_finite_parameters
#print axioms adim9b_section_of_regular_model
#print axioms adim9b_regular_model_dimension

/-- The germ at the origin of a function analytic at a point, after translating that point to the origin. -/
def adim9b_transGerm {N : ℕ} (h : (Fin N → ℂ) → ℂ) (y : Fin N → ℂ) (hy : AnalyticAt ℂ h y) :
    AnalyticGerm N :=
  ⟨Germ.ofFun (fun z ↦ h (y + z)), fun z ↦ h (y + z),
    hy.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp), rfl⟩

#print axioms adim9b_transGerm

/-- The zero germ of an ideal containing local equations of a set lies in the germ of that set. -/
theorem adim9b_zeroSet_le_germ_of_equations {N : ℕ} (Q : Ideal (AnalyticGerm N))
    (B : Set (Fin N → ℂ)) (y : Fin N → ℂ) (t : Finset ((Fin N → ℂ) → ℂ))
    (ht : ∀ h ∈ t, AnalyticAt ℂ h y)
    (hB : ∀ᶠ z in 𝓝 y, (z ∈ B ↔ ∀ h ∈ t, h z = 0))
    (hQ : ∀ h (hh : h ∈ t), adim9b_transGerm h y (ht h hh) ∈ Q) :
    adim2_zeroSet N Q ≤ adim2_germ N B y := by
  have hle : ∀ h (hh : h ∈ t),
      adim2_zeroSet N Q ≤ adim2_zero N (adim9b_transGerm h y (ht h hh)) :=
    fun h hh ↦ (adim2_galois N _ Q).mp le_rfl (hQ h hh)
  have hB' : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), (y + z ∈ B ↔ ∀ h ∈ t, h (y + z) = 0) := by
    have hc : Tendsto (fun z : Fin N → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
      have h := (tendsto_id (x := 𝓝 (0 : Fin N → ℂ))).const_add y
      rw [add_zero] at h
      exact h
    exact hc.eventually hB
  generalize adim2_zeroSet N Q = S at hle ⊢
  induction S using Filter.Germ.inductionOn with | h S =>
  have hall : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), ∀ h ∈ t, S z → h (y + z) = 0 :=
    (eventually_all_finset t).mpr fun h hh ↦ hle h hh
  change ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), S z → y + z ∈ B
  filter_upwards [hall, hB'] with z h1 h2 hS
  exact h2.mpr fun h hh ↦ h1 h hh hS

#print axioms adim9b_zeroSet_le_germ_of_equations

/-- A finite union of finite zero sets is a finite zero set, with products as equations. -/
theorem adim9b_union_zero_equations {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (F : Finset ι) (s : ι → Finset (E → ℂ))
    (hs : ∀ i ∈ F, ∀ h ∈ s i, AnalyticOnNhd ℂ h U) :
    ∃ t : Finset (E → ℂ), (∀ h ∈ t, AnalyticOnNhd ℂ h U) ∧
      ∀ z, (∀ h ∈ t, h z = 0) ↔ ∃ i ∈ F, ∀ h ∈ s i, h z = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨{fun _ ↦ 1}, ?_, ?_⟩
    · intro h hh
      rw [Finset.mem_singleton.mp hh]
      exact analyticOnNhd_const
    · intro z
      simp
  | insert i F hi ih =>
    obtain ⟨t, ht, htz⟩ := ih (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))
    refine ⟨Finset.image₂ (· * ·) (s i) t, ?_, ?_⟩
    · intro h hh
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hh
      exact (hs i (Finset.mem_insert_self i F) a ha).mul (ht b hb)
    · intro z
      constructor
      · intro H
        by_cases ha : ∀ a ∈ s i, a z = 0
        · exact ⟨i, Finset.mem_insert_self i F, ha⟩
        · push Not at ha
          obtain ⟨a, ha, haz⟩ := ha
          have hb : ∀ b ∈ t, b z = 0 := fun b hb ↦
            (mul_eq_zero.mp (H _ (Finset.mem_image₂_of_mem ha hb))).resolve_left haz
          obtain ⟨j, hj, hjz⟩ := (htz z).mp hb
          exact ⟨j, Finset.mem_insert_of_mem hj, hjz⟩
      · rintro ⟨j, hj, hjz⟩ h hh
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hh
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [hjz a ha]
        · simp [(htz z).mpr ⟨j, hj, hjz⟩ b hb]

#print axioms adim9b_union_zero_equations

/-- A minimal prime over a finite intersection is minimal over one of the intersected ideals. -/
theorem adim9b_minimalPrime_of_finset_inf {R ι : Type*} [CommRing R] (F : Finset ι)
    (J : ι → Ideal R) (Q : Ideal R) (hQ : Q ∈ (F.inf J).minimalPrimes) :
    ∃ i ∈ F, Q ∈ (J i).minimalPrimes := by
  obtain ⟨i, hi, hiQ⟩ := hQ.1.1.inf_le'.mp hQ.1.2
  exact ⟨i, hi, ⟨hQ.1.1, hiQ⟩, fun Q' hQ' hQ'Q ↦
    hQ.2 ⟨hQ'.1, (Finset.inf_le hi).trans hQ'.2⟩ hQ'Q⟩

#print axioms adim9b_minimalPrime_of_finset_inf

/-- Germs of a finite union of sets are the finite supremum of their germs. -/
theorem adim9b_finset_sup_germ {ι : Type*} (N : ℕ) (F : Finset ι)
    (S : ι → Set (Fin N → ℂ)) (y : Fin N → ℂ) :
    F.sup (fun i ↦ adim2_germ N (S i) y) = adim2_germ N {z | ∃ i ∈ F, z ∈ S i} y := by
  classical
  induction F using Finset.induction_on with
  | empty => simp; rfl
  | insert i F hi ih =>
    rw [Finset.sup_insert, ih]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by simp

#print axioms adim9b_finset_sup_germ

/-- Near the anchor, primes containing the vanishing ideal of a set whose
minimal primes all have codimension one inside a bound inherit that bound. -/
theorem adim9b_prime_dimension_drop_near (n e : ℕ) (B : Set (Fin (n + 1) → ℂ))
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (s : Finset ((Fin (n + 1) → ℂ) → ℂ)) (hs : ∀ f ∈ s, AnalyticOnNhd ℂ f U)
    (hB : ∀ z ∈ U, (z ∈ B ↔ ∀ f ∈ s, f z = 0))
    (hdim : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) B 0)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) + 1 ≤ (e : WithBot ℕ∞)) :
    ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), y ∈ B →
      ∀ Q : Ideal (AnalyticGerm (n + 1)), Q.IsPrime →
        adim2_zeroSet (n + 1) Q ≤ adim2_germ (n + 1) B y →
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) + 1 ≤ (e : WithBot ℕ∞) := by
  rcases e with _ | k
  · have htop : adim2_ideal (n + 1) (adim2_germ (n + 1) B 0) = ⊤ := by
      by_contra hne
      obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hne
      have := hP.isPrime
      have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P) :=
        ringKrullDim_nonneg_of_nontrivial
      have h1 : (0 : WithBot ℕ∞) + 1 ≤ ((0 : ℕ) : WithBot ℕ∞) :=
        (by gcongr : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P) + 1).trans
          (hdim P hP)
      simp only [zero_add, Nat.cast_zero] at h1
      exact not_le.mpr zero_lt_one h1
    have h1 : (1 : AnalyticGerm (n + 1)) ∈ adim2_ideal (n + 1) (adim2_germ (n + 1) B 0) := by
      rw [htop]
      trivial
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), 0 + z ∈ B → (1 : ℂ) = 0 at h1
    filter_upwards [h1] with y hy hyB
    exact absurd (hy (by simpa using hyB)) one_ne_zero
  · obtain ⟨H, hH, hHdim⟩ := adim9b_local_dimH n k B ⟨U, hU, hU0, s, hs, hB⟩
      (fun P hP ↦ adim9b_le_pred_of_succ_le _ k (hdim P hP))
    filter_upwards [eventually_mem_nhds_iff.mpr hH] with y hyH _ Q hQ hsub
    let B' : Set (Fin (n + 1) → ℂ) := {z | y + z ∈ B ∩ H}
    have hB' : adim2_germ (n + 1) B' 0 = adim2_germ (n + 1) B y := by
      apply Germ.coe_eq.mpr
      have ht : ContinuousAt (fun z : Fin (n + 1) → ℂ ↦ y + z) 0 :=
        continuousAt_const.add continuousAt_id
      filter_upwards [ht.preimage_mem_nhds (by simpa only [add_zero] using hyH)] with z hz
      apply propext
      rw [zero_add]
      change (y + z ∈ B ∧ y + z ∈ H) ↔ y + z ∈ B
      exact ⟨And.left, fun ha ↦ ⟨ha, hz⟩⟩
    have hle := adim9b_prime_dimension_le_of_dimH (n + 1) k B' Q hQ (hB'.symm ▸ hsub)
      ((isometry_add_left y).antilipschitzWith.dimH_preimage_le (B ∩ H) |>.trans hHdim)
    calc ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) + 1 ≤ (k : WithBot ℕ∞) + 1 :=
          by gcongr
      _ = ((k + 1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl

#print axioms adim9b_prime_dimension_drop_near

set_option linter.unusedVariables false in
/-- Near a point of a locally analytic set, local purity identifies the points
having a local component of a given dimension with the union of the zero sets
of the minimal primes of that dimension at the point. -/
theorem adim9b_local_parts_of_LP (n : ℕ)
    (hLP : ∀ (n e m : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
      (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
      (g : Fin m → AnalyticGerm n)
      (hgen : Ideal.span (Set.range g) = P)
      (f : Fin m → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
      (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
      (hrep : ∀ j, Germ.ofFun (f j) = (g j).val),
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) →
          ∀ Q ∈ (adim2_ideal n
            (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞))
    (A : Set (Fin (n + 1) → ℂ))
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    ∃ (F : Finset (Ideal (AnalyticGerm (n + 1))))
      (s : Ideal (AnalyticGerm (n + 1)) → Finset ((Fin (n + 1) → ℂ) → ℂ)),
      (∀ P ∈ F, P.IsPrime) ∧
      (∀ P ∈ F, adim2_ideal (n + 1)
        (adim2_germ (n + 1) {z | ∀ h ∈ s P, h z = 0} 0) = P) ∧
      ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), (∀ P ∈ F, ∀ h ∈ s P, AnalyticAt ℂ h y) ∧
        ∀ d : ℕ, ((y ∈ A ∧ ∃ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A y)).minimalPrimes,
            ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) = (d : WithBot ℕ∞)) ↔
          ∃ P ∈ F, ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) ∧
            ∀ h ∈ s P, h y = 0) := by
  classical
  obtain ⟨s0, hs0⟩ := adim9b_local_equations_of_representatives (n + 1) m A 0 U hU hU0 f hf hA
  obtain ⟨F, hF, hcover⟩ := adim3_minimal_prime_cover (n + 1) s0
  rw [← hs0] at hF hcover
  choose rep hrepa hrep using fun g : AnalyticGerm (n + 1) ↦ g.property
  let s : Ideal (AnalyticGerm (n + 1)) → Finset ((Fin (n + 1) → ℂ) → ℂ) :=
    fun P ↦ (adim2_generators (n + 1) P).image rep
  let Z : Ideal (AnalyticGerm (n + 1)) → Set (Fin (n + 1) → ℂ) :=
    fun P ↦ {z | ∀ h ∈ s P, h z = 0}
  have hFmin : ∀ P ∈ F, P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A 0)).minimalPrimes := by
    intro P hP
    rw [← hF]
    exact hP
  have hFprime : ∀ P ∈ F, P.IsPrime := fun P hP ↦ (hFmin P hP).isPrime
  have hZgerm : ∀ P, adim2_germ (n + 1) (Z P) 0 = adim2_zeroSet (n + 1) P := by
    intro P
    rw [adim9b_zeroSet_eq (n + 1) rep hrep P]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z ↦ by
      simp only [Z, s, zero_add, Set.mem_ofPred_eq, Finset.forall_mem_image]
  have hZideal : ∀ P ∈ F, adim2_ideal (n + 1) (adim2_germ (n + 1) (Z P) 0) = P := by
    intro P hP
    rw [hZgerm]
    exact adim9b_minimal_component_ideal (n + 1) _ F hF hcover P hP
  have hdimP : ∀ P ∈ F, ∃ e : ℕ,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (e : WithBot ℕ∞) := by
    intro P hP
    obtain ⟨d, -, -, -, -, -, -, hd⟩ := adim5_finite_parameters (n + 1) P (hFprime P hP)
    exact ⟨d, hd.symm.trans (adim6_parameter_dimension d)⟩
  choose! e he using hdimP
  have hcov0 : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), (z ∈ A ↔ ∃ P ∈ F, z ∈ Z P) := by
    have h := Germ.coe_eq.mp (hcover.trans (adim9b_sup_zeroSet_eq (n + 1) rep hrep F))
    filter_upwards [h] with z hz
    have hz' : (0 + z ∈ A) = ∃ P ∈ F, ∀ g ∈ adim2_generators (n + 1) P, rep g z = 0 := hz
    rw [zero_add] at hz'
    rw [hz']
    simp only [Z, s, Set.mem_ofPred_eq, Finset.forall_mem_image]
  have han : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ P ∈ F, ∀ h ∈ s P, AnalyticAt ℂ h y := by
    refine (eventually_all_finset F).mpr fun P _ ↦ (eventually_all_finset (s P)).mpr ?_
    intro h hh
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hh
    exact (hrepa g).eventually_analyticAt
  obtain ⟨V, hVsub, hV, hV0⟩ := mem_nhds_iff.mp han
  have hsV : ∀ P ∈ F, ∀ h ∈ s P, AnalyticOnNhd ℂ h V :=
    fun P hP h hh y hy ↦ hVsub hy P hP h hh
  have hlp : ∀ P ∈ F, ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), y ∈ Z P →
      ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) (Z P) y)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) = (e P : WithBot ℕ∞) := by
    intro P hP
    let G := adim2_generators (n + 1) P
    let g : Fin G.card → AnalyticGerm (n + 1) := fun j ↦ (G.equivFin.symm j).val
    have hrange : Set.range g = (G : Set (AnalyticGerm (n + 1))) := by
      ext b
      constructor
      · rintro ⟨j, rfl⟩
        exact (G.equivFin.symm j).property
      · intro hb
        exact ⟨G.equivFin ⟨b, hb⟩, by simp [g]⟩
    have hg : Ideal.span (Set.range g) = P := by
      rw [hrange]
      exact adim9b_span_generators (n + 1) P
    have hset : {z | ∀ j, rep (g j) z = 0} = Z P := by
      ext z
      constructor
      · intro hz h hh
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
        simpa [g] using hz (G.equivFin ⟨b, hb⟩)
      · intro hz j
        exact hz _ (Finset.mem_image_of_mem rep (G.equivFin.symm j).property)
    obtain ⟨W, hW, hW0, -, hWlp⟩ := hLP (n + 1) (e P) G.card P (hFprime P hP) (he P hP) g hg
      (fun j ↦ rep (g j)) V hV hV0
      (fun j ↦ hsV P hP _ (Finset.mem_image_of_mem rep (G.equivFin.symm j).property))
      (fun j ↦ hrep (g j))
    filter_upwards [hW.mem_nhds hW0] with y hy hyZ
    rw [← hset] at hyZ ⊢
    exact hWlp y hy hyZ
  have hT : ∀ P ∈ F, ∀ P' ∈ F, ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), P' ≠ P →
      y ∈ Z P ∩ Z P' → ∀ Q : Ideal (AnalyticGerm (n + 1)), Q.IsPrime →
        adim2_zeroSet (n + 1) Q ≤ adim2_germ (n + 1) (Z P ∩ Z P') y →
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) + 1 ≤ (e P : WithBot ℕ∞) := by
    intro P hP P' hP'
    by_cases hPP : P' = P
    · exact Eventually.of_forall fun y h ↦ absurd hPP h
    have hev := adim9b_prime_dimension_drop_near n (e P) (Z P ∩ Z P') V hV hV0 (s P ∪ s P')
      (by
        intro h hh
        rcases Finset.mem_union.mp hh with hh | hh
        · exact hsV P hP h hh
        · exact hsV P' hP' h hh)
      (by
        intro z _
        simp only [Z, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.forall_mem_union])
      (by
        intro Q hQ
        have hanti : ∀ (S T : adim2_SetGerm (n + 1)), S ≤ T →
            adim2_ideal (n + 1) T ≤ adim2_ideal (n + 1) S := fun S T hST a ha ↦ hST.trans ha
        have hPQ : P ≤ Q := by
          rw [← hZideal P hP]
          refine (hanti _ _ ?_).trans hQ.1.2
          exact Germ.coe_le.mpr (Eventually.of_forall fun z hz ↦ hz.1)
        have hP'Q : P' ≤ Q := by
          rw [← hZideal P' hP']
          refine (hanti _ _ ?_).trans hQ.1.2
          exact Germ.coe_le.mpr (Eventually.of_forall fun z hz ↦ hz.2)
        have hnot : ¬ P' ≤ P := fun hle ↦
          hPP (hle.antisymm ((hFmin P hP).2 (hFmin P' hP').1 hle))
        obtain ⟨b, hbP', hbP⟩ := Set.not_subset.mp hnot
        have := hFprime P hP
        rw [← he P hP]
        exact adim9b_krullDim_drop P Q hPQ b hbP (hP'Q hbP'))
    filter_upwards [hev] with y hy _ hyT
    exact hy hyT
  have hlp' := (eventually_all_finset F).mpr hlp
  have hT' : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ P ∈ F, ∀ P' ∈ F, P' ≠ P →
      y ∈ Z P ∩ Z P' → ∀ Q : Ideal (AnalyticGerm (n + 1)), Q.IsPrime →
        adim2_zeroSet (n + 1) Q ≤ adim2_germ (n + 1) (Z P ∩ Z P') y →
        ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) + 1 ≤ (e P : WithBot ℕ∞) :=
    (eventually_all_finset F).mpr fun P hP ↦ (eventually_all_finset F).mpr (hT P hP)
  refine ⟨F, s, hFprime, hZideal, ?_⟩
  filter_upwards [han, hcov0.eventually_nhds, hlp', hT'] with y hyan hycov hylp hyT
  refine ⟨hyan, ?_⟩
  have hgermA : adim2_germ (n + 1) A y = F.sup (fun P ↦ adim2_germ (n + 1) (Z P) y) := by
    rw [adim9b_finset_sup_germ]
    apply Germ.coe_eq.mpr
    have hc : Tendsto (fun z : Fin (n + 1) → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
      have h := (tendsto_id (x := 𝓝 (0 : Fin (n + 1) → ℂ))).const_add y
      rw [add_zero] at h
      exact h
    filter_upwards [hc.eventually hycov] with z hz
    exact propext hz
  have hIA : adim2_ideal (n + 1) (adim2_germ (n + 1) A y) =
      F.inf (fun P ↦ adim2_ideal (n + 1) (adim2_germ (n + 1) (Z P) y)) := by
    rw [hgermA, adim9b_ideal_finset_sup]
  have hstep : ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A y)).minimalPrimes,
      ∃ P ∈ F, Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) (Z P) y)).minimalPrimes ∧
        y ∈ Z P ∧ ringKrullDim (AnalyticGerm (n + 1) ⧸ Q) = (e P : WithBot ℕ∞) := by
    intro Q hQ
    rw [hIA] at hQ
    obtain ⟨P, hP, hQP⟩ := adim9b_minimalPrime_of_finset_inf F _ Q hQ
    have hyZ : y ∈ Z P := by
      by_contra hyZ
      simp only [Z, Set.mem_ofPred_eq, not_forall] at hyZ
      obtain ⟨h, hh, hhy⟩ := hyZ
      have hev : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), h (y + z) ≠ 0 := by
        have hc : ContinuousAt (fun z : Fin (n + 1) → ℂ ↦ h (y + z)) 0 :=
          ((hyan P hP h hh).continuousAt).comp_of_eq
            (continuousAt_const.add continuousAt_id) (by simp)
        exact hc.eventually_ne (by simpa using hhy)
      have h1 : (1 : AnalyticGerm (n + 1)) ∈
          adim2_ideal (n + 1) (adim2_germ (n + 1) (Z P) y) := by
        change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), y + z ∈ Z P → (1 : ℂ) = 0
        filter_upwards [hev] with z hz hzZ
        exact absurd (hzZ h hh) hz
      exact hQP.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr (hQP.1.2 h1))
    exact ⟨P, hP, hQP, hyZ, hylp P hP hyZ Q hQP⟩
  intro d
  constructor
  · rintro ⟨-, Q, hQ, hQd⟩
    obtain ⟨P, hP, -, hyZ, hQe⟩ := hstep Q hQ
    exact ⟨P, hP, (he P hP).trans (hQe.symm.trans hQd), hyZ⟩
  · rintro ⟨P, hP, hPd, hyZ⟩
    have hyA : y ∈ A := hycov.self_of_nhds.mpr ⟨P, hP, hyZ⟩
    refine ⟨hyA, ?_⟩
    obtain ⟨Q', hQ'⟩ := Ideal.nonempty_minimalPrimes
      (adim9b_germ_ideal_ne_top (n + 1) (Z P) y hyZ)
    have hQ'e := hylp P hP hyZ Q' hQ'
    have hIQ' : adim2_ideal (n + 1) (adim2_germ (n + 1) A y) ≤ Q' := by
      rw [hIA]
      exact (Finset.inf_le hP).trans hQ'.1.2
    have := hQ'.1.1
    obtain ⟨Q, hQ, hQQ'⟩ := Ideal.exists_minimalPrimes_le hIQ'
    obtain ⟨P0, hP0, hQP0, hyZ0, -⟩ := hstep Q hQ
    by_cases hP0P : P0 = P
    · rw [hP0P] at hQP0
      have hQeq : Q = Q' := hQQ'.antisymm (hQ'.2 hQP0.1 hQQ')
      refine ⟨Q, hQ, ?_⟩
      rw [hQeq, hQ'e, ← he P hP, hPd]
    · exfalso
      have hsub : adim2_zeroSet (n + 1) Q' ≤ adim2_germ (n + 1) (Z P ∩ Z P0) y := by
        refine adim9b_zeroSet_le_germ_of_equations Q' _ y (s P ∪ s P0) ?_
          (Eventually.of_forall fun z ↦ by
            simp only [Z, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.forall_mem_union]) ?_
        · intro h hh
          rcases Finset.mem_union.mp hh with hh | hh
          · exact hyan P hP h hh
          · exact hyan P0 hP0 h hh
        · intro h hh
          rcases Finset.mem_union.mp hh with hh' | hh'
          · apply hQ'.1.2
            change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), y + z ∈ Z P → h (y + z) = 0
            exact Eventually.of_forall fun z hz ↦ hz h hh'
          · apply hQQ'
            apply hQP0.1.2
            change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), y + z ∈ Z P0 → h (y + z) = 0
            exact Eventually.of_forall fun z hz ↦ hz h hh'
      have hbad := hyT P hP P0 hP0 hP0P ⟨hyZ, hyZ0⟩ Q' hQ'.1.1 hsub
      rw [hQ'e] at hbad
      have h2 : e P + 1 ≤ e P := by exact_mod_cast hbad
      omega

#print axioms adim9b_local_parts_of_LP

set_option linter.unusedVariables false in
/-- Near every point of the cone, local purity gives finite analytic equations
for each component-dimension part. -/
theorem adim9b_componentDimensionPart_equations_near_of_LP (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hLP : ∀ (n e m : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
      (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
      (g : Fin m → AnalyticGerm n)
      (hgen : Ideal.span (Set.range g) = P)
      (f : Fin m → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
      (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
      (hrep : ∀ j, Germ.ofFun (f j) = (g j).val),
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) →
          ∀ Q ∈ (adim2_ideal n
            (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞))
    (d : ℕ) :
    ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ adim9_componentDimensionPart n C d ↔ ∀ j, f j z = 0) := by
  classical
  intro x hx
  obtain ⟨U, hU, hxU, hU0, m, f, hf, hC⟩ := hloc x hx
  let U' : Set (Fin (n + 1) → ℂ) := (fun z ↦ x + z) ⁻¹' U
  have hU' : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have h0U' : (0 : Fin (n + 1) → ℂ) ∈ U' := by simpa [U'] using hxU
  obtain ⟨F, s, -, -, hev⟩ := adim9b_local_parts_of_LP n hLP {z | x + z ∈ C} U' hU' h0U' m
    (fun j z ↦ f j (x + z))
    (fun j z hz ↦ (hf j (x + z) hz).comp_of_eq (analyticAt_const.add analyticAt_id) rfl)
    (fun z hz ↦ hC (x + z) hz)
  obtain ⟨W, hWsub, hW, hW0⟩ := mem_nhds_iff.mp (hev.and (hU'.mem_nhds h0U'))
  obtain ⟨t, ht, htz⟩ := adim9b_union_zero_equations W (F.filter fun P ↦
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞)) s
    (fun P hP h hh y hy ↦ (hWsub hy).1.1 P (Finset.mem_filter.mp hP).1 h hh)
  refine ⟨(fun z ↦ z - x) ⁻¹' W, hW.preimage (continuous_id.sub continuous_const),
    by simpa using hW0, ?_, t.card, fun j z ↦ (t.equivFin.symm j).val (z - x), ?_, ?_⟩
  · intro z hz
    have hzU : x + (z - x) ∈ U := (hWsub hz).2
    rw [add_sub_cancel] at hzU
    exact hU0 hzU
  · intro j z hz
    exact (ht _ (t.equivFin.symm j).property (z - x) hz).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  · intro z hz
    have hy := (hWsub hz).1.2 d
    have hgerm : adim2_germ (n + 1) C z =
        adim2_germ (n + 1) {w | x + w ∈ C} (z - x) := by
      unfold adim2_germ
      congr 1
      funext w
      rw [Set.mem_ofPred_eq, ← add_assoc, add_sub_cancel]
    have hzC : z ∈ C ↔ z - x ∈ {w | x + w ∈ C} := by
      rw [Set.mem_ofPred_eq, add_sub_cancel]
    rw [adim9_mem_componentDimensionPart_iff, hgerm, hzC, hy]
    constructor
    · rintro ⟨P, hP, hPd, hPz⟩ j
      exact (htz (z - x)).mpr ⟨P, Finset.mem_filter.mpr ⟨hP, hPd⟩, hPz⟩ _
        (t.equivFin.symm j).property
    · intro hj
      obtain ⟨P, hP, hPz⟩ := (htz (z - x)).mp fun h hh ↦ by
        simpa using hj (t.equivFin ⟨h, hh⟩)
      exact ⟨P, (Finset.mem_filter.mp hP).1, (Finset.mem_filter.mp hP).2, hPz⟩

#print axioms adim9b_componentDimensionPart_equations_near_of_LP

set_option linter.unusedVariables false in
/-- Local analyticity of a component-dimension part, from local purity. -/
theorem adim9b_componentDimensionPart_locally_analytic_of_LP (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hLP : ∀ (n e m : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
      (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
      (g : Fin m → AnalyticGerm n)
      (hgen : Ideal.span (Set.range g) = P)
      (f : Fin m → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
      (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
      (hrep : ∀ j, Germ.ofFun (f j) = (g j).val),
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) →
          ∀ Q ∈ (adim2_ideal n
            (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞))
    (d : ℕ) :
    ∀ x ∈ adim9_componentDimensionPart n C d,
      ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
        U ⊆ {z | z ≠ 0} ∧
        ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
          (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
          ∀ z ∈ U, (z ∈ adim9_componentDimensionPart n C d ↔ ∀ j, f j z = 0) :=
  fun x hx ↦ adim9b_componentDimensionPart_equations_near_of_LP n C hloc hLP d x hx.1

#print axioms adim9b_componentDimensionPart_locally_analytic_of_LP

set_option linter.unusedVariables false in
/-- A component-dimension part is closed in the punctured space, from local purity. -/
theorem adim9b_componentDimensionPart_closed_of_LP (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hLP : ∀ (n e m : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
      (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
      (g : Fin m → AnalyticGerm n)
      (hgen : Ideal.span (Set.range g) = P)
      (f : Fin m → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
      (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
      (hrep : ∀ j, Germ.ofFun (f j) = (g j).val),
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) →
          ∀ Q ∈ (adim2_ideal n
            (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞))
    (d : ℕ) :
    IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} |
      z.val ∈ adim9_componentDimensionPart n C d} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  by_cases hzC : z.val ∈ C
  · obtain ⟨U, hU, hzU, -, m, f, hf, hiff⟩ :=
      adim9b_componentDimensionPart_equations_near_of_LP n C hloc hLP d z.val hzC
    have hnot : ¬ ∀ j, f j z.val = 0 := fun h ↦ hz ((hiff z.val hzU).mpr h)
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    refine ⟨Subtype.val ⁻¹' (U ∩ f j ⁻¹' {0}ᶜ), ?_, ?_, ⟨hzU, hj⟩⟩
    · rintro w ⟨hwU, hwj⟩ hw
      exact hwj ((hiff w.val hwU).mp hw j)
    · exact ((hf j).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).preimage
        continuous_subtype_val
  · exact ⟨{w | w.val ∉ C}, fun w hw hw' ↦ hw hw'.1, hclosed.isOpen_compl, hzC⟩

#print axioms adim9b_componentDimensionPart_closed_of_LP

set_option linter.unusedVariables false in
/-- Purity of a component-dimension part, from local purity. -/
theorem adim9b_componentDimensionPart_pure_of_LP (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hLP : ∀ (n e m : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
      (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
      (g : Fin m → AnalyticGerm n)
      (hgen : Ideal.span (Set.range g) = P)
      (f : Fin m → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
      (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
      (hrep : ∀ j, Germ.ofFun (f j) = (g j).val),
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) →
          ∀ Q ∈ (adim2_ideal n
            (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞))
    (d : ℕ) :
    ∀ x ∈ adim9_componentDimensionPart n C d,
      ∀ P ∈ (adim2_ideal (n + 1)
        (adim2_germ (n + 1) (adim9_componentDimensionPart n C d) x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) := by
  classical
  intro x hx Q hQ
  obtain ⟨U, hU, hxU, -, m, f, hf, hC⟩ := hloc x hx.1
  let U' : Set (Fin (n + 1) → ℂ) := (fun z ↦ x + z) ⁻¹' U
  have hU' : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have h0U' : (0 : Fin (n + 1) → ℂ) ∈ U' := by simpa [U'] using hxU
  obtain ⟨F, s, hFprime, hZideal, hev⟩ := adim9b_local_parts_of_LP n hLP {z | x + z ∈ C}
    U' hU' h0U' m (fun j z ↦ f j (x + z))
    (fun j z hz ↦ (hf j (x + z) hz).comp_of_eq (analyticAt_const.add analyticAt_id) rfl)
    (fun z hz ↦ hC (x + z) hz)
  let F' := F.filter fun P ↦ ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞)
  have hgerm : adim2_germ (n + 1) (adim9_componentDimensionPart n C d) x =
      F'.sup (fun P ↦ adim2_germ (n + 1) {z | ∀ h ∈ s P, h z = 0} 0) := by
    rw [adim9b_finset_sup_germ]
    apply Germ.coe_eq.mpr
    filter_upwards [hev] with w hw
    apply propext
    rw [zero_add]
    change x + w ∈ adim9_componentDimensionPart n C d ↔
      ∃ P ∈ F', ∀ h ∈ s P, h w = 0
    have hg : adim2_germ (n + 1) C (x + w) = adim2_germ (n + 1) {z | x + z ∈ C} w := by
      unfold adim2_germ
      congr 1
      funext v
      rw [Set.mem_ofPred_eq, add_assoc]
    rw [adim9_mem_componentDimensionPart_iff, hg]
    refine (hw.2 d).trans ?_
    constructor
    · rintro ⟨P, hP, hPd, hPz⟩
      exact ⟨P, Finset.mem_filter.mpr ⟨hP, hPd⟩, hPz⟩
    · rintro ⟨P, hP, hPz⟩
      exact ⟨P, (Finset.mem_filter.mp hP).1, (Finset.mem_filter.mp hP).2, hPz⟩
  rw [hgerm, adim9b_ideal_finset_sup] at hQ
  obtain ⟨P, hP, hQP⟩ := adim9b_minimalPrime_of_finset_inf F' _ Q hQ
  obtain ⟨hPF, hPd⟩ := Finset.mem_filter.mp hP
  rw [hZideal P hPF] at hQP
  have hQeq : Q = P := (hQP.2 ⟨hFprime P hPF, le_rfl⟩ hQP.1.2).antisymm hQP.1.2
  rw [hQeq]
  exact hPd

#print axioms adim9b_componentDimensionPart_pure_of_LP

set_option linter.unusedVariables false in
/-- The conclusion of `adim9_cone_pure_cover_aux` from its premises and local purity:
the nonempty component-dimension parts, with dimensions shifted down by one. -/
theorem adim9b_cone_pure_cover_of_LP (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hLP : ∀ (n e m : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
      (hdim : ringKrullDim (AnalyticGerm n ⧸ P) = (e : WithBot ℕ∞))
      (g : Fin m → AnalyticGerm n)
      (hgen : Ideal.span (Set.range g) = P)
      (f : Fin m → (Fin n → ℂ) → ℂ)
      (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
      (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
      (hrep : ∀ j, Germ.ofFun (f j) = (g j).val),
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
        ∀ y ∈ W, (∀ j, f j y = 0) →
          ∀ Q ∈ (adim2_ideal n
            (adim2_germ n {z | ∀ j, f j z = 0} y)).minimalPrimes,
            ringKrullDim (AnalyticGerm n ⧸ Q) = (e : WithBot ℕ∞)) :
    ∃ (k : ℕ) (Cι : Fin k → Set (Fin (n + 1) → ℂ)) (dι : Fin k → ℕ),
      insert 0 C = ⋃ i, insert 0 (Cι i) ∧
      ∀ i, Cι i ⊆ C ∧ dι i ≤ n ∧
        (0 : Fin (n + 1) → ℂ) ∉ Cι i ∧ (Cι i).Nonempty ∧
        IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ Cι i} ∧
        (∀ (t : ℂ), t ≠ 0 → ∀ z ∈ Cι i, t • z ∈ Cι i) ∧
        (∀ x ∈ Cι i, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
          U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
            (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
            ∀ z ∈ U, (z ∈ Cι i ↔ ∀ j, f j z = 0)) ∧
        ∀ x ∈ Cι i,
          ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) (Cι i) x)).minimalPrimes,
            ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((dι i + 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have hfin := adim9_nonempty_componentDimensionParts_finite n C hzero hclosed hscale hloc
  let D := hfin.toFinset
  have hcov := adim9b_componentDimensionParts_cover n C hzero hclosed hscale hloc
  refine ⟨D.card, fun i ↦ adim9_componentDimensionPart n C (D.equivFin.symm i).val,
    fun i ↦ (D.equivFin.symm i).val - 1, ?_, ?_⟩
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_iUnion]
    constructor
    · rintro (rfl | hz)
      · obtain ⟨x, hx⟩ := hne
        rw [hcov] at hx
        obtain ⟨d, -, hd⟩ := mem_iUnion₂.mp hx
        have hdD : d ∈ D := hfin.mem_toFinset.mpr ⟨x, hd⟩
        exact ⟨D.equivFin ⟨d, hdD⟩, Or.inl rfl⟩
      · rw [hcov] at hz
        obtain ⟨d, -, hd⟩ := mem_iUnion₂.mp hz
        have hdD : d ∈ D := hfin.mem_toFinset.mpr ⟨z, hd⟩
        exact ⟨D.equivFin ⟨d, hdD⟩, Or.inr (by simpa using hd)⟩
    · rintro ⟨i, rfl | hz⟩
      · exact Or.inl rfl
      · exact Or.inr hz.1
  · intro i
    beta_reduce
    generalize D.equivFin.symm i = p
    obtain ⟨d, hdD⟩ := p
    have hne' : (adim9_componentDimensionPart n C d).Nonempty := hfin.mem_toFinset.mp hdD
    obtain ⟨hd1, hdn⟩ :=
      adim9_nonempty_componentDimensionPart_bounds n C hzero hclosed hscale hloc d hne'
    have hd' : d - 1 + 1 = d := by omega
    refine ⟨adim9_componentDimensionPart_subset n C d, show d - 1 ≤ n by omega,
      adim9_zero_not_mem_componentDimensionPart n C hzero d, hne',
      adim9b_componentDimensionPart_closed_of_LP n C hzero hclosed hscale hloc hLP d,
      fun t ht z hz ↦ adim9b_componentDimensionPart_scale n d C hscale t ht z hz,
      adim9b_componentDimensionPart_locally_analytic_of_LP n C hzero hclosed hscale hloc hLP d,
      ?_⟩
    change ∀ x ∈ adim9_componentDimensionPart n C d, ∀ P ∈ _, _ = ((d - 1 + 1 : ℕ) : WithBot ℕ∞)
    rw [hd']
    exact adim9b_componentDimensionPart_pure_of_LP n C hzero hclosed hscale hloc hLP d

#print axioms adim9b_cone_pure_cover_of_LP

/-- Each pure-dimensional part of a punctured homogeneous cone is again a
punctured homogeneous cone, and finitely many such parts cover the cone.
Source: Gunning--Rossi, III.C and III.D, decomposition of an analytic set into
irreducible components and its pure-dimensional parts; Chirka, Complex Analytic
Sets, §5.4, pure-dimensional parts; Griffiths--Harris, Chapter 1 §3, cones. -/
theorem adim9_cone_pure_cover_aux (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    ∃ (k : ℕ) (Cι : Fin k → Set (Fin (n + 1) → ℂ)) (dι : Fin k → ℕ),
      insert 0 C = ⋃ i, insert 0 (Cι i) ∧
      ∀ i, Cι i ⊆ C ∧ dι i ≤ n ∧
        (0 : Fin (n + 1) → ℂ) ∉ Cι i ∧ (Cι i).Nonempty ∧
        IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ Cι i} ∧
        (∀ (t : ℂ), t ≠ 0 → ∀ z ∈ Cι i, t • z ∈ Cι i) ∧
        (∀ x ∈ Cι i, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
          U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
            (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
            ∀ z ∈ U, (z ∈ Cι i ↔ ∀ j, f j z = 0)) ∧
        ∀ x ∈ Cι i,
          ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) (Cι i) x)).minimalPrimes,
            ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((dι i + 1 : ℕ) : WithBot ℕ∞) := by
  exact adim9b_cone_pure_cover_of_LP n C hzero hne hclosed hscale hloc adim9b_local_purity

/-- Pullback of analytic germs along a linear map. -/
private def adim9_pb {n d : ℕ}
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) : AnalyticGerm d →+* AnalyticGerm n := by
  have ht : Tendsto π (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using π.continuous.continuousAt (x := 0)
  let t : Germ (𝓝 (0 : Fin d → ℂ)) ℂ →+* Germ (𝓝 (0 : Fin n → ℂ)) ℂ :=
    { toFun := fun g ↦ g.compTendsto π ht
      map_one' := rfl
      map_zero' := rfl
      map_mul' := fun g h ↦ Germ.inductionOn g fun _ ↦ Germ.inductionOn h fun _ ↦ rfl
      map_add' := fun g h ↦ Germ.inductionOn g fun _ ↦ Germ.inductionOn h fun _ ↦ rfl }
  refine
    { toFun := fun a ↦ ⟨t a.val, ?_⟩
      map_one' := Subtype.ext t.map_one
      map_zero' := Subtype.ext t.map_zero
      map_mul' := fun a b ↦ Subtype.ext (t.map_mul a.val b.val)
      map_add' := fun a b ↦ Subtype.ext (t.map_add a.val b.val) }
  obtain ⟨f, hf, hrep⟩ := a.property
  refine ⟨fun z ↦ f (π z), hf.comp_of_eq (π.analyticAt 0) (map_zero _), ?_⟩
  change _ = a.val.compTendsto π ht
  rw [← hrep]
  rfl

private theorem adim9_pb_rep {n d : ℕ}
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ) (hrep : Germ.ofFun f = a.val) :
    Germ.ofFun (fun z ↦ f (π z)) = (adim9_pb π a).val := by
  change _ = a.val.compTendsto π (by
    simpa only [ContinuousAt, map_zero] using π.continuous.continuousAt (x := 0))
  rw [← hrep]
  rfl

private theorem adim9_pb_pb {n m k : ℕ} (A : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ))
    (B : (Fin m → ℂ) →L[ℂ] (Fin k → ℂ)) (a : AnalyticGerm k) :
    adim9_pb A (adim9_pb B a) = adim9_pb (B.comp A) a := by
  obtain ⟨f, -, hrep⟩ := a.property
  apply Subtype.ext
  rw [← adim9_pb_rep A _ _ (adim9_pb_rep B a f hrep), ← adim9_pb_rep (B.comp A) a f hrep]
  rfl

private theorem adim9_pb_id {n : ℕ} (a : AnalyticGerm n) :
    adim9_pb (ContinuousLinearMap.id ℂ (Fin n → ℂ)) a = a := by
  obtain ⟨f, -, hrep⟩ := a.property
  apply Subtype.ext
  rw [← adim9_pb_rep _ a f hrep, ← hrep]
  rfl

private theorem adim9_value_ofFun {n : ℕ} (a : AnalyticGerm n) (f : (Fin n → ℂ) → ℂ)
    (hrep : Germ.ofFun f = a.val) : analyticGermValue n a = f 0 := by
  change a.val.value = f 0
  rw [← hrep]
  exact Filter.Germ.value_ofFun f 0

private theorem adim9_pb_value {n d : ℕ} (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (a : AnalyticGerm d) : analyticGermValue n (adim9_pb π a) = analyticGermValue d a := by
  obtain ⟨f, -, hrep⟩ := a.property
  rw [adim9_value_ofFun _ _ (adim9_pb_rep π a f hrep), adim9_value_ofFun a f hrep, map_zero]

/-- The coordinate germ `w ↦ w i`. -/
private def adim9_coord (d : ℕ) (i : Fin d) : AnalyticGerm d :=
  ⟨Germ.ofFun (fun w ↦ w i), fun w ↦ w i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).analyticAt 0, rfl⟩

/-- Every prime containing the ideal and the coordinates of `L` contains the maximal ideal. -/
private def adim9_Primary {N d : ℕ} (P : Ideal (AnalyticGerm N))
    (L : (Fin N → ℂ) →L[ℂ] (Fin d → ℂ)) : Prop :=
  ∀ q : Ideal (AnalyticGerm N), q.IsPrime → P ≤ q →
    (∀ i, adim9_pb L (adim9_coord d i) ∈ q) → analyticGermMaximalIdeal N ≤ q

private theorem adim9_finite_of_injective {N d : ℕ} (P : Ideal (AnalyticGerm N))
    (L : (Fin N → ℂ) →L[ℂ] (Fin d → ℂ)) (hL : LinearMap.ker (L : (Fin N → ℂ) →ₗ[ℂ] (Fin d → ℂ)) = ⊥) :
    ((Ideal.Quotient.mk P).comp (adim9_pb L)).Finite := by
  obtain ⟨M, hM⟩ := LinearMap.exists_leftInverse_of_injective
    (L : (Fin N → ℂ) →ₗ[ℂ] (Fin d → ℂ)) hL
  let M' : (Fin d → ℂ) →L[ℂ] (Fin N → ℂ) := LinearMap.toContinuousLinearMap M
  have hML : M'.comp L = ContinuousLinearMap.id ℂ _ := by
    ext1 z
    exact LinearMap.congr_fun hM z
  apply RingHom.Finite.of_surjective
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨adim9_pb M' b, ?_⟩
  simp only [RingHom.comp_apply, adim9_pb_pb, hML, adim9_pb_id]


private def adim9_drop (N : ℕ) : (Fin (N + 1) → ℂ) →L[ℂ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.castSucc

private def adim9_axis (N : ℕ) : (Fin 1 → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).smulRight
    (Pi.single (Fin.last N) 1)

private theorem adim9_pb_drop_eq (N : ℕ)
    (ι : Polynomial (AnalyticGerm N) →+* AnalyticGerm (N + 1))
    (hι : IsWeierstrassEmbedding ι) (a : AnalyticGerm N) :
    ι (Polynomial.C a) = adim9_pb (adim9_drop N) a := by
  obtain ⟨f, -, hfa, hfι⟩ := hι.2.1 a
  apply Subtype.ext
  rw [← hfι, ← adim9_pb_rep _ a f hfa]
  rfl

/-- A prime ideal which is primary together with a map killing the last axis contains
an element regular in the last variable. -/
private theorem adim9_regular_of_primary {N d : ℕ} (J : Ideal (AnalyticGerm (N + 1)))
    (K : (Fin (N + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) (hK : K (Pi.single (Fin.last N) 1) = 0)
    (hJ : adim9_Primary J K) : ∃ g ∈ J, IsRegularInLast g := by
  have : NoZeroDivisors (AnalyticGerm 1) := analyticGerm_noZeroDivisors_succ (n := 0)
  have : IsDomain (AnalyticGerm 1) := NoZeroDivisors.to_isDomain _
  by_contra hcon
  push Not at hcon
  set q := RingHom.ker (adim9_pb (adim9_axis N))
  have hq : q.IsPrime := RingHom.ker_isPrime _
  have haxis : ∀ (f : (Fin (N + 1) → ℂ) → ℂ) (t : Fin 1 → ℂ),
      f (adim9_axis N t) = f (Pi.single (Fin.last N) (t 0)) := by
    intro f t
    congr 1
    simp [adim9_axis, ← Pi.single_smul]
  have hJq : J ≤ q := by
    intro g hg
    obtain ⟨f, hf, hrep⟩ := g.property
    have hord : analyticOrderAt (fun w : ℂ ↦ f (Pi.single (Fin.last N) w)) 0 = ⊤ := by
      by_contra h
      exact hcon g hg ⟨f, hf, hrep, h⟩
    rw [analyticOrderAt_eq_top] at hord
    change adim9_pb (adim9_axis N) g = 0
    apply Subtype.ext
    rw [← adim9_pb_rep _ g f hrep]
    change (Germ.ofFun _ : Germ (𝓝 (0 : Fin 1 → ℂ)) ℂ) = Germ.ofFun (fun _ ↦ 0)
    rw [Germ.coe_eq]
    have ht : Tendsto (fun t : Fin 1 → ℂ ↦ t 0) (𝓝 0) (𝓝 0) :=
      (continuous_apply 0).tendsto' _ _ rfl
    filter_upwards [ht.eventually hord] with t ht
    rw [haxis f t]
    exact ht
  have hℓ : ∀ i, adim9_pb K (adim9_coord d i) ∈ q := by
    intro i
    change adim9_pb (adim9_axis N) _ = 0
    rw [adim9_pb_pb]
    have h0 : K.comp (adim9_axis N) = 0 := by
      ext1 t
      simp [adim9_axis, hK]
    rw [h0]
    apply Subtype.ext
    rw [← adim9_pb_rep _ _ _ rfl]
    change (Germ.ofFun _ : Germ (𝓝 (0 : Fin 1 → ℂ)) ℂ) = Germ.ofFun (fun _ ↦ 0)
    simp
  have hm := hJ q hq hJq hℓ
  have hlast : adim9_coord (N + 1) (Fin.last N) ∈ analyticGermMaximalIdeal N.succ := by
    change analyticGermValue _ _ = 0
    rw [adim9_value_ofFun _ _ rfl]
    rfl
  have h := hm hlast
  change adim9_pb (adim9_axis N) _ = 0 at h
  have h' := congrArg Subtype.val h
  rw [← adim9_pb_rep _ _ _ rfl] at h'
  change (Germ.ofFun _ : Germ (𝓝 (0 : Fin 1 → ℂ)) ℂ) = Germ.ofFun (fun _ ↦ 0) at h'
  rw [Germ.coe_eq] at h'
  have hc : Tendsto (fun s : ℂ ↦ (fun _ : Fin 1 ↦ s)) (𝓝[≠] 0) (𝓝 0) :=
    (continuous_pi fun _ ↦ continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs, hs0⟩ := ((hc.eventually h').and self_mem_nhdsWithin).exists
  simp [adim9_axis] at hs
  exact hs0 hs


private def adim9_incl (N : ℕ) : (Fin N → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ Fin.lastCases 0 (fun j ↦ ContinuousLinearMap.proj j) i

private theorem adim9_factor_drop {N d : ℕ} (K : (Fin (N + 1) → ℂ) →L[ℂ] (Fin d → ℂ))
    (hK : K (Pi.single (Fin.last N) 1) = 0) :
    K = (K.comp (adim9_incl N)).comp (adim9_drop N) := by
  ext1 z
  have hz : z = adim9_incl N (adim9_drop N z) + z (Fin.last N) • Pi.single (Fin.last N) 1 := by
    funext i
    induction i using Fin.lastCases <;> simp [adim9_incl, adim9_drop]
  conv_lhs => rw [hz]
  simp [hK]

/-- Pullback along an invertible linear change of coordinates. -/
private def adim9_pbEquiv {n : ℕ} (T : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) :
    AnalyticGerm n ≃+* AnalyticGerm n :=
  RingEquiv.ofRingHom (adim9_pb (T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)))
    (adim9_pb (T.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)))
    (RingHom.ext fun a ↦ by simp [adim9_pb_pb, adim9_pb_id])
    (RingHom.ext fun a ↦ by simp [adim9_pb_pb, adim9_pb_id])

/-- Finite parameters along a linear map whose coordinates, together with a prime,
cut out only the closed point. -/
private theorem adim9_finite_of_primary (d : ℕ) : ∀ (N : ℕ) (P : Ideal (AnalyticGerm N)),
    P.IsPrime → ∀ (L : (Fin N → ℂ) →L[ℂ] (Fin d → ℂ)), adim9_Primary P L →
      ((Ideal.Quotient.mk P).comp (adim9_pb L)).Finite := by
  intro N
  induction N with
  | zero =>
    intro P _ L _
    exact adim9_finite_of_injective P L (Submodule.eq_bot_of_subsingleton)
  | succ N ih =>
    intro P hP L hPL
    by_cases hker : LinearMap.ker (L : (Fin (N + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)) = ⊥
    · exact adim9_finite_of_injective P L hker
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hs0 : (Pi.single (Fin.last N) 1 : Fin (N + 1) → ℂ) ≠ 0 := by
      simp
    obtain ⟨T, hT⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℂ) hs0 hv0
    set K := L.comp (T : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (N + 1) → ℂ)) with hKdef
    have hK : K (Pi.single (Fin.last N) 1) = 0 := by
      simp only [K, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hT]
      exact hv
    set e := adim9_pbEquiv T
    have he : ∀ a, e a = adim9_pb (T : (Fin (N + 1) → ℂ) →L[ℂ] (Fin (N + 1) → ℂ)) a :=
      fun _ ↦ rfl
    set J := P.map (e : AnalyticGerm (N + 1) →+* AnalyticGerm (N + 1))
    have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv e
    have hJK : adim9_Primary J K := by
      intro q hq hJq hℓ
      have hq' : (q.comap (e : AnalyticGerm (N + 1) →+* AnalyticGerm (N + 1))).IsPrime :=
        Ideal.comap_isPrime _ _
      have hPq : P ≤ q.comap (e : AnalyticGerm (N + 1) →+* AnalyticGerm (N + 1)) :=
        Ideal.map_le_iff_le_comap.mp hJq
      have hℓ' : ∀ i, adim9_pb L (adim9_coord d i) ∈
          q.comap (e : AnalyticGerm (N + 1) →+* AnalyticGerm (N + 1)) := by
        intro i
        change e (adim9_pb L _) ∈ q
        rw [he, adim9_pb_pb]
        exact hℓ i
      have hm := hPL _ hq' hPq hℓ'
      intro x hx
      have hx' : e.symm x ∈ analyticGermMaximalIdeal (N + 1) := by
        change analyticGermValue _ (adim9_pb _ x) = 0
        rw [adim9_pb_value]
        exact hx
      have := hm hx'
      change e (e.symm x) ∈ q at this
      simpa using this
    obtain ⟨g, hgJ, hreg⟩ := adim9_regular_of_primary J K hK hJK
    have hgu : ¬ IsUnit g := fun h ↦ hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hgJ h)
    obtain ⟨ι, W, hι, hW, hassoc⟩ := spec_preparation_transfer hreg hgu
    have hιW : ι W ∈ J := by
      obtain ⟨c, hc⟩ := hassoc.dvd
      rw [hc]
      exact J.mul_mem_right c hgJ
    set Q := J.comap (ι.comp Polynomial.C)
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hqf := adim4_contraction_finite N ι hι W hW J hιW
    set K' := K.comp (adim9_incl N)
    have hfac : K = K'.comp (adim9_drop N) := adim9_factor_drop K hK
    have hdrop := adim9_pb_drop_eq N ι hι
    have hφ : (Ideal.Quotient.mk J).comp (ι.comp Polynomial.C) =
        (Ideal.quotientMap J (ι.comp Polynomial.C) le_rfl).comp (Ideal.Quotient.mk Q) :=
      RingHom.ext fun a ↦ rfl
    have hφf : ((Ideal.Quotient.mk J).comp (ι.comp Polynomial.C)).Finite := by
      rw [hφ]
      exact hqf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
    have hQK' : adim9_Primary Q K' := by
      intro q' hq' hQq' hℓ'
      let := ((Ideal.Quotient.mk J).comp (ι.comp Polynomial.C)).toAlgebra
      have : Algebra.IsIntegral (AnalyticGerm N) (AnalyticGerm (N + 1) ⧸ J) :=
        ⟨hφf.to_isIntegral⟩
      obtain ⟨Qb, -, hQb, hQbu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral q'
        (⊥ : Ideal (AnalyticGerm (N + 1) ⧸ J)) (by
          intro x hx
          apply hQq'
          change (Ideal.Quotient.mk J) (ι (Polynomial.C x)) ∈ (⊥ : Ideal _) at hx
          rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
          exact hx)
      set q := Qb.comap (Ideal.Quotient.mk J)
      have hqp : q.IsPrime := Ideal.comap_isPrime _ _
      have hJq : J ≤ q := fun x hx ↦ by
        change Ideal.Quotient.mk J x ∈ Qb
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact Qb.zero_mem
      have hcomap : ∀ x, ι (Polynomial.C x) ∈ q ↔ x ∈ q' := by
        intro x
        rw [← hQbu]
        rfl
      have hℓK : ∀ i, adim9_pb K (adim9_coord d i) ∈ q := by
        intro i
        rw [hfac, ← adim9_pb_pb, ← hdrop]
        exact (hcomap _).mpr (hℓ' i)
      have hm := hJK q hqp hJq hℓK
      intro x hx
      apply (hcomap x).mp
      apply hm
      rw [hdrop]
      change analyticGermValue _ _ = 0
      rw [adim9_pb_value]
      exact hx
    have hfin' := ih Q hQ K' hQK'
    have hKfin : ((Ideal.Quotient.mk J).comp (adim9_pb K)).Finite := by
      have hcomp : (Ideal.Quotient.mk J).comp (adim9_pb K) =
          (Ideal.quotientMap J (ι.comp Polynomial.C) le_rfl).comp
            ((Ideal.Quotient.mk Q).comp (adim9_pb K')) := by
        refine RingHom.ext fun a ↦ ?_
        simp only [RingHom.comp_apply]
        rw [hfac, ← adim9_pb_pb, ← hdrop]
        rfl
      rw [hcomp]
      exact hqf.comp hfin'
    let E : (AnalyticGerm (N + 1) ⧸ P) ≃+* (AnalyticGerm (N + 1) ⧸ J) :=
      Ideal.quotientEquiv P J e rfl
    have hPE : (Ideal.Quotient.mk P).comp (adim9_pb L) =
        E.symm.toRingHom.comp ((Ideal.Quotient.mk J).comp (adim9_pb K)) := by
      refine RingHom.ext fun a ↦ ?_
      apply E.injective
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.apply_symm_apply, E, Ideal.quotientEquiv_apply, RingHom.toFun_eq_coe,
        Ideal.quotientMap_mk]
      rw [hKdef, ← adim9_pb_pb]
      rfl
    rw [hPE]
    exact (RingHom.Finite.of_surjective _ E.symm.surjective).comp hKfin

/-- A finite injective ring map preserves Krull dimension. -/
private theorem adim9_param_krullDim_eq {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Finite)
    (hinj : Function.Injective f) : ringKrullDim R = ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have hint : Algebra.IsIntegral R S := ⟨hf.to_isIntegral⟩
  apply le_antisymm
  · rw [ringKrullDim, Order.krullDim]
    apply iSup_le
    intro l
    obtain ⟨Q, -, hQ, hQo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
      (⊥ : Ideal S) (by
        change RingHom.ker f ≤ l.head.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
        exact bot_le)
    have : Q.LiesOver l.head.asIdeal := ⟨hQo.symm⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L
  · exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun I J hIJ ↦ by
      change Ideal.under R I.asIdeal < Ideal.under R J.asIdeal
      exact Ideal.IsIntegral.under_lt_under hIJ

/-- Finite parameters into a domain of the parameter dimension are injective. -/
private theorem adim9_param_injective (d : ℕ) {B : Type*} [CommRing B] [IsDomain B]
    (θ : AnalyticGerm (d + 1) →+* B) (hθ : θ.Finite)
    (hdim : ringKrullDim B = ((d + 1 : ℕ) : WithBot ℕ∞)) : Function.Injective θ := by
  let : NoZeroDivisors (AnalyticGerm (d + 1)) := analyticGerm_noZeroDivisors_succ
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hfin : (RingHom.kerLift θ).Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker θ)) hθ
  have heq := adim9_param_krullDim_eq _ hfin (RingHom.kerLift_injective θ)
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker θ))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  rw [heq, hdim, adim6_parameter_dimension] at hle
  have : (((d + 1 : ℕ) : ℕ∞) + 1 : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) := hle
  norm_cast at this
  simp at this

/-- Finitely many elements of an ideal with analytic representatives extend to a generating
family with representatives analytic on one open neighbourhood inside a given one. -/
private theorem adim9_generators_extending (N k : ℕ) (q : Ideal (AnalyticGerm N))
    (h : Fin k → AnalyticGerm N) (hh : ∀ j, h j ∈ q) (F : Fin k → (Fin N → ℂ) → ℂ)
    (hFa : ∀ j, AnalyticAt ℂ (F j) 0) (hrep : ∀ j, Germ.ofFun (F j) = (h j).val)
    (O : Set (Fin N → ℂ)) (hO : O ∈ 𝓝 0) :
    ∃ (m : ℕ) (g : Fin (k + m) → AnalyticGerm N) (G : Fin (k + m) → (Fin N → ℂ) → ℂ)
      (U : Set (Fin N → ℂ)), Ideal.span (Set.range g) = q ∧
      (∀ j, Germ.ofFun (G j) = (g j).val) ∧ IsOpen U ∧ (0 : Fin N → ℂ) ∈ U ∧ U ⊆ O ∧
      (∀ j, AnalyticOnNhd ℂ (G j) U) ∧ ∀ j, G (Fin.castAdd m j) = F j := by
  have hfg : q.FG := (isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian N) q
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let g : Fin (k + m) → AnalyticGerm N := Fin.append h s
  have hgen : Ideal.span (Set.range g) = q := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j => simpa [g] using hh j
      | right j =>
        simp only [g, Fin.append_right]
        rw [← hs]
        exact Submodule.subset_span ⟨j, rfl⟩
    · rw [← hs]
      apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨Fin.natAdd k j, by simp [g]⟩
  choose S hSa hSrep using fun j ↦ (s j).property
  let G : Fin (k + m) → (Fin N → ℂ) → ℂ := Fin.append F S
  have hGa : ∀ j, AnalyticAt ℂ (G j) 0 := by
    intro j
    induction j using Fin.addCases with
    | left j => simpa [G] using hFa j
    | right j => simpa [G] using hSa j
  have hGrep : ∀ j, Germ.ofFun (G j) = (g j).val := by
    intro j
    induction j using Fin.addCases with
    | left j => simpa [G, g] using hrep j
    | right j => simpa [G, g] using hSrep j
  have hev : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), z ∈ O ∧ ∀ j, AnalyticAt ℂ (G j) z :=
    (Filter.eventually_mem_set.mpr hO).and
      (Filter.eventually_all.mpr fun j ↦ (hGa j).eventually_analyticAt)
  obtain ⟨U, hUsub, hU, hU0⟩ := mem_nhds_iff.mp hev
  exact ⟨m, g, G, U, hgen, hGrep, hU, hU0, fun z hz ↦ (hUsub hz).1,
    fun j z hz ↦ (hUsub hz).2 j, fun j ↦ by simp [G]⟩

/-- A prime germ ideal other than the maximal ideal has common zeros of any finitely
many of its elements at nonzero points arbitrarily close to the origin. -/
private theorem adim9_prime_points (N : ℕ) (q : Ideal (AnalyticGerm N)) (hq : q.IsPrime)
    (hqm : ¬ analyticGermMaximalIdeal N ≤ q) (k : ℕ) (h : Fin k → AnalyticGerm N)
    (hh : ∀ j, h j ∈ q) (F : Fin k → (Fin N → ℂ) → ℂ) (hFa : ∀ j, AnalyticAt ℂ (F j) 0)
    (hrep : ∀ j, Germ.ofFun (F j) = (h j).val) (O : Set (Fin N → ℂ)) (hO : O ∈ 𝓝 0) :
    ∃ z ∈ O, z ≠ 0 ∧ ∀ j, F j z = 0 := by
  have hqle : q ≤ analyticGermMaximalIdeal N := by
    intro x hx
    by_contra hx'
    have hu : IsUnit x := by
      rw [analyticGerm_isUnit_iff]
      exact hx'
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  have hmmax : (analyticGermMaximalIdeal N).IsMaximal := by
    apply RingHom.ker_isMaximal_of_surjective
    intro c
    exact ⟨⟨Filter.Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩
  have hdimq : ¬ ringKrullDim (AnalyticGerm N ⧸ q) ≤ 0 := by
    intro hle
    have : Ring.KrullDimLE 0 (AnalyticGerm N ⧸ q) :=
      (Ring.krullDimLE_iff).mpr (by exact_mod_cast hle)
    have hfield : IsField (AnalyticGerm N ⧸ q) := Ring.KrullDimLE.isField_of_isDomain
    have hqmax : q.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient q).mpr hfield
    exact hqm (hqmax.eq_of_le hmmax.ne_top hqle).symm.le
  obtain ⟨d, π, θ, -, hfin, hinj, hcomp, hdim⟩ := adim5_finite_parameters N q hq
  rw [adim6_parameter_dimension] at hdim
  have hd : d ≠ 0 := by
    rintro rfl
    rw [← hdim] at hdimq
    exact hdimq (by simp)
  obtain ⟨m, g, G, U, hgen, hGrep, hU, hU0, hUO, hGU, hGF⟩ :=
    adim9_generators_extending N k q h hh F hFa hrep O hO
  obtain ⟨W, V, hW, hW0, hWU, hV, hV0, p, hp, -, -, hsurj, -⟩ :=
    adim7_surjective_projection N d (k + m) q hq π θ hfin hinj hcomp g hgen G U hU hU0
      hGU hGrep
  have : Nontrivial (Fin d → ℂ) := by
    have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
    infer_instance
  have hVn : V ∈ 𝓝[≠] (0 : Fin d → ℂ) := nhdsWithin_le_nhds (hV.mem_nhds hV0)
  have hmem : V ∩ {0}ᶜ ∈ 𝓝[≠] (0 : Fin d → ℂ) := Filter.inter_mem hVn self_mem_nhdsWithin
  obtain ⟨w, hwV, hw0⟩ := Filter.nonempty_of_mem hmem
  obtain ⟨z, hz⟩ := hsurj ⟨w, hwV⟩
  have hzw : π z.val = w := by rw [← hp z, hz]
  refine ⟨z.val, hUO (hWU z.2.1), fun h0 ↦ hw0 ?_, fun j ↦ ?_⟩
  · rw [← hzw, h0, map_zero]
    rfl
  · rw [← hGF j]
    exact z.2.2 (Fin.castAdd m j)


private theorem adim9_maximalIdeal_isMaximal (N : ℕ) :
    (analyticGermMaximalIdeal N).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨⟨Filter.Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩

/-- At a point of an analytic set isolated in its fibre, a linear map gives finite
parameters on some minimal prime of the germ. -/
private theorem adim9_local_finite (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (x : Fin (n + 1) → ℂ) (hx : x ∈ C) (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U)
    (hxU : x ∈ U) (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U) (hUC : ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hiso : ∀ᶠ y in 𝓝 x, y ∈ C → L y = L x → y = x) :
    ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
      ((Ideal.Quotient.mk P).comp (adim9_pb L)).Finite := by
  have hT : Tendsto (fun z : Fin (n + 1) → ℂ ↦ x + z) (𝓝 0) (𝓝 x) :=
    (continuous_const.add continuous_id).tendsto' 0 x (add_zero x)
  let F : Fin m → (Fin (n + 1) → ℂ) → ℂ := fun j z ↦ f j (x + z)
  have hFa : ∀ j, AnalyticAt ℂ (F j) 0 := fun j ↦
    (hf j x hxU).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  let hg : Fin m → AnalyticGerm (n + 1) := fun j ↦ ⟨Germ.ofFun (F j), F j, hFa j, rfl⟩
  set I := adim2_ideal (n + 1) (adim2_germ (n + 1) C x)
  have hI : ∀ j, hg j ∈ I := by
    intro j
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), (x + z ∈ C) → F j z = 0
    filter_upwards [hT.eventually (hU.mem_nhds hxU)] with z hz hzC
    exact (hUC _ hz).mp hzC j
  have hIm : I ≤ analyticGermMaximalIdeal (n + 1) := by
    intro g hgI
    obtain ⟨r, -, hrep⟩ := g.property
    have h' : adim2_germ (n + 1) C x ≤ adim2_zero (n + 1) g := hgI
    rw [adim2_zero, ← hrep] at h'
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), (x + z ∈ C) → r z = 0 at h'
    change analyticGermValue _ g = 0
    rw [adim9_value_ofFun g r hrep]
    exact h'.self_of_nhds (by simpa using hx)
  have : (analyticGermMaximalIdeal (n + 1)).IsPrime :=
    (adim9_maximalIdeal_isMaximal (n + 1)).isPrime
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le hIm
  have hPprime : P.IsPrime := hPmin.1.1
  have hIP : I ≤ P := hPmin.1.2
  have hprim : adim9_Primary P L := by
    intro q hq hPq hℓ
    by_contra hqm
    let hfam : Fin (m + (d + 1)) → AnalyticGerm (n + 1) :=
      Fin.append hg (fun i ↦ adim9_pb L (adim9_coord (d + 1) i))
    let Ffam : Fin (m + (d + 1)) → (Fin (n + 1) → ℂ) → ℂ :=
      Fin.append F (fun i z ↦ L z i)
    have hfamq : ∀ j, hfam j ∈ q := by
      intro j
      induction j using Fin.addCases with
      | left j => simpa [hfam] using hPq (hIP (hI j))
      | right j => simpa [hfam] using hℓ j
    have hFfam : ∀ j, AnalyticAt ℂ (Ffam j) 0 := by
      intro j
      induction j using Fin.addCases with
      | left j => simpa [Ffam] using hFa j
      | right j =>
        simp only [Ffam, Fin.append_right]
        exact ((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin (d + 1) ↦ ℂ) j).comp L).analyticAt 0
    have hrepfam : ∀ j, Germ.ofFun (Ffam j) = (hfam j).val := by
      intro j
      induction j using Fin.addCases with
      | left j => simp [Ffam, hfam, hg]
      | right j =>
        simpa [Ffam, hfam] using adim9_pb_rep L (adim9_coord (d + 1) j) (fun w ↦ w j) rfl
    obtain ⟨z, hzO, hz0, hzF⟩ := adim9_prime_points (n + 1) q hq hqm _ hfam hfamq Ffam
      hFfam hrepfam {z | x + z ∈ U ∧ (x + z ∈ C → L (x + z) = L x → x + z = x)}
      (hT.eventually ((hU.eventually_mem hxU).and hiso))
    have hzC : x + z ∈ C := (hUC _ hzO.1).mpr fun j ↦ by
      simpa [Ffam, F] using hzF (Fin.castAdd _ j)
    have hLz : L z = 0 := funext fun i ↦ by simpa [Ffam] using hzF (Fin.natAdd _ i)
    have := hzO.2 hzC (by rw [map_add, hLz, add_zero])
    exact hz0 (by simpa using this)
  exact ⟨P, hPmin, adim9_finite_of_primary (d + 1) (n + 1) P hPprime L hprim⟩

/-- At a point of an analytic set isolated in its fibre, a linear map gives finite
parameters on every minimal prime of the germ. -/
private theorem adim9_local_finite_all (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (x : Fin (n + 1) → ℂ) (_hx : x ∈ C) (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U)
    (hxU : x ∈ U) (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U) (hUC : ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hiso : ∀ᶠ y in 𝓝 x, y ∈ C → L y = L x → y = x) :
    ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
      ((Ideal.Quotient.mk P).comp (adim9_pb L)).Finite := by
  have hT : Tendsto (fun z : Fin (n + 1) → ℂ ↦ x + z) (𝓝 0) (𝓝 x) :=
    (continuous_const.add continuous_id).tendsto' 0 x (add_zero x)
  let F : Fin m → (Fin (n + 1) → ℂ) → ℂ := fun j z ↦ f j (x + z)
  have hFa : ∀ j, AnalyticAt ℂ (F j) 0 := fun j ↦
    (hf j x hxU).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  let hg : Fin m → AnalyticGerm (n + 1) := fun j ↦ ⟨Germ.ofFun (F j), F j, hFa j, rfl⟩
  set I := adim2_ideal (n + 1) (adim2_germ (n + 1) C x)
  have hI : ∀ j, hg j ∈ I := by
    intro j
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), (x + z ∈ C) → F j z = 0
    filter_upwards [hT.eventually (hU.mem_nhds hxU)] with z hz hzC
    exact (hUC _ hz).mp hzC j
  intro P hPmin
  have hPprime : P.IsPrime := hPmin.1.1
  have hIP : I ≤ P := hPmin.1.2
  have hprim : adim9_Primary P L := by
    intro q hq hPq hℓ
    by_contra hqm
    let hfam : Fin (m + (d + 1)) → AnalyticGerm (n + 1) :=
      Fin.append hg (fun i ↦ adim9_pb L (adim9_coord (d + 1) i))
    let Ffam : Fin (m + (d + 1)) → (Fin (n + 1) → ℂ) → ℂ :=
      Fin.append F (fun i z ↦ L z i)
    have hfamq : ∀ j, hfam j ∈ q := by
      intro j
      induction j using Fin.addCases with
      | left j => simpa [hfam] using hPq (hIP (hI j))
      | right j => simpa [hfam] using hℓ j
    have hFfam : ∀ j, AnalyticAt ℂ (Ffam j) 0 := by
      intro j
      induction j using Fin.addCases with
      | left j => simpa [Ffam] using hFa j
      | right j =>
        simp only [Ffam, Fin.append_right]
        exact ((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin (d + 1) ↦ ℂ) j).comp L).analyticAt 0
    have hrepfam : ∀ j, Germ.ofFun (Ffam j) = (hfam j).val := by
      intro j
      induction j using Fin.addCases with
      | left j => simp [Ffam, hfam, hg]
      | right j =>
        simpa [Ffam, hfam] using adim9_pb_rep L (adim9_coord (d + 1) j) (fun w ↦ w j) rfl
    obtain ⟨z, hzO, hz0, hzF⟩ := adim9_prime_points (n + 1) q hq hqm _ hfam hfamq Ffam
      hFfam hrepfam {z | x + z ∈ U ∧ (x + z ∈ C → L (x + z) = L x → x + z = x)}
      (hT.eventually ((hU.eventually_mem hxU).and hiso))
    have hzC : x + z ∈ C := (hUC _ hzO.1).mpr fun j ↦ by
      simpa [Ffam, F] using hzF (Fin.castAdd _ j)
    have hLz : L z = 0 := funext fun i ↦ by simpa [Ffam] using hzF (Fin.natAdd _ i)
    have := hzO.2 hzC (by rw [map_add, hLz, add_zero])
    exact hz0 (by simpa using this)
  exact adim9_finite_of_primary (d + 1) (n + 1) P hPprime L hprim

/-- At a point of a pure analytic set isolated in its fibre, a linear map onto the
dimension of the set gives finite injective parameters on every minimal prime of the
germ and maps the set onto a neighbourhood of the image point. -/
private theorem adim9_local_onto (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (x : Fin (n + 1) → ℂ) (hx : x ∈ C) (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U)
    (hxU : x ∈ U) (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U) (hUC : ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hpure : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hiso : ∀ᶠ y in 𝓝 x, y ∈ C → L y = L x → y = x) :
    ∀ᶠ w in 𝓝 (L x), ∃ y ∈ C, L y = w := by
  have hT : Tendsto (fun z : Fin (n + 1) → ℂ ↦ x + z) (𝓝 0) (𝓝 x) :=
    (continuous_const.add continuous_id).tendsto' 0 x (add_zero x)
  let F : Fin m → (Fin (n + 1) → ℂ) → ℂ := fun j z ↦ f j (x + z)
  have hFa : ∀ j, AnalyticAt ℂ (F j) 0 := fun j ↦
    (hf j x hxU).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  let hg : Fin m → AnalyticGerm (n + 1) := fun j ↦ ⟨Germ.ofFun (F j), F j, hFa j, rfl⟩
  set I := adim2_ideal (n + 1) (adim2_germ (n + 1) C x)
  have hI : ∀ j, hg j ∈ I := by
    intro j
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), (x + z ∈ C) → F j z = 0
    filter_upwards [hT.eventually (hU.mem_nhds hxU)] with z hz hzC
    exact (hUC _ hz).mp hzC j
  obtain ⟨P, hPmin, hfin⟩ := adim9_local_finite n d C x hx U hU hxU m f hf hUC L hiso
  have hPprime : P.IsPrime := hPmin.1.1
  have hIP : I ≤ P := hPmin.1.2
  have hdim := hpure P hPmin
  set θ := (Ideal.Quotient.mk P).comp (adim9_pb L)
  have hinj : Function.Injective θ := adim9_param_injective d θ hfin hdim
  have hcomp : ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
      Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk P b := by
    intro a h _ ha b hb
    change Ideal.Quotient.mk P (adim9_pb L a) = Ideal.Quotient.mk P b
    rw [show adim9_pb L a = b from Subtype.ext ((adim9_pb_rep L a h ha).symm.trans hb)]
  obtain ⟨mm, g, G, U', hgen, hGrep, hU', hU'0, hU'O, hGU, hGF⟩ :=
    adim9_generators_extending (n + 1) m P hg (fun j ↦ hIP (hI j)) F hFa (fun j ↦ rfl)
      {z | x + z ∈ U} (hT.eventually (hU.mem_nhds hxU))
  obtain ⟨W, V, -, -, hWU, hV, hV0, p, hp, -, -, hsurj, -⟩ :=
    adim7_surjective_projection (n + 1) (d + 1) (m + mm) P hPprime L θ hfin hinj hcomp g hgen
      G U' hU' hU'0 hGU hGrep
  have hVx : ∀ᶠ w in 𝓝 (L x), w - L x ∈ V := by
    have ht : Tendsto (fun w ↦ w - L x) (𝓝 (L x)) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' (L x) 0 (sub_self _)
    exact ht.eventually (hV.mem_nhds hV0)
  filter_upwards [hVx] with w hw
  obtain ⟨z, hz⟩ := hsurj ⟨w - L x, hw⟩
  have hzw : L z.val = w - L x := by rw [← hp z, hz]
  refine ⟨x + z.val, (hUC _ (hU'O (hWU z.2.1))).mpr fun j ↦ ?_, ?_⟩
  · have := z.2.2 (Fin.castAdd mm j)
    rw [hGF] at this
    exact this
  · rw [map_add, hzw, add_sub_cancel]

/-- A pure-dimensional punctured homogeneous cone has a finite proper linear
projection of the whole cone onto affine space of its own dimension.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
projection of a homogeneous cone from a disjoint linear centre;
Chirka, Complex Analytic Sets, §§3--4, dimension and generic projections. -/
theorem adim9_cone_pure_projection_aux (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ)
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ),
      Function.Surjective L ∧
      Function.Surjective
        (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
      IsProperMap (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
      (∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) ∧
      (L ⁻¹' {0}) ∩ insert 0 C = {0} := by
  obtain ⟨r, hr, -, x₀, hx₀, P₀, hP₀, hatt⟩ :=
    adim9_cone_dimension_maximum n C hzero hne hclosed hscale hloc
  have hrd : r = d := by
    have h := (hpure x₀ hx₀ P₀ hP₀).symm.trans hatt
    have h' : ((d + 1 : ℕ) : ℕ∞) = ((r + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h
    have h'' : d + 1 = r + 1 := by exact_mod_cast h'
    omega
  subst hrd
  have hle : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ ((r + 1 : ℕ) : WithBot ℕ∞) :=
    fun x hx P hP ↦ (hpure x hx P hP).le
  obtain ⟨K, hK, hKC⟩ := adim9_center_of_dimH (n + 1) (r + 1) (by omega) C hzero hscale
    (adim9_cone_dimH_le n r C hloc hle)
  obtain ⟨L, hsurj, hcentral⟩ := adim9_projection_of_disjoint_center (n + 1) (r + 1) C K hK hKC
  have hproper := adim9_cone_proper_of_central (n + 1) (r + 1) C hzero hne hclosed hscale L
    hcentral
  have hfib := adim9_cone_finite_fibres_of_proper (n + 1) (r + 1) C hloc L hproper hcentral
  refine ⟨L, hsurj, ?_, hproper, hfib, hcentral⟩
  set S := Set.range (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val)
  have hSc : IsClosed S := hproper.isClosedMap.isClosed_range
  have hS0 : (0 : Fin (r + 1) → ℂ) ∈ S := ⟨⟨0, mem_insert 0 C⟩, map_zero L⟩
  have hL0 : ∀ y ∈ C, L y ≠ 0 := by
    intro y hy hy0
    have : y ∈ (L ⁻¹' {0}) ∩ insert 0 C := ⟨hy0, mem_insert_of_mem 0 hy⟩
    rw [hcentral] at this
    exact hzero (by simpa using (show y = 0 from this) ▸ hy)
  have hSn : ∀ w ∈ S, w ≠ 0 → S ∈ 𝓝 w := by
    rintro w ⟨⟨y, hy⟩, rfl⟩ hw
    have hyC : y ∈ C := by
      rcases hy with rfl | hyC
      · exact absurd (map_zero L) hw
      · exact hyC
    have hiso : ∀ᶠ y' in 𝓝 y, y' ∈ C → L y' = L y → y' = y := by
      have hcl : IsClosed ({z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = L y} \ {y}) :=
        ((hfib (L y)).sdiff).isClosed
      filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl)] with y' hy' hy'C hy'L
      by_contra hne
      exact hy' ⟨⟨mem_insert_of_mem 0 hy'C, hy'L⟩, hne⟩
    obtain ⟨U, hU, hyU, -, m, f, hf, hUC⟩ := hloc y hyC
    filter_upwards [adim9_local_onto n r C y hyC U hU hyU m f hf hUC (hpure y hyC) L hiso]
      with w ⟨y', hy'C, hy'w⟩
    exact ⟨⟨y', mem_insert_of_mem 0 hy'C⟩, hy'w⟩
  have hconn : IsConnected ({0}ᶜ : Set (Fin (r + 1) → ℂ)) := by
    apply isConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank, adim9_finrank_real_pi]
    exact_mod_cast (by omega : 1 < 2 * (r + 1))
  have hsub : ({0}ᶜ : Set (Fin (r + 1) → ℂ)) ⊆ S ∩ {0}ᶜ := by
    apply hconn.isPreconnected.subset_of_closure_inter_subset
    · rw [isOpen_iff_mem_nhds]
      rintro w ⟨hwS, hw0⟩
      exact Filter.inter_mem (hSn w hwS hw0) (isOpen_compl_singleton.mem_nhds hw0)
    · obtain ⟨x, hx⟩ := hne
      exact ⟨L x, hL0 x hx, ⟨⟨x, mem_insert_of_mem 0 hx⟩, rfl⟩, hL0 x hx⟩
    · rintro w ⟨hwcl, hw0⟩
      exact ⟨hSc.closure_subset_iff.mpr inter_subset_left hwcl, hw0⟩
  intro w
  by_cases hw : w = 0
  · rw [hw]
    exact hS0
  · exact (hsub hw).1

/-- Properness and the central fibre bound a homogeneous cone linearly by its projection. -/
private theorem adim9_cone_norm_le_of_proper (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ insert 0 C, ‖z‖ ≤ c * ‖L z‖ := by
  have hK := hproper.isCompact_preimage
    (isCompact_closedBall (0 : Fin (d + 1) → ℂ) 1)
  obtain ⟨M, hM⟩ := (hK.image continuous_subtype_val).isBounded.subset_closedBall 0
  refine ⟨max M 1, by positivity, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  have hzC : z ∈ C := by rcases hz with h | h <;> simp_all
  have hLz : L z ≠ 0 := by
    intro h
    have : z ∈ (L ⁻¹' {0}) ∩ insert 0 C := ⟨h, hz⟩
    rw [hcentral] at this
    exact hz0 this
  have hn : 0 < ‖L z‖ := norm_pos_iff.mpr hLz
  set t : ℂ := ((‖L z‖⁻¹ : ℝ) : ℂ)
  have ht : t ≠ 0 := by simp [t, hn.ne']
  have htz : t • z ∈ insert 0 C := mem_insert_of_mem _ (hscale t ht z hzC)
  have htn : ‖t‖ = ‖L z‖⁻¹ := by
    simp [t, Complex.norm_real]
  have hmem : t • z ∈ Subtype.val '' ((fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦
      L z.val) ⁻¹' Metric.closedBall 0 1) := by
    refine ⟨⟨t • z, htz⟩, ?_, rfl⟩
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, map_smul, norm_smul, htn]
    rw [inv_mul_cancel₀ hn.ne']
  have h1 := hM hmem
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, htn] at h1
  have h2 : ‖z‖ ≤ M * ‖L z‖ := by
    rw [inv_mul_le_iff₀ hn] at h1
    linarith
  calc ‖z‖ ≤ M * ‖L z‖ := h2
    _ ≤ max M 1 * ‖L z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) hn.le

/-- Bounded symmetric sheet coefficients of an observable, continued across the
exceptional hypersurface and the vertex. -/
private theorem adim9_cone_bounded_coefficients (n d k : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ z ∈ insert 0 C, ‖z‖ ≤ c * ‖L z‖)
    (ρ : ℝ) (hρ : 0 < ρ) (δ : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ (Metric.ball 0 ρ \ {0}))
    (hnz : ∀ x ∈ Metric.ball 0 ρ \ {0}, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (hsheets : ∀ x ∈ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0},
      ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0} ∧
      (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z)
    (ℓ : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) :
    ∃ b : Fin k → (Fin (d + 1) → ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (b i) (Metric.ball 0 ρ)) ∧
      ∀ w ∈ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0}, ∀ t : ℂ,
        (adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ).eval t =
          t ^ k + ∑ i : Fin k, b i w * t ^ (i : ℕ) := by
  set D := (Metric.ball (0 : Fin (d + 1) → ℂ) ρ \ {0}) \ {x | δ x = 0}
  have hR : 0 ≤ ‖ℓ‖ * c * ρ := by positivity
  have hbound : ∀ x ∈ D, ∀ z ∈ (hfib x).toFinset, ‖ℓ z‖ ≤ ‖ℓ‖ * c * ρ := by
    intro x hx z hz
    rw [Finite.mem_toFinset] at hz
    obtain ⟨hzC, hzx⟩ := hz
    have hx' : ‖x‖ < ρ := by simpa using hx.1.1
    calc ‖ℓ z‖ ≤ ‖ℓ‖ * ‖z‖ := ℓ.le_opNorm z
      _ ≤ ‖ℓ‖ * (c * ‖x‖) := by
        gcongr
        simpa [hzx] using hc z hzC
      _ ≤ ‖ℓ‖ * c * ρ := by
        rw [← mul_assoc]
        gcongr
  obtain ⟨hcoef, hmon⟩ := adim9_sheet_coefficients_aux (n + 1) (d + 1) k D
    (fun w ↦ (hfib w).toFinset) hsheets ℓ (‖ℓ‖ * c * ρ) hR hbound
  obtain ⟨b, hb, hbeq, -⟩ := adim8_coefficient_extension_aux d k (Metric.ball 0 ρ)
    Metric.isOpen_ball (Metric.mem_ball_self hρ) δ hδ hnz
    (fun i w ↦ (adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ).coeff i)
    (fun i ↦ hcoef i) (fun _ ↦ (1 + ‖ℓ‖ * c * ρ) ^ k)
    (fun i x hx ↦ ((hmon x hx).2.2.1 i))
  refine ⟨b, hb, ?_⟩
  intro w hw t
  obtain ⟨hm, hdeg, -, -⟩ := hmon w hw
  conv_lhs => rw [hm.as_sum, hdeg]
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_range (fun i ↦ (adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ).coeff i *
    t ^ i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hbeq i hw]

/-- Finitely many moment observables separate a point from a fibre of at most k points. -/
private theorem adim9_moment_observables_separate (n k : ℕ) (z : Fin (n + 1) → ℂ)
    (y : Fin k → Fin (n + 1) → ℂ)
    (h : ∀ t : Fin (n * k + 1), ∃ j, ∑ i : Fin (n + 1), ((t : ℕ) : ℂ) ^ (i : ℕ) * z i =
      ∑ i : Fin (n + 1), ((t : ℕ) : ℂ) ^ (i : ℕ) * y j i) :
    ∃ j, z = y j := by
  classical
  choose g hg using h
  have hk : Fintype.card (Fin k) * n < Fintype.card (Fin (n * k + 1)) := by
    simp [Nat.mul_comm]
  obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := g) hk
  refine ⟨j, ?_⟩
  set q : ℂ[X] := ∑ i : Fin (n + 1), C (z i - y j i) * X ^ (i : ℕ)
  have hqdeg : q.natDegree ≤ n := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)
  set S : Finset ℂ := (Finset.univ.filter (fun t ↦ g t = j)).image
    (fun t : Fin (n * k + 1) ↦ ((t : ℕ) : ℂ))
  have hinj : Function.Injective (fun t : Fin (n * k + 1) ↦ ((t : ℕ) : ℂ)) := by
    intro a b hab
    simp only [Nat.cast_inj] at hab
    exact Fin.ext hab
  have hS : S.card = (Finset.univ.filter (fun t ↦ g t = j)).card :=
    Finset.card_image_of_injective _ hinj
  have hq : q = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q S ?_ (by omega)
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htj : g t = j := (Finset.mem_filter.mp ht).2
    have := hg t
    rw [htj] at this
    simp only [q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_comm (z _), mul_comm (y j _)]
    rw [this, sub_self]
  funext i
  have hc := congrArg (fun p : ℂ[X] ↦ p.coeff i) hq
  simp only [q, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun b _ hb ↦ by
    simp [show (i : ℕ) ≠ b from fun h ↦ hb (Fin.ext h).symm]) (by simp)] at hc
  simpa [sub_eq_zero] using hc

/-- Over a good base (bounded sheets off a nowhere locally zero hypersurface, whose
preimage is dense in the cone), finitely many monic observable equations cut out the cone
near the vertex. -/
private theorem adim9_vertex_equations_of_good_base (n d k : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (ρ : ℝ) (hρ : 0 < ρ) (δ : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ (Metric.ball 0 ρ \ {0}))
    (hnz : ∀ x ∈ Metric.ball 0 ρ \ {0}, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (hsheets : ∀ x ∈ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0},
      ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0} ∧
      (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z)
    (hdense : ∀ z ∈ C, L z ∈ Metric.ball 0 ρ →
      z ∈ closure (C ∩ L ⁻¹' ((Metric.ball 0 ρ \ {0}) \ {x | δ x = 0}))) :
    ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ insert 0 C ↔ ∀ j, f j z = 0) := by
  classical
  set B := Metric.ball (0 : Fin (d + 1) → ℂ) ρ
  set D := (B \ {0}) \ {x | δ x = 0}
  set G := C ∩ L ⁻¹' D
  obtain ⟨c, hc0, hc⟩ := adim9_cone_norm_le_of_proper n d C hscale L hproper hcentral
  have hins : IsClosed (insert 0 C) := adim9_closed_insert_zero_of_closed_punctured C hclosed
  let ℓ : Fin (n * k + 1) → (Fin (n + 1) → ℂ) →L[ℂ] ℂ := fun t ↦
    ∑ i : Fin (n + 1), (((t : ℕ) : ℂ) ^ (i : ℕ)) •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i
  have hℓ : ∀ t z, ℓ t z = ∑ i : Fin (n + 1), ((t : ℕ) : ℂ) ^ (i : ℕ) * z i := by
    intro t z
    simp [ℓ, sum_apply]
  choose b hb heq using fun t ↦ adim9_cone_bounded_coefficients n d k C L hfib c hc0.le hc ρ hρ
    δ hδ hnz hsheets (ℓ t)
  let f : Fin (n * k + 1) → (Fin (n + 1) → ℂ) → ℂ := fun t z ↦
    ℓ t z ^ k + ∑ i : Fin k, b t i (L z) * ℓ t z ^ (i : ℕ)
  set U := L ⁻¹' B
  have hUo : IsOpen U := Metric.isOpen_ball.preimage L.continuous
  have hfa : ∀ t, AnalyticOnNhd ℂ (f t) U := by
    intro t z hz
    have hℓa : AnalyticAt ℂ (ℓ t) z := (ℓ t).analyticAt z
    refine (hℓa.pow k).add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
    exact ((hb t i (L z) hz).comp (L.analyticAt z)).mul (hℓa.pow _)
  have hfG : ∀ t, ∀ y ∈ G, f t y = 0 := by
    intro t y hy
    have h := heq t (L y) hy.2 (ℓ t y)
    simp only [f, ← h, adim9_fibrePolynomial, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_eq_zero (i := y) ?_ (sub_self _)
    rw [Finite.mem_toFinset]
    exact ⟨mem_insert_of_mem _ hy.1, rfl⟩
  have h0G : (0 : Fin (n + 1) → ℂ) ∈ closure G := by
    obtain ⟨x, hx⟩ := hne
    have htend : Tendsto (fun s : ℂ ↦ s • x) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℂ ↦ s • x) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℂ))).smul_const x
      exact this.mono_left nhdsWithin_le_nhds
    have hLt : Tendsto (fun s : ℂ ↦ L (s • x)) (𝓝[≠] 0) (𝓝 0) := by
      have := (L.continuous.tendsto 0).comp htend
      rw [map_zero] at this
      exact this
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s • x ∈ closure G := by
      filter_upwards [hLt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)),
        self_mem_nhdsWithin] with s hs hs0
      exact hdense _ (hscale s hs0 x hx) hs
    simpa [closure_closure] using mem_closure_of_tendsto htend hev
  have hfwd : ∀ t, ∀ z ∈ U, z ∈ closure G → f t z = 0 := by
    intro t z hz hzG
    exact ((hfa t z hz).continuousAt.continuousWithinAt).eq_const_of_mem_closure hzG (hfG t)
  have hDdense : ∀ w ∈ B, w ∈ closure D := by
    have hpunct : ∀ w ∈ B \ {0}, w ∈ closure D := by
      intro w hw
      rw [mem_closure_iff_frequently]
      have hfr := Filter.not_eventually.mp (hnz w hw)
      have hBo : IsOpen (B \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
      exact (hfr.and_eventually (hBo.mem_nhds hw)).mono fun v hv ↦ ⟨hv.2, hv.1⟩
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      have := Module.punctured_nhds_neBot ℂ (Fin (d + 1) → ℂ) (0 : Fin (d + 1) → ℂ)
      have hev : ∀ᶠ v in 𝓝[≠] (0 : Fin (d + 1) → ℂ), v ∈ closure D := by
        filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hw),
          self_mem_nhdsWithin] with v hv hv0
        exact hpunct v ⟨hv, hv0⟩
      have hfr : ∃ᶠ v in 𝓝 (0 : Fin (d + 1) → ℂ), v ∈ closure D :=
        hev.frequently.filter_mono nhdsWithin_le_nhds
      simpa [closure_closure] using mem_closure_iff_frequently.mpr hfr
    · exact hpunct w ⟨hw, hw0⟩
  have hbwd : ∀ z ∈ U, (∀ t, f t z = 0) → z ∈ insert 0 C := by
    intro z hz hf0
    obtain ⟨ws, hwsD, hws⟩ := mem_closure_iff_seq_limit.mp (hDdense (L z) hz)
    choose W r hWo hxW hWD hra hr using fun m ↦ hsheets (ws m) (hwsD m)
    let E : ℕ → Fin k → Fin (n + 1) → ℂ := fun m j ↦ r m j (ws m)
    have hEmem : ∀ m j, E m j ∈ insert 0 C ∧ L (E m j) = ws m := by
      intro m j
      have := ((hr m (ws m) (hxW m)).2 (E m j)).mpr ⟨j, rfl⟩
      rwa [Finite.mem_toFinset] at this
    have hEimg : ∀ m, (hfib (ws m)).toFinset = Finset.univ.image (E m) := by
      intro m
      ext y
      rw [(hr m (ws m) (hxW m)).2 y]
      simp [E]
    have hEinj : ∀ m, Function.Injective (E m) := fun m ↦ (hr m (ws m) (hxW m)).1
    have hEb : ∀ m, E m ∈ Metric.closedBall (0 : Fin k → Fin (n + 1) → ℂ) (c * ρ) := by
      intro m
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j ↦ ?_
      obtain ⟨hm, hL⟩ := hEmem m j
      have hwm : ‖ws m‖ < ρ := by simpa [B] using (hwsD m).1.1
      calc ‖E m j‖ ≤ c * ‖L (E m j)‖ := hc _ hm
        _ ≤ c * ρ := by rw [hL]; gcongr
    obtain ⟨Y, -, φ, hφ, hY⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hEb
    have hYj : ∀ j, Tendsto (fun m ↦ E (φ m) j) atTop (𝓝 (Y j)) :=
      fun j ↦ ((continuous_apply j).tendsto Y).comp hY
    have hYmem : ∀ j, Y j ∈ insert 0 C := fun j ↦
      hins.mem_of_tendsto (hYj j) (Eventually.of_forall fun m ↦ (hEmem (φ m) j).1)
    have hwφ : Tendsto (fun m ↦ ws (φ m)) atTop (𝓝 (L z)) := hws.comp hφ.tendsto_atTop
    have hroot : ∀ t, ∃ j, ℓ t z = ℓ t (Y j) := by
      intro t
      set x := ℓ t z
      have hlhs : Tendsto (fun m ↦ x ^ k + ∑ i : Fin k, b t i (ws (φ m)) * x ^ (i : ℕ))
          atTop (𝓝 (f t z)) := by
        refine tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ ↦ ?_)
        exact (((hb t i (L z) hz).continuousAt.tendsto).comp hwφ).mul tendsto_const_nhds
      have hrhs : Tendsto (fun m ↦ ∏ j, (x - ℓ t (E (φ m) j))) atTop
          (𝓝 (∏ j, (x - ℓ t (Y j)))) :=
        tendsto_finsetProd _ fun j _ ↦
          tendsto_const_nhds.sub (((ℓ t).continuous.tendsto _).comp (hYj j))
      have hEq : ∀ m, x ^ k + ∑ i : Fin k, b t i (ws (φ m)) * x ^ (i : ℕ) =
          ∏ j, (x - ℓ t (E (φ m) j)) := by
        intro m
        rw [← heq t (ws (φ m)) (hwsD (φ m)) x, hEimg, adim9_fibrePolynomial,
          Finset.prod_image fun a _ b _ h ↦ hEinj (φ m) h]
        simp [eval_prod]
      have hlim := tendsto_nhds_unique (hlhs.congr hEq) hrhs
      rw [hf0 t] at hlim
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hlim.symm
      exact ⟨j, sub_eq_zero.mp hj⟩
    obtain ⟨j, hj⟩ := adim9_moment_observables_separate n k z Y fun t ↦ by
      obtain ⟨j, hj⟩ := hroot t
      exact ⟨j, by rw [← hℓ, ← hℓ, hj]⟩
    exact hj ▸ hYmem j
  refine ⟨U, hUo, by simp [U, B, hρ], n * k + 1, f, hfa, fun z hz ↦ ⟨fun h t ↦ ?_, hbwd z hz⟩⟩
  rcases h with h | h
  · exact hfwd t z hz (h ▸ h0G)
  · exact hfwd t z hz (hdense z h hz)

/-- Closed analyticity of the cone with its vertex from a good base for the projection. -/
private theorem adim9_cone_closed_analytic_of_good_base (n d k : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (ρ : ℝ) (hρ : 0 < ρ) (δ : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ (Metric.ball 0 ρ \ {0}))
    (hnz : ∀ x ∈ Metric.ball 0 ρ \ {0}, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (hsheets : ∀ x ∈ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0},
      ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ {x | δ x = 0} ∧
      (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z)
    (hdense : ∀ z ∈ C, L z ∈ Metric.ball 0 ρ →
      z ∈ closure (C ∩ L ⁻¹' ((Metric.ball 0 ρ \ {0}) \ {x | δ x = 0}))) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) := by
  obtain ⟨U, hUo, hU0, m, f, hf, hUf⟩ := adim9_vertex_equations_of_good_base n d k C hne hclosed
    hscale L hproper hfib hcentral ρ hρ δ hδ hnz hsheets hdense
  refine adim9_closed_analytic_of_vertex_equations (n + 1) C hclosed hloc
    ⟨U, hUo, ?_, ?_, m, f, hf, ?_⟩
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hU0
  · simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_target, subset_univ]
  · intro z hz
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq] using hUf z hz

/-- Points off two nowhere locally zero functions accumulate at every common point. -/
private theorem adim9_frequently_ne_zero_two {N : Type*} [NormedAddCommGroup N] [NormedSpace ℂ N]
    (W₁ W₂ : Set N) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) (δ₁ δ₂ : N → ℂ)
    (hδ₁ : ContinuousOn δ₁ W₁)
    (hnz₁ : ∀ y ∈ W₁, ¬ (δ₁ =ᶠ[𝓝 y] fun _ ↦ 0))
    (hnz₂ : ∀ y ∈ W₂, ¬ (δ₂ =ᶠ[𝓝 y] fun _ ↦ 0))
    (x : N) (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂) :
    ∃ᶠ y in 𝓝 x, y ∈ W₁ ∧ y ∈ W₂ ∧ δ₁ y ≠ 0 ∧ δ₂ y ≠ 0 := by
  rw [Filter.frequently_iff]
  intro o ho
  obtain ⟨o', ho'o, ho', hxo'⟩ := mem_nhds_iff.mp ho
  have hO : IsOpen (o' ∩ W₁ ∩ W₂) := (ho'.inter hW₁).inter hW₂
  obtain ⟨y, hδy, hy⟩ := ((Filter.not_eventually.mp (hnz₁ x hx₁)).and_eventually
    (hO.mem_nhds ⟨⟨hxo', hx₁⟩, hx₂⟩)).exists
  have hO' : o' ∩ W₁ ∩ W₂ ∩ {z | δ₁ z ≠ 0} ∈ 𝓝 y :=
    inter_mem (hO.mem_nhds hy)
      ((hδ₁.continuousAt (hW₁.mem_nhds hy.1.2)).preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds hδy))
  obtain ⟨z, hδz, hz⟩ := ((Filter.not_eventually.mp (hnz₂ y hy.2)).and_eventually
    hO').exists
  exact ⟨z, ho'o hz.1.1.1, hz.1.1.2, hz.1.2, hz.2, hδz⟩

/-- A bounded function, analytic off a set that lies locally in nowhere locally zero
hypersurfaces, continues analytically with the same bound. -/
private theorem adim9_local_hypersurface_extension (d : ℕ) (V E : Set (Fin (d + 1) → ℂ))
    (hE : ∀ x ∈ V, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0})
    (f : (Fin (d + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f (V \ E))
    (M : ℝ) (hb : ∀ x ∈ V \ E, ‖f x‖ ≤ M) :
    ∃ F : (Fin (d + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ F V ∧ EqOn F f (V \ E) ∧ ∀ x ∈ V, ‖F x‖ ≤ M := by
  classical
  choose W hWo hxW hWV δ hδ hnz hEW using hE
  have hext : ∀ x (hx : x ∈ V), ∃ F : (Fin (d + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ F (W x hx) ∧
      EqOn F f (W x hx \ {y | δ x hx y = 0}) ∧ ∀ y ∈ W x hx, ‖F y‖ ≤ M := by
    intro x hx
    have hsub : W x hx \ {y | δ x hx y = 0} ⊆ V \ E := fun y hy ↦
      ⟨hWV x hx hy.1, fun hyE ↦ hy.2 (hEW x hx ⟨hyE, hy.1⟩)⟩
    obtain ⟨F, hF, hFf, hFb, -⟩ := adim8_hypersurface_extension d (W x hx) (hWo x hx)
      (δ x hx) f (hδ x hx) (hnz x hx) (fun y hy ↦ hf y (hsub hy)) M
      (fun y hy ↦ hb y (hsub hy))
    exact ⟨F, hF, hFf, hFb⟩
  choose F hF hFf hFb using hext
  have hagree : ∀ x (hx : x ∈ V) y (hy : y ∈ V), ∀ z ∈ W x hx ∩ W y hy,
      F x hx z = F y hy z := by
    intro x hx y hy z hz
    refine tendsto_nhds_unique_of_frequently_eq
      (hF x hx z hz.1).continuousAt.tendsto (hF y hy z hz.2).continuousAt.tendsto ?_
    refine (adim9_frequently_ne_zero_two (W x hx) (W y hy) (hWo x hx) (hWo y hy)
      (δ x hx) (δ y hy) (hδ x hx).continuousOn (hnz x hx) (hnz y hy) z hz.1 hz.2).mono ?_
    rintro v ⟨hv₁, hv₂, hδ₁, hδ₂⟩
    rw [hFf x hx ⟨hv₁, hδ₁⟩, hFf y hy ⟨hv₂, hδ₂⟩]
  let G : (Fin (d + 1) → ℂ) → ℂ := fun z ↦ if h : z ∈ V then F z h z else 0
  have hGloc : ∀ x (hx : x ∈ V), ∀ z ∈ W x hx, G z = F x hx z := by
    intro x hx z hz
    have hzV := hWV x hx hz
    simp only [G, hzV, ↓reduceDIte]
    exact hagree z hzV x hx z ⟨hxW z hzV, hz⟩
  have hGa : AnalyticOnNhd ℂ G V := by
    intro x hx
    refine (hF x hx x (hxW x hx)).congr ?_
    filter_upwards [(hWo x hx).mem_nhds (hxW x hx)] with z hz
    exact (hGloc x hx z hz).symm
  refine ⟨G, hGa, ?_, fun x hx ↦ by rw [hGloc x hx x (hxW x hx)]; exact hFb x hx x (hxW x hx)⟩
  intro x hx
  refine tendsto_nhds_unique_of_frequently_eq (hGa x hx.1).continuousAt.tendsto
    (hf x hx).continuousAt.tendsto ?_
  refine (adim9_frequently_ne_zero_two (W x hx.1) (W x hx.1) (hWo x hx.1) (hWo x hx.1)
    (δ x hx.1) (δ x hx.1) (hδ x hx.1).continuousOn (hnz x hx.1) (hnz x hx.1) x
    (hxW x hx.1) (hxW x hx.1)).mono ?_
  rintro v ⟨hv, -, hδv, -⟩
  rw [hGloc x hx.1 v hv, hFf x hx.1 ⟨hv, hδv⟩]

/-- The fibre of a local enumeration by k injective sheets has k points. -/
private theorem adim9_fibre_card_of_sheets {n d k : ℕ} (s : (Fin d → ℂ) → Finset (Fin n → ℂ))
    (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ)) (y : Fin d → ℂ)
    (hr : Function.Injective (fun j ↦ r j y) ∧ ∀ z, z ∈ s y ↔ ∃ j, r j y = z) :
    (s y).card = k := by
  classical
  have : s y = Finset.univ.image (fun j ↦ r j y) := by
    ext z
    rw [hr.2 z]
    simp
  rw [this, Finset.card_image_of_injective _ hr.1, Finset.card_univ, Fintype.card_fin]

/-- Padded symmetric sheet coefficients of an observable: over a base whose bad set lies
locally in nowhere locally zero hypersurfaces, with at most N local sheets, the fibre
polynomial padded by a power of X to degree N has coefficients continuing analytically
across the bad set and the vertex. -/
private theorem adim9_cone_padded_coefficients (n d N : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ z ∈ insert 0 C, ‖z‖ ≤ c * ‖L z‖)
    (ρ : ℝ) (hρ : 0 < ρ) (E : Set (Fin (d + 1) → ℂ))
    (hE : ∀ x ∈ Metric.ball 0 ρ \ {0}, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧
      W ⊆ Metric.ball 0 ρ \ {0} ∧ ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0})
    (hsheets : ∀ x ∈ (Metric.ball 0 ρ \ {0}) \ E, ∃ k, k ≤ N ∧
      ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ E ∧
      (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z)
    (ℓ : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) :
    ∃ b : Fin N → (Fin (d + 1) → ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (b i) (Metric.ball 0 ρ)) ∧
      ∀ w ∈ (Metric.ball 0 ρ \ {0}) \ E, ∀ t : ℂ,
        t ^ (N - (hfib w).toFinset.card) *
            (adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ).eval t =
          t ^ N + ∑ i : Fin N, b i w * t ^ (i : ℕ) := by
  classical
  set V := Metric.ball (0 : Fin (d + 1) → ℂ) ρ \ {0}
  set D := V \ E
  obtain ⟨R, hRdef⟩ : ∃ R, R = ‖ℓ‖ * c * ρ := ⟨_, rfl⟩
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  let P : (Fin (d + 1) → ℂ) → ℂ[X] := fun w ↦
    X ^ (N - (hfib w).toFinset.card) * adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ
  have hbound : ∀ x ∈ D, ∀ z ∈ (hfib x).toFinset, ‖ℓ z‖ ≤ R := by
    intro x hx z hz
    rw [Finite.mem_toFinset] at hz
    obtain ⟨hzC, hzx⟩ := hz
    have hx' : ‖x‖ < ρ := by simpa using hx.1.1
    calc ‖ℓ z‖ ≤ ‖ℓ‖ * ‖z‖ := ℓ.le_opNorm z
      _ ≤ ‖ℓ‖ * (c * ‖x‖) := by
        gcongr
        simpa [hzx] using hc z hzC
      _ ≤ R := by
        rw [hRdef, ← mul_assoc]
        gcongr
  -- local data at a good point: analytic coefficients, monic of degree N, bounded
  have hlocal : ∀ x ∈ D, (∀ i : ℕ, AnalyticAt ℂ (fun w ↦ (P w).coeff i) x) ∧
      (P x).Monic ∧ (P x).natDegree = N ∧ ∀ i : ℕ, ‖(P x).coeff i‖ ≤ (1 + R) ^ N := by
    intro x hx
    obtain ⟨k, hkN, W, r, hWo, hxW, hWD, hra, hr⟩ := hsheets x hx
    obtain ⟨hcoef, hmon⟩ := adim9_sheet_coefficients_aux (n + 1) (d + 1) k W
      (fun w ↦ (hfib w).toFinset) (fun y hy ↦ ⟨W, r, hWo, hy, subset_rfl, hra, hr⟩) ℓ R hR
      (fun y hy ↦ hbound y (hWD hy))
    have hcard : ∀ y ∈ W, (hfib y).toFinset.card = k := fun y hy ↦
      adim9_fibre_card_of_sheets (fun w ↦ (hfib w).toFinset) r y (hr y hy)
    have hPW : ∀ y ∈ W, ∀ i : ℕ, (P y).coeff i = if N - k ≤ i then
        (adim9_fibrePolynomial (n + 1) (hfib y).toFinset ℓ).coeff (i - (N - k)) else 0 := by
      intro y hy i
      simp only [P, hcard y hy, coeff_X_pow_mul']
    obtain ⟨hm, hdeg, hcb, -⟩ := hmon x hxW
    refine ⟨fun i ↦ ?_, ?_, ?_, fun i ↦ ?_⟩
    · have hev : (fun w ↦ (P w).coeff i) =ᶠ[𝓝 x] fun w ↦ if N - k ≤ i then
          (adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ).coeff (i - (N - k)) else 0 := by
        filter_upwards [hWo.mem_nhds hxW] with y hy
        exact hPW y hy i
      refine AnalyticAt.congr ?_ hev.symm
      split_ifs
      · exact hcoef _ x hxW
      · exact analyticAt_const
    · exact (monic_X_pow _).mul hm
    · simp only [P, hcard x hxW]
      rw [(monic_X_pow _).natDegree_mul hm, natDegree_X_pow, hdeg]
      omega
    · rw [hPW x hxW i]
      split_ifs
      · exact (hcb _).trans (pow_le_pow_right₀ (by linarith) hkN)
      · simp only [norm_zero]
        positivity
  -- continuation across the bad set, then across the vertex
  have hext : ∀ i : Fin N, ∃ b : (Fin (d + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ b (Metric.ball 0 ρ) ∧ EqOn b (fun w ↦ (P w).coeff i) D := by
    intro i
    obtain ⟨F, hF, hFf, hFb⟩ := adim9_local_hypersurface_extension d V E hE
      (fun w ↦ (P w).coeff i) (fun x hx ↦ (hlocal x hx).1 i) ((1 + R) ^ N)
      (fun x hx ↦ (hlocal x hx).2.2.2 i)
    refine ⟨Function.update F 0 (limUnder (𝓝[≠] 0) F),
      adim6_bounded_point_extension d (Metric.ball 0 ρ) Metric.isOpen_ball
        (Metric.mem_ball_self hρ) F hF ⟨_, hFb⟩, ?_⟩
    intro w hw
    have hw0 : w ≠ 0 := hw.1.2
    rw [Function.update_of_ne hw0]
    exact hFf hw
  choose b hb hbeq using hext
  refine ⟨b, hb, ?_⟩
  intro w hw t
  obtain ⟨-, hm, hdeg, -⟩ := hlocal w hw
  have hP : (P w).eval t = t ^ (N - (hfib w).toFinset.card) *
      (adim9_fibrePolynomial (n + 1) (hfib w).toFinset ℓ).eval t := by
    simp [P, eval_mul, eval_pow, eval_X]
  rw [← hP]
  conv_lhs => rw [hm.as_sum, hdeg]
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_range (fun i ↦ (P w).coeff i * t ^ i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hbeq i hw]

/-- Padding an enumeration of a finite fibre by the vertex to length N multiplies the
fibre polynomial by a power of X. -/
private theorem adim9_padded_prod (n N : ℕ) (s : Finset (Fin (n + 1) → ℂ)) (hN : s.card ≤ N)
    (ℓ : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) (x : ℂ) :
    ∏ j : Fin N, (x - ℓ (if h : (j : ℕ) < s.card then (s.equivFin.symm ⟨j, h⟩ : _) else 0)) =
      x ^ (N - s.card) * (adim9_fibrePolynomial (n + 1) s ℓ).eval x := by
  classical
  set F : ℕ → ℂ := fun i ↦
    x - ℓ (if h : i < s.card then (s.equivFin.symm ⟨i, h⟩ : _) else 0)
  rw [Fin.prod_univ_eq_prod_range F, ← Nat.add_sub_cancel' hN, Finset.prod_range_add,
    Nat.add_sub_cancel_left, mul_comm]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ ↦ x) fun i _ ↦ by simp [F],
      Finset.prod_const, Finset.card_range]
  · rw [← Fin.prod_univ_eq_prod_range F]
    simp only [F, Fin.is_lt, ↓reduceDIte, Fin.eta, adim9_fibrePolynomial, eval_prod, eval_sub,
      eval_X, eval_C]
    rw [← Finset.prod_coe_sort s]
    exact Equiv.prod_comp s.equivFin.symm (fun z : s ↦ x - ℓ z)

/-- Over a padded good base (at most N local sheets off a set lying locally in nowhere
locally zero hypersurfaces, whose preimage is dense in the cone), finitely many monic
observable equations cut out the cone near the vertex. -/
private theorem adim9_vertex_equations_of_padded_base (n d N : ℕ)
    (C : Set (Fin (n + 1) → ℂ)) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (ρ : ℝ) (hρ : 0 < ρ) (E : Set (Fin (d + 1) → ℂ))
    (hE : ∀ x ∈ Metric.ball 0 ρ \ {0}, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧
      W ⊆ Metric.ball 0 ρ \ {0} ∧ ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0})
    (hsheets : ∀ x ∈ (Metric.ball 0 ρ \ {0}) \ E, ∃ k, k ≤ N ∧
      ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ E ∧
      (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z)
    (hdense : ∀ z ∈ C, L z ∈ Metric.ball 0 ρ →
      z ∈ closure (C ∩ L ⁻¹' ((Metric.ball 0 ρ \ {0}) \ E))) :
    ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ (0 : Fin (n + 1) → ℂ) ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ insert 0 C ↔ ∀ j, f j z = 0) := by
  classical
  set B := Metric.ball (0 : Fin (d + 1) → ℂ) ρ
  set D := (B \ {0}) \ E
  set G := C ∩ L ⁻¹' D
  obtain ⟨c, hc0, hc⟩ := adim9_cone_norm_le_of_proper n d C hscale L hproper hcentral
  have hins : IsClosed (insert 0 C) := adim9_closed_insert_zero_of_closed_punctured C hclosed
  have hcard : ∀ w ∈ D, (hfib w).toFinset.card ≤ N := by
    intro w hw
    obtain ⟨k, hkN, W, r, -, hwW, -, -, hr⟩ := hsheets w hw
    rw [adim9_fibre_card_of_sheets (fun w ↦ (hfib w).toFinset) r w (hr w hwW)]
    exact hkN
  let ℓ : Fin (n * N + 1) → (Fin (n + 1) → ℂ) →L[ℂ] ℂ := fun t ↦
    ∑ i : Fin (n + 1), (((t : ℕ) : ℂ) ^ (i : ℕ)) •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i
  have hℓ : ∀ t z, ℓ t z = ∑ i : Fin (n + 1), ((t : ℕ) : ℂ) ^ (i : ℕ) * z i := by
    intro t z
    simp [ℓ, sum_apply]
  choose b hb heq using fun t ↦ adim9_cone_padded_coefficients n d N C L hfib c hc0.le hc ρ hρ
    E hE hsheets (ℓ t)
  let f : Fin (n * N + 1) → (Fin (n + 1) → ℂ) → ℂ := fun t z ↦
    ℓ t z ^ N + ∑ i : Fin N, b t i (L z) * ℓ t z ^ (i : ℕ)
  set U := L ⁻¹' B
  have hUo : IsOpen U := Metric.isOpen_ball.preimage L.continuous
  have hfa : ∀ t, AnalyticOnNhd ℂ (f t) U := by
    intro t z hz
    have hℓa : AnalyticAt ℂ (ℓ t) z := (ℓ t).analyticAt z
    refine (hℓa.pow N).add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
    exact ((hb t i (L z) hz).comp (L.analyticAt z)).mul (hℓa.pow _)
  have hfG : ∀ t, ∀ y ∈ G, f t y = 0 := by
    intro t y hy
    have h := heq t (L y) hy.2 (ℓ t y)
    simp only [f, ← h, adim9_fibrePolynomial, eval_prod, eval_sub, eval_X, eval_C]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := y) ?_ (sub_self _))
    rw [Finite.mem_toFinset]
    exact ⟨mem_insert_of_mem _ hy.1, rfl⟩
  have h0G : (0 : Fin (n + 1) → ℂ) ∈ closure G := by
    obtain ⟨x, hx⟩ := hne
    have htend : Tendsto (fun s : ℂ ↦ s • x) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℂ ↦ s • x) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℂ))).smul_const x
      exact this.mono_left nhdsWithin_le_nhds
    have hLt : Tendsto (fun s : ℂ ↦ L (s • x)) (𝓝[≠] 0) (𝓝 0) := by
      have := (L.continuous.tendsto 0).comp htend
      rw [map_zero] at this
      exact this
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s • x ∈ closure G := by
      filter_upwards [hLt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)),
        self_mem_nhdsWithin] with s hs hs0
      exact hdense _ (hscale s hs0 x hx) hs
    simpa [closure_closure] using mem_closure_of_tendsto htend hev
  have hfwd : ∀ t, ∀ z ∈ U, z ∈ closure G → f t z = 0 := by
    intro t z hz hzG
    exact ((hfa t z hz).continuousAt.continuousWithinAt).eq_const_of_mem_closure hzG (hfG t)
  have hDdense : ∀ w ∈ B, w ∈ closure D := by
    have hpunct : ∀ w ∈ B \ {0}, w ∈ closure D := by
      intro w hw
      rw [mem_closure_iff_frequently]
      obtain ⟨W, hWo, hwW, hWB, δ, -, hnz, hEW⟩ := hE w hw
      exact ((Filter.not_eventually.mp (hnz w hwW)).and_eventually (hWo.mem_nhds hwW)).mono
        fun v hv ↦ ⟨hWB hv.2, fun hvE ↦ hv.1 (hEW ⟨hvE, hv.2⟩)⟩
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      have := Module.punctured_nhds_neBot ℂ (Fin (d + 1) → ℂ) (0 : Fin (d + 1) → ℂ)
      have hev : ∀ᶠ v in 𝓝[≠] (0 : Fin (d + 1) → ℂ), v ∈ closure D := by
        filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hw),
          self_mem_nhdsWithin] with v hv hv0
        exact hpunct v ⟨hv, hv0⟩
      have hfr : ∃ᶠ v in 𝓝 (0 : Fin (d + 1) → ℂ), v ∈ closure D :=
        hev.frequently.filter_mono nhdsWithin_le_nhds
      simpa [closure_closure] using mem_closure_iff_frequently.mpr hfr
    · exact hpunct w ⟨hw, hw0⟩
  have hbwd : ∀ z ∈ U, (∀ t, f t z = 0) → z ∈ insert 0 C := by
    intro z hz hf0
    obtain ⟨ws, hwsD, hws⟩ := mem_closure_iff_seq_limit.mp (hDdense (L z) hz)
    let s : ℕ → Finset (Fin (n + 1) → ℂ) := fun m ↦ (hfib (ws m)).toFinset
    let Ep : ℕ → Fin N → Fin (n + 1) → ℂ := fun m j ↦
      if h : (j : ℕ) < (s m).card then ((s m).equivFin.symm ⟨j, h⟩ : _) else 0
    have hEmem : ∀ m j, Ep m j ∈ insert 0 C ∧ ‖Ep m j‖ ≤ c * ρ := by
      intro m j
      by_cases h : (j : ℕ) < (s m).card
      · have hmem := ((s m).equivFin.symm ⟨j, h⟩).2
        simp only [s, Finite.mem_toFinset] at hmem
        simp only [Ep, h, ↓reduceDIte]
        refine ⟨hmem.1, ?_⟩
        have hwm : ‖ws m‖ < ρ := by simpa [B] using (hwsD m).1.1
        calc _ ≤ c * ‖L _‖ := hc _ hmem.1
          _ ≤ c * ρ := by rw [hmem.2]; gcongr
      · simp only [Ep, h, ↓reduceDIte, norm_zero]
        exact ⟨mem_insert _ _, by positivity⟩
    have hEb : ∀ m, Ep m ∈ Metric.closedBall (0 : Fin N → Fin (n + 1) → ℂ) (c * ρ) := by
      intro m
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j ↦ (hEmem m j).2
    obtain ⟨Y, -, φ, hφ, hY⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hEb
    have hYj : ∀ j, Tendsto (fun m ↦ Ep (φ m) j) atTop (𝓝 (Y j)) :=
      fun j ↦ ((continuous_apply j).tendsto Y).comp hY
    have hYmem : ∀ j, Y j ∈ insert 0 C := fun j ↦
      hins.mem_of_tendsto (hYj j) (Eventually.of_forall fun m ↦ (hEmem (φ m) j).1)
    have hwφ : Tendsto (fun m ↦ ws (φ m)) atTop (𝓝 (L z)) := hws.comp hφ.tendsto_atTop
    have hroot : ∀ t, ∃ j, ℓ t z = ℓ t (Y j) := by
      intro t
      set x := ℓ t z
      have hlhs : Tendsto (fun m ↦ x ^ N + ∑ i : Fin N, b t i (ws (φ m)) * x ^ (i : ℕ))
          atTop (𝓝 (f t z)) := by
        refine tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ ↦ ?_)
        exact (((hb t i (L z) hz).continuousAt.tendsto).comp hwφ).mul tendsto_const_nhds
      have hrhs : Tendsto (fun m ↦ ∏ j, (x - ℓ t (Ep (φ m) j))) atTop
          (𝓝 (∏ j, (x - ℓ t (Y j)))) :=
        tendsto_finsetProd _ fun j _ ↦
          tendsto_const_nhds.sub (((ℓ t).continuous.tendsto _).comp (hYj j))
      have hEq : ∀ m, x ^ N + ∑ i : Fin N, b t i (ws (φ m)) * x ^ (i : ℕ) =
          ∏ j, (x - ℓ t (Ep (φ m) j)) := by
        intro m
        rw [← heq t (ws (φ m)) (hwsD (φ m)) x]
        exact (adim9_padded_prod n N (s (φ m)) (hcard _ (hwsD (φ m))) (ℓ t) x).symm
      have hlim := tendsto_nhds_unique (hlhs.congr hEq) hrhs
      rw [hf0 t] at hlim
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hlim.symm
      exact ⟨j, sub_eq_zero.mp hj⟩
    obtain ⟨j, hj⟩ := adim9_moment_observables_separate n N z Y fun t ↦ by
      obtain ⟨j, hj⟩ := hroot t
      exact ⟨j, by rw [← hℓ, ← hℓ, hj]⟩
    exact hj ▸ hYmem j
  refine ⟨U, hUo, by simp [U, B, hρ], n * N + 1, f, hfa, fun z hz ↦ ⟨fun h t ↦ ?_, hbwd z hz⟩⟩
  rcases h with h | h
  · exact hfwd t z hz (h ▸ h0G)
  · exact hfwd t z hz (hdense z h hz)

/-- Closed analyticity of the cone with its vertex from a padded good base. -/
private theorem adim9_cone_closed_analytic_of_padded_base (n d N : ℕ)
    (C : Set (Fin (n + 1) → ℂ)) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (ρ : ℝ) (hρ : 0 < ρ) (E : Set (Fin (d + 1) → ℂ))
    (hE : ∀ x ∈ Metric.ball 0 ρ \ {0}, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧
      W ⊆ Metric.ball 0 ρ \ {0} ∧ ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
        (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0})
    (hsheets : ∀ x ∈ (Metric.ball 0 ρ \ {0}) \ E, ∃ k, k ≤ N ∧
      ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ E ∧
      (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z)
    (hdense : ∀ z ∈ C, L z ∈ Metric.ball 0 ρ →
      z ∈ closure (C ∩ L ⁻¹' ((Metric.ball 0 ρ \ {0}) \ E))) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) := by
  obtain ⟨U, hUo, hU0, m, f, hf, hUf⟩ := adim9_vertex_equations_of_padded_base n d N C hne
    hclosed hscale L hproper hfib hcentral ρ hρ E hE hsheets hdense
  refine adim9_closed_analytic_of_vertex_equations (n + 1) C hclosed hloc
    ⟨U, hUo, ?_, ?_, m, f, hf, ?_⟩
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hU0
  · simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_target, subset_univ]
  · intro z hz
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq] using hUf z hz

/-- A finite injective ring map preserves Krull dimension. -/
private theorem adim9_ringKrullDim_eq_of_finite_injective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Finite)
    (hinj : Function.Injective f) : ringKrullDim R = ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have hint : Algebra.IsIntegral R S := ⟨hf.to_isIntegral⟩
  apply le_antisymm
  · rw [ringKrullDim, Order.krullDim]
    apply iSup_le
    intro l
    obtain ⟨Q, -, hQ, hQo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
      (⊥ : Ideal S) (by
        change RingHom.ker f ≤ l.head.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
        exact bot_le)
    have : Q.LiesOver l.head.asIdeal := ⟨hQo.symm⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L
  · exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun I J hIJ ↦ by
      change Ideal.under R I.asIdeal < Ideal.under R J.asIdeal
      exact Ideal.IsIntegral.under_lt_under hIJ

/-- Finite parameters into a domain of the parameter dimension are injective: a nonzero
kernel would cut the dimension of the parameter germ ring. -/
private theorem adim9_injective_of_finite_of_dim (d : ℕ) {B : Type*} [CommRing B] [IsDomain B]
    (θ : AnalyticGerm (d + 1) →+* B) (hθ : θ.Finite)
    (hdim : ringKrullDim B = ((d + 1 : ℕ) : WithBot ℕ∞)) : Function.Injective θ := by
  let : NoZeroDivisors (AnalyticGerm (d + 1)) := analyticGerm_noZeroDivisors_succ
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hfin : (RingHom.kerLift θ).Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker θ)) hθ
  have heq := adim9_ringKrullDim_eq_of_finite_injective _ hfin (RingHom.kerLift_injective θ)
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker θ))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  rw [heq, hdim, adim6_parameter_dimension] at hle
  have : (((d + 1 : ℕ) : ℕ∞) + 1 : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) := hle
  norm_cast at this
  simp at this

/-- Along injective parameters into a domain of dimension d + 1, a nonzero parameter
function cuts out a germ of dimension at most d. -/
private theorem adim9_dim_drop_of_injective (d : ℕ) {B : Type*} [CommRing B] [IsDomain B]
    (θ : AnalyticGerm (d + 1) →+* B) (hinj : Function.Injective θ)
    (hdim : ringKrullDim B = ((d + 1 : ℕ) : WithBot ℕ∞))
    (δ : AnalyticGerm (d + 1)) (hδ : δ ≠ 0) :
    ringKrullDim (B ⧸ Ideal.span {θ δ}) ≤ ((d : ℕ) : WithBot ℕ∞) := by
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff θ hinj).mpr hδ))
  rw [hdim, ← WithBot.coe_natCast, ← WithBot.coe_one] at hle
  generalize ringKrullDim (B ⧸ Ideal.span {θ δ}) = x at hle ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    rw [← WithBot.coe_add, WithBot.coe_le_coe] at hle
    induction e using ENat.recTopCoe with
    | top => simp at hle
    | coe e =>
      have h : e + 1 ≤ d + 1 := by exact_mod_cast hle
      exact_mod_cast (show e ≤ d by omega)

/-- Finitely many nowhere locally zero functions are simultaneously nonzero at points
accumulating at every common point of their domains. -/
private theorem adim9_frequently_ne_zero_finset {N ι : Type*} [TopologicalSpace N]
    (s : Finset ι) (W : ι → Set N) (hW : ∀ i ∈ s, IsOpen (W i)) (δ : ι → N → ℂ)
    (hδ : ∀ i ∈ s, ContinuousOn (δ i) (W i))
    (hnz : ∀ i ∈ s, ∀ y ∈ W i, ¬ (δ i =ᶠ[𝓝 y] fun _ ↦ 0))
    (x : N) (hx : ∀ i ∈ s, x ∈ W i) :
    ∃ᶠ v in 𝓝 x, ∀ i ∈ s, v ∈ W i ∧ δ i v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hT : IsOpen {v | ∀ i ∈ s, v ∈ W i ∧ δ i v ≠ 0} := by
      have : {v | ∀ i ∈ s, v ∈ W i ∧ δ i v ≠ 0} = ⋂ i ∈ s, (W i ∩ δ i ⁻¹' {0}ᶜ) := by
        ext v
        simp
      rw [this]
      exact isOpen_biInter_finset fun i hi ↦
        (hδ i (Finset.mem_insert_of_mem hi)).isOpen_inter_preimage
          (hW i (Finset.mem_insert_of_mem hi)) isOpen_compl_singleton
    have ha' := Finset.mem_insert_self a s
    have hfr := (ih (fun i hi ↦ hW i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hδ i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hnz i (Finset.mem_insert_of_mem hi))
      fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)).and_eventually
      ((hW a ha').mem_nhds (hx a ha'))
    rw [Filter.frequently_iff]
    intro o ho
    obtain ⟨o', ho'o, ho', hxo'⟩ := mem_nhds_iff.mp ho
    obtain ⟨y, ⟨hys, hya⟩, hyo⟩ := (hfr.and_eventually (ho'.mem_nhds hxo')).exists
    have hO : {v | ∀ i ∈ s, v ∈ W i ∧ δ i v ≠ 0} ∩ W a ∩ o' ∈ 𝓝 y :=
      ((hT.inter (hW a ha')).inter ho').mem_nhds ⟨⟨hys, hya⟩, hyo⟩
    obtain ⟨z, hδz, hz⟩ := ((Filter.not_eventually.mp (hnz a ha' y hya)).and_eventually hO).exists
    refine ⟨z, ho'o hz.2, fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨hz.1.2, hδz⟩
    · exact hz.1.1 i hi

/-- Local sheets of the cone over L near each point of a fibre glue, by properness, to a
neighbourhood of the fibre's parameter with one nowhere locally zero function off which
the whole fibre is given by boundedly many injective analytic sheets. -/
private theorem adim9_local_good_base (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hlocal : ∀ y ∈ C, ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z)
    (w₀ : Fin (d + 1) → ℂ) (hw₀ : w₀ ≠ 0) :
    ∃ (U : Set (Fin (d + 1) → ℂ)) (δ : (Fin (d + 1) → ℂ) → ℂ) (M : ℕ),
      IsOpen U ∧ w₀ ∈ U ∧ (0 : Fin (d + 1) → ℂ) ∉ U ∧ AnalyticOnNhd ℂ δ U ∧
      (∀ w ∈ U, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ v ∈ U, δ v ≠ 0 → ∃ k, k ≤ M ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ v ∈ W ∧ W ⊆ U ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v' ∈ W, Function.Injective (fun j ↦ r j v') ∧
          ∀ z, z ∈ (hfib v').toFinset ↔ ∃ j, r j v' = z := by
  classical
  set F := (hfib w₀).toFinset
  have hFC : ∀ y ∈ F, y ∈ C := by
    intro y hy
    rw [Finite.mem_toFinset] at hy
    rcases hy with ⟨rfl | hyC, hLy⟩
    · exact absurd (by simpa using hLy.symm) hw₀
    · exact hyC
  obtain ⟨Us, hUs, hdisj⟩ := (hfib w₀).t2_separation
  choose! O V δ K hOo hyO hOU hVo hyV hδ hnz hsh using fun y (hy : y ∈ F) ↦
    hlocal y (hFC y hy) (Us y) ((hUs y).2.mem_nhds (hUs y).1)
  -- parameters near w₀ have their whole fibre inside the union of the O y
  set p := fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val
  set S := {z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} | z.val ∉ ⋃ y ∈ F, O y}
  have hS : IsClosed S :=
    (isOpen_biUnion fun y hy ↦ hOo y hy).isClosed_compl.preimage continuous_subtype_val
  set U := (p '' S)ᶜ ∩ {0}ᶜ ∩ ⋂ y ∈ F, V y
  have hUo : IsOpen U :=
    ((hproper.isClosedMap S hS).isOpen_compl.inter isOpen_compl_singleton).inter
      (isOpen_biInter_finset fun y hy ↦ hVo y hy)
  have hcover : ∀ v ∈ U, ∀ z, z ∈ insert 0 C → L z = v → ∃ y ∈ F, z ∈ O y := by
    intro v hv z hz hzv
    by_contra h
    push Not at h
    exact hv.1.1 ⟨⟨z, hz⟩, by simpa [S] using h, hzv⟩
  have hw₀U : w₀ ∈ U := by
    refine ⟨⟨?_, hw₀⟩, mem_iInter₂.mpr fun y hy ↦ ?_⟩
    · rintro ⟨z, hzS, hzw⟩
      have hzF : z.val ∈ F := by
        rw [Finite.mem_toFinset]
        exact ⟨z.2, hzw⟩
      exact hzS (mem_biUnion hzF (hyO _ hzF))
    · have := hyV y hy
      rw [show L y = w₀ from ((Finite.mem_toFinset _).mp hy).2] at this
      exact this
  have hUV : ∀ v ∈ U, ∀ y ∈ F, v ∈ V y := fun v hv y hy ↦ mem_iInter₂.mp hv.2 y hy
  refine ⟨U, fun w ↦ ∏ y ∈ F, δ y w, ∑ y ∈ F, K y, hUo, hw₀U, fun h ↦ h.1.2 rfl,
    fun w hw ↦ Finset.analyticAt_fun_prod _ fun y hy ↦ hδ y hy w (hUV w hw y hy), ?_, ?_⟩
  · intro w hw hev
    have hfr := adim9_frequently_ne_zero_finset F V hVo δ
      (fun y hy ↦ (hδ y hy).continuousOn) hnz w fun y hy ↦ hUV w hw y hy
    obtain ⟨v, hv, hv0⟩ := (hfr.and_eventually hev).exists
    exact (Finset.prod_ne_zero_iff.mpr fun y hy ↦ (hv y hy).2) hv0
  · intro v hv hδv
    have hδy : ∀ y ∈ F, δ y v ≠ 0 := fun y hy ↦ Finset.prod_ne_zero_iff.mp hδv y hy
    choose! k hkK W r hWo hvW hra hr using fun y (hy : y ∈ F) ↦
      hsh y hy v (hUV v hv y hy) (hδy y hy)
    let σ := Σ y : F, Fin (k y)
    let e := Fintype.equivFin σ
    let R : Fin (Fintype.card σ) → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ) := fun j ↦
      r (e.symm j).1 (e.symm j).2
    set W' := U ∩ ⋂ y ∈ F, W y
    have hW'o : IsOpen W' := hUo.inter (isOpen_biInter_finset fun y hy ↦ hWo y hy)
    have hW'W : ∀ v' ∈ W', ∀ y ∈ F, v' ∈ W y := fun v' hv' y hy ↦ mem_iInter₂.mp hv'.2 y hy
    refine ⟨Fintype.card σ, ?_, W', R, hW'o, ⟨hv, mem_iInter₂.mpr fun y hy ↦ hvW y hy⟩,
      inter_subset_left, fun j ↦ ?_, fun v' hv' ↦ ⟨?_, fun z ↦ ?_⟩⟩
    · rw [Fintype.card_sigma, ← Finset.sum_coe_sort F K]
      exact Finset.sum_le_sum fun y _ ↦ by simpa using hkK y y.2
    · exact (hra _ (e.symm j).1.2 _).mono fun v' hv' ↦ hW'W v' hv' _ (e.symm j).1.2
    · have key : ∀ a b : σ, r a.1 a.2 v' = r b.1 b.2 v' → a = b := by
        rintro ⟨y₁, j₁⟩ ⟨y₂, j₂⟩ h
        have hz₁ := ((hr y₁ y₁.2 v' (hW'W v' hv' _ y₁.2)).2 _).mpr ⟨j₁, rfl⟩
        have hz₂ := ((hr y₂ y₂.2 v' (hW'W v' hv' _ y₂.2)).2 _).mpr ⟨j₂, h.symm⟩
        have hy : y₁ = y₂ := by
          by_contra hne
          have hne' : y₁.val ≠ y₂.val := fun h ↦ hne (Subtype.ext h)
          have hd := hdisj ((Finite.mem_toFinset _).mp y₁.2) ((Finite.mem_toFinset _).mp y₂.2)
            hne'
          exact Set.disjoint_left.mp hd (hOU _ y₁.2 hz₁.2.1) (hOU _ y₂.2 hz₂.2.1)
        subst hy
        have := (hr y₁ y₁.2 v' (hW'W v' hv' _ y₁.2)).1 h
        simp only at this
        subst this
        rfl
      intro i j hij
      exact e.symm.injective (key _ _ hij)
    · rw [Finite.mem_toFinset]
      constructor
      · rintro ⟨hz, hzv⟩
        have hv'0 : v' ≠ 0 := fun h ↦ hv'.1.1.2 h
        have hzC : z ∈ C := by
          rcases hz with rfl | hzC
          · exact absurd (by simpa using hzv.symm) hv'0
          · exact hzC
        obtain ⟨y, hy, hzy⟩ := hcover v' hv'.1 z hz hzv
        obtain ⟨j, hj⟩ := ((hr y hy v' (hW'W v' hv' y hy)).2 z).mp ⟨hzC, hzy, hzv⟩
        refine ⟨e ⟨⟨y, hy⟩, j⟩, ?_⟩
        change (fun x : σ ↦ r x.1 x.2 v') (e.symm (e _)) = z
        rw [e.symm_apply_apply]
        exact hj
      · rintro ⟨j, rfl⟩
        obtain ⟨hzC, -, hzv⟩ := ((hr _ (e.symm j).1.2 v'
          (hW'W v' hv' _ (e.symm j).1.2)).2 _).mpr ⟨(e.symm j).2, rfl⟩
        exact ⟨mem_insert_of_mem _ hzC, hzv⟩

/-- Scaling by a nonzero constant preserves the number of points in a punctured fibre of
a homogeneous cone. -/
private theorem adim9_fibre_card_smul (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (w : Fin (d + 1) → ℂ) (hw : w ≠ 0) (t : ℂ) (ht : t ≠ 0) :
    (hfib (t • w)).toFinset.card = (hfib w).toFinset.card := by
  classical
  have hC : ∀ z v, v ≠ 0 → z ∈ insert 0 C → L z = v → z ∈ C := by
    rintro z v hv (rfl | hz) hzv
    · exact absurd (by simpa using hzv.symm) hv
    · exact hz
  have htw : t • w ≠ 0 := smul_ne_zero ht hw
  have : (hfib (t • w)).toFinset = (hfib w).toFinset.image (fun z ↦ t • z) := by
    ext z
    simp only [Finite.mem_toFinset, Finset.mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨hz, hzw⟩
      refine ⟨t⁻¹ • z, ⟨mem_insert_of_mem _ (hscale _ (inv_ne_zero ht) z
        (hC z _ htw hz hzw)), ?_⟩, smul_inv_smul₀ ht z⟩
      rw [map_smul, hzw, inv_smul_smul₀ ht]
    · rintro ⟨y, ⟨hy, hyw⟩, rfl⟩
      exact ⟨mem_insert_of_mem _ (hscale t ht y (hC y w hw hy hyw)), by rw [map_smul, hyw]⟩
  rw [this, Finset.card_image_of_injective _ (smul_right_injective _ ht)]

open scoped Pointwise in
/-- From local sheets of the cone over L at its points, a padded good base on every
punctured ball: a uniform bound on the local sheet count (by homogeneity and compactness
of the unit sphere), the bad set locally inside nowhere locally zero hypersurfaces, and
local good bases around every nonzero parameter. -/
private theorem adim9_padded_base_of_local_sheets (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hlocal : ∀ y ∈ C, ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z)
    (ρ : ℝ) :
    ∃ (N : ℕ) (E : Set (Fin (d + 1) → ℂ)),
      (∀ x ∈ Metric.ball 0 ρ \ {0}, ∃ W : Set (Fin (d + 1) → ℂ), IsOpen W ∧ x ∈ W ∧
        W ⊆ Metric.ball 0 ρ \ {0} ∧ ∃ δ : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ δ W ∧
          (∀ y ∈ W, ¬ (δ =ᶠ[𝓝 y] fun _ ↦ 0)) ∧ E ∩ W ⊆ {y | δ y = 0}) ∧
      (∀ x ∈ (Metric.ball 0 ρ \ {0}) \ E, ∃ k, k ≤ N ∧
        ∃ (W : Set (Fin (d + 1) → ℂ)) (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ x ∈ W ∧ W ⊆ (Metric.ball 0 ρ \ {0}) \ E ∧
        (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
          ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z) ∧
      ∀ w₀ : Fin (d + 1) → ℂ, w₀ ≠ 0 → ∃ (U : Set (Fin (d + 1) → ℂ))
        (δ : (Fin (d + 1) → ℂ) → ℂ), IsOpen U ∧ w₀ ∈ U ∧ (0 : Fin (d + 1) → ℂ) ∉ U ∧
        AnalyticOnNhd ℂ δ U ∧ (∀ w ∈ U, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
        ∀ v ∈ U, δ v ≠ 0 → v ∉ E := by
  classical
  let Good : (Fin (d + 1) → ℂ) → Prop := fun v ↦ ∃ (k : ℕ) (W : Set (Fin (d + 1) → ℂ))
    (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
    IsOpen W ∧ v ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
    ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
      ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z
  have hA := adim9_local_good_base n d C L hproper hfib hlocal
  have hgoodA : ∀ w₀ : Fin (d + 1) → ℂ, w₀ ≠ 0 → ∃ (U : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (M : ℕ), IsOpen U ∧ w₀ ∈ U ∧
      (0 : Fin (d + 1) → ℂ) ∉ U ∧ AnalyticOnNhd ℂ δ U ∧
      (∀ w ∈ U, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ v ∈ U, δ v ≠ 0 → Good v ∧ (hfib v).toFinset.card ≤ M := by
    intro w₀ hw₀
    obtain ⟨U, δ, M, hUo, hw₀U, h0U, hδ, hnz, hsh⟩ := hA w₀ hw₀
    refine ⟨U, δ, M, hUo, hw₀U, h0U, hδ, hnz, fun v hv hδv ↦ ?_⟩
    obtain ⟨k, hkM, W, r, hWo, hvW, -, hra, hr⟩ := hsh v hv hδv
    refine ⟨⟨k, W, r, hWo, hvW, hra, hr⟩, ?_⟩
    rw [adim9_fibre_card_of_sheets (fun w ↦ (hfib w).toFinset) r v (hr v hvW)]
    exact hkM
  -- a uniform bound on the sheet count over good parameters
  choose! U δ M hUo hw₀U h0U hδ hnz hUgood using hgoodA
  have hsphere : Metric.sphere (0 : Fin (d + 1) → ℂ) 1 ⊆ ⋃ w ∈ Metric.sphere 0 1, U w :=
    fun w hw ↦ mem_biUnion hw (hw₀U w (ne_zero_of_mem_unit_sphere ⟨w, hw⟩))
  obtain ⟨T, hTS, hTfin, hTcov⟩ :=
    (isCompact_sphere (0 : Fin (d + 1) → ℂ) 1).elim_finite_subcover_image
    (fun w hw ↦ hUo w (ne_zero_of_mem_unit_sphere ⟨w, hw⟩)) hsphere
  set N := ∑ w ∈ hTfin.toFinset, M w
  have hbound : ∀ v, v ≠ 0 → ∀ (k : ℕ) (W : Set (Fin (d + 1) → ℂ))
      (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)), IsOpen W → v ∈ W →
      (∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ (hfib y).toFinset ↔ ∃ j, r j y = z) → k ≤ N := by
    intro v hv k W r hWo hvW hr
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set t : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ)
    have ht : t ≠ 0 := by simp [t, hnv.ne']
    have htv : t • v ∈ Metric.sphere (0 : Fin (d + 1) → ℂ) 1 := by
      simp [t, norm_smul, Complex.norm_real, hnv.ne']
    obtain ⟨w, hwT, htvw⟩ := mem_iUnion₂.mp (hTcov htv)
    have hwS := hTS hwT
    have hw0 : w ≠ 0 := ne_zero_of_mem_unit_sphere ⟨w, hwS⟩
    have hO : t • W ∩ U w ∈ 𝓝 (t • v) :=
      ((hWo.smul₀ ht).inter (hUo w hw0)).mem_nhds ⟨smul_mem_smul_set hvW, htvw⟩
    obtain ⟨u, hδu, ⟨v', hv'W, rfl⟩, huU⟩ :=
      ((Filter.not_eventually.mp (hnz w hw0 _ htvw)).and_eventually hO).exists
    have hv'0 : v' ≠ 0 := by
      rintro rfl
      exact h0U w hw0 (by simpa using huU)
    have hcard := (hUgood w hw0 _ huU hδu).2
    rw [adim9_fibre_card_smul n d C hscale L hfib v' hv'0 t ht,
      adim9_fibre_card_of_sheets (fun w ↦ (hfib w).toFinset) r v' (hr v' hv'W)] at hcard
    refine hcard.trans ?_
    exact Finset.single_le_sum (f := M) (fun _ _ ↦ Nat.zero_le _)
      ((Finite.mem_toFinset hTfin).mpr hwT)
  refine ⟨N, {v | ¬ Good v}, ?_, ?_, fun w₀ hw₀ ↦ ⟨U w₀, δ w₀, hUo w₀ hw₀, hw₀U w₀ hw₀,
    h0U w₀ hw₀, hδ w₀ hw₀, hnz w₀ hw₀, fun v hv hδv hvE ↦ hvE (hUgood w₀ hw₀ v hv hδv).1⟩⟩
  · intro x hx
    have hBo : IsOpen (Metric.ball (0 : Fin (d + 1) → ℂ) ρ \ {0}) :=
      Metric.isOpen_ball.sdiff isClosed_singleton
    refine ⟨U x ∩ (Metric.ball 0 ρ \ {0}), (hUo x hx.2).inter hBo, ⟨hw₀U x hx.2, hx⟩,
      inter_subset_right, δ x, (hδ x hx.2).mono inter_subset_left,
      fun y hy ↦ hnz x hx.2 y hy.1, ?_⟩
    rintro v ⟨hvE, hvU, -⟩
    by_contra hδv
    exact hvE (hUgood x hx.2 v hvU hδv).1
  · rintro x ⟨hxB, hxG⟩
    simp only [mem_ofPred_eq, not_not] at hxG
    obtain ⟨k, W, r, hWo, hxW, hra, hr⟩ := hxG
    have hBo : IsOpen (Metric.ball (0 : Fin (d + 1) → ℂ) ρ \ {0}) :=
      Metric.isOpen_ball.sdiff isClosed_singleton
    refine ⟨k, hbound x hxB.2 k W r hWo hxW hr, W ∩ (Metric.ball 0 ρ \ {0}), r,
      hWo.inter hBo, ⟨hxW, hxB⟩, fun v hv ↦ ⟨hv.2, ?_⟩,
      fun j ↦ (hra j).mono inter_subset_left, fun y hy ↦ hr y hy.1⟩
    simp only [mem_ofPred_eq, not_not]
    exact ⟨k, W ∩ (Metric.ball 0 ρ \ {0}), r, hWo.inter hBo, hv,
      fun j ↦ (hra j).mono inter_subset_left, fun y hy ↦ hr y hy.1⟩

/-- Closed analyticity of the cone with its vertex from local sheets over L at its points
and thinness of the preimages of hypersurfaces (no piece of the cone lies over a nowhere
locally zero analytic hypersurface). -/
private theorem adim9_cone_closed_analytic_of_local_sheets (n d : ℕ)
    (C : Set (Fin (n + 1) → ℂ)) (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (hlocal : ∀ y ∈ C, ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z)
    (hthin : ∀ y ∈ C, ∀ V : Set (Fin (d + 1) → ℂ), IsOpen V → L y ∈ V →
      ∀ h : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ h V →
        (∀ w ∈ V, ¬ (h =ᶠ[𝓝 w] fun _ ↦ 0)) →
        y ∈ closure (C ∩ L ⁻¹' {w | w ∈ V ∧ h w ≠ 0})) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) := by
  obtain ⟨N, E, hE, hsheets, hgood⟩ :=
    adim9_padded_base_of_local_sheets n d C hscale L hproper hfib hlocal 1
  refine adim9_cone_closed_analytic_of_padded_base n d N C hne hclosed hscale hloc L hproper
    hfib hcentral 1 one_pos E hE hsheets fun z hz hzB ↦ ?_
  have hLz : L z ≠ 0 := by
    intro h
    have : z ∈ (L ⁻¹' {0}) ∩ insert 0 C := ⟨h, mem_insert_of_mem _ hz⟩
    rw [hcentral, mem_singleton_iff] at this
    exact hzero (this ▸ hz)
  obtain ⟨U, δ, hUo, hzU, h0U, hδ, hnz, hUE⟩ := hgood (L z) hLz
  refine closure_mono ?_ (hthin z hz (U ∩ Metric.ball 0 1) (hUo.inter Metric.isOpen_ball)
    ⟨hzU, hzB⟩ δ (hδ.mono inter_subset_left) fun w hw ↦ hnz w hw.1)
  rintro y ⟨hyC, hyV, hδy⟩
  refine ⟨hyC, ⟨hyV.2, fun h ↦ h0U ?_⟩, hUE _ hyV.1 hδy⟩
  rw [← mem_singleton_iff.mp h]
  exact hyV.1

/-- No neighbourhood of a point of C lies over a hypersurface that is not locally zero at
its parameter, once L gives injective parameters on one component of the germ of C there. -/
private theorem adim9_thin_of_injective_parameters (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (y : Fin (n + 1) → ℂ)
    (Q : Ideal (AnalyticGerm (n + 1)))
    (hQ : Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes)
    (θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q)) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
      Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk Q b)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hyV : L y ∈ V)
    (h : (Fin (d + 1) → ℂ) → ℂ) (hh : AnalyticAt ℂ h (L y))
    (hnz : ¬ (h =ᶠ[𝓝 (L y)] fun _ ↦ 0)) :
    y ∈ closure (C ∩ L ⁻¹' {w | w ∈ V ∧ h w ≠ 0}) := by
  by_contra hy
  rw [mem_closure_iff_frequently, Filter.not_frequently] at hy
  have hev : ∀ᶠ z in 𝓝 y, z ∈ C → h (L z) = 0 := by
    filter_upwards [hy, L.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hyV)]
      with z hz hzV hzC
    by_contra hne
    exact hz ⟨hzC, hzV, hne⟩
  have htr : Tendsto (fun z : Fin (n + 1) → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
    simpa using ((continuous_const_add y).tendsto (0 : Fin (n + 1) → ℂ))
  have hev0 : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), y + z ∈ C → h (L y + L z) = 0 := by
    simpa [map_add] using htr.eventually hev
  set h' : (Fin (d + 1) → ℂ) → ℂ := fun w ↦ h (L y + w)
  have ha' : AnalyticAt ℂ h' 0 :=
    hh.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  have hg : AnalyticAt ℂ (fun z ↦ h' (L z)) 0 :=
    ha'.comp_of_eq (L.analyticAt 0) (by simp)
  let a : AnalyticGerm (d + 1) := ⟨Germ.ofFun h', h', ha', rfl⟩
  let b : AnalyticGerm (n + 1) := ⟨Germ.ofFun (fun z ↦ h' (L z)), _, hg, rfl⟩
  have hθ := hcomp a h' ha' rfl b rfl
  have hb : b ∈ Q := by
    refine hQ.1.2 ?_
    change Germ.ofFun (fun z ↦ y + z ∈ C) ≤ (Germ.ofFun (fun z ↦ h' (L z))).map (· = 0)
    rw [Germ.map_coe, Germ.coe_le]
    filter_upwards [hev0] with z hz hzC
    exact hz hzC
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, ← map_zero θ] at hθ
  have ha0 := congrArg Subtype.val (hinj hθ)
  have he : h' =ᶠ[𝓝 0] fun _ ↦ 0 := Germ.coe_eq.mp ha0
  apply hnz
  have htr' : Tendsto (fun v : Fin (d + 1) → ℂ ↦ v - L y) (𝓝 (L y)) (𝓝 0) := by
    simpa using ((continuous_sub_right (L y)).tendsto (L y))
  filter_upwards [htr'.eventually he] with v hv
  simpa [h'] using hv

/-- Thinness of preimages of hypersurfaces at every point of a pure cone, from finite
parameters along L on one component of the germ at each point. -/
private theorem adim9_thin_of_finite_parameters (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hfinpar : ∀ y ∈ C, ∃ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b) :
    ∀ y ∈ C, ∀ V : Set (Fin (d + 1) → ℂ), IsOpen V → L y ∈ V →
      ∀ h : (Fin (d + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ h V →
        (∀ w ∈ V, ¬ (h =ᶠ[𝓝 w] fun _ ↦ 0)) →
        y ∈ closure (C ∩ L ⁻¹' {w | w ∈ V ∧ h w ≠ 0}) := by
  intro y hy V hV hyV h hh hnz
  obtain ⟨Q, hQ, θ, hθ, hcomp⟩ := hfinpar y hy
  have : Q.IsPrime := hQ.1.1
  have hinj := adim9_injective_of_finite_of_dim d θ hθ (hpure y hy Q hQ)
  refine adim9_thin_of_injective_parameters n d C L y Q hQ θ hinj (fun a h' ha' hra b hb ↦
    hcomp a h' ha' hra b ?_) V hV hyV h (hh (L y) hyV) (hnz (L y) hyV)
  simpa [map_add] using hb

/-- Finite parameters along L on one component of the germ at every point of the cone,
from local equations and finite fibres of L. -/
private theorem adim9_hfinpar_of_premises (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) :
    ∀ y ∈ C, ∃ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b := by
  intro y hyC
  have hiso : ∀ᶠ y' in 𝓝 y, y' ∈ C → L y' = L y → y' = y := by
    have hcl : IsClosed ({z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = L y} \ {y}) :=
      ((hfib (L y)).sdiff).isClosed
    filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl)] with y' hy' hy'C hy'L
    by_contra hne
    exact hy' ⟨⟨mem_insert_of_mem 0 hy'C, hy'L⟩, hne⟩
  obtain ⟨U, hU, hyU, -, m, f, hf, hUC⟩ := hloc y hyC
  obtain ⟨Q, hQ, hfin⟩ := adim9_local_finite n d C y hyC U hU hyU m f hf hUC L hiso
  refine ⟨Q, hQ, _, hfin, fun a h _ ha b hb ↦ ?_⟩
  have hb' : Germ.ofFun (fun z ↦ h (L z)) = b.val := by simpa [map_add] using hb
  change Ideal.Quotient.mk Q (adim9_pb L a) = Ideal.Quotient.mk Q b
  rw [show adim9_pb L a = b from Subtype.ext ((adim9_pb_rep L a h ha).symm.trans hb')]

/-- Finite parameters along L on every component of the germ at every point of the cone,
from local equations and finite fibres of L. -/
private theorem adim9_hfinpar_all_of_premises (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) :
    ∀ y ∈ C, ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b := by
  intro y hyC Q hQ
  have hiso : ∀ᶠ y' in 𝓝 y, y' ∈ C → L y' = L y → y' = y := by
    have hcl : IsClosed ({z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = L y} \ {y}) :=
      ((hfib (L y)).sdiff).isClosed
    filter_upwards [hcl.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl)] with y' hy' hy'C hy'L
    by_contra hne
    exact hy' ⟨⟨mem_insert_of_mem 0 hy'C, hy'L⟩, hne⟩
  obtain ⟨U, hU, hyU, -, m, f, hf, hUC⟩ := hloc y hyC
  have hfin := adim9_local_finite_all n d C y hyC U hU hyU m f hf hUC L hiso Q hQ
  refine ⟨_, hfin, fun a h _ ha b hb ↦ ?_⟩
  have hb' : Germ.ofFun (fun z ↦ h (L z)) = b.val := by simpa [map_add] using hb
  change Ideal.Quotient.mk Q (adim9_pb L a) = Ideal.Quotient.mk Q b
  rw [show adim9_pb L a = b from Subtype.ext ((adim9_pb_rep L a h ha).symm.trans hb')]

/-- The amended vertex extension from two pointwise inputs at the points of the pure cone:
local sheets over L off a local discriminant, and finite parameters along L on one
component of the germ. -/
private theorem adim9_cone_vertex_extension_of_local_data (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (hlocal : ∀ y ∈ C, ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z)
    (hfinpar : ∀ y ∈ C, ∃ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) :=
  adim9_cone_closed_analytic_of_local_sheets n d C hzero hne hclosed hscale hloc L hproper
    hfib hcentral hlocal (adim9_thin_of_finite_parameters n d C L hpure hfinpar)

open scoped ContDiff in
/-- An analytic branch of roots through a simple root of a polynomial with analytic
coefficients. -/
private theorem adim9_root_branch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (p : Polynomial (E → ℂ)) (w₀ : E)
    (hp : ∀ i, AnalyticAt ℂ (p.coeff i) w₀) (t₀ : ℂ)
    (h0 : p.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) w₀) t₀ = 0)
    (h1 : p.derivative.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) w₀) t₀ ≠ 0) :
    ∃ τ : E → ℂ, AnalyticAt ℂ τ w₀ ∧ τ w₀ = t₀ ∧
      ∀ᶠ v in 𝓝 w₀, p.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) v) (τ v) = 0 := by
  set F : E × ℂ → ℂ := fun x ↦ p.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) x.1) x.2 with hFdef
  have hFsum : F = fun x ↦ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i x.1 * x.2 ^ i := by
    funext x
    simp only [hFdef, Polynomial.eval₂_eq_sum_range, Pi.evalRingHom_apply]
  have hF : AnalyticAt ℂ F (w₀, t₀) := by
    rw [hFsum]
    refine Finset.analyticAt_fun_sum _ fun i _ ↦ ?_
    exact ((hp i).comp_of_eq analyticAt_fst rfl).mul (analyticAt_snd.pow i)
  have cdf : ContDiffAt ℂ ω F (w₀, t₀) := hF.contDiffAt
  set c : ℂ := p.derivative.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) w₀) t₀
  have hline : HasDerivAt (fun s : ℂ ↦ F (w₀, s)) c t₀ := by
    have h := (p.map (Pi.evalRingHom (fun _ : E ↦ ℂ) w₀)).hasDerivAt t₀
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h
    exact h
  have hcomp : HasFDerivAt (fun s : ℂ ↦ F (w₀, s))
      ((fderiv ℂ F (w₀, t₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)) t₀ := by
    have hi : HasFDerivAt (fun s : ℂ ↦ ((w₀, s) : E × ℂ)) (ContinuousLinearMap.inr ℂ E ℂ) t₀ :=
      (hasFDerivAt_const w₀ t₀).prodMk (hasFDerivAt_id t₀)
    exact (cdf.differentiableAt (by simp)).hasFDerivAt.comp t₀ hi
  have heq : (fderiv ℂ F (w₀, t₀)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ((ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c h1) : ℂ ≃L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) := by
    rw [hcomp.unique hline.hasFDerivAt]
    ext
    simp
  have if₂ : ((fderiv ℂ F (w₀, t₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible :=
    ⟨_, heq.symm⟩
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨cdf.implicitFunction pn if₂, (cdf.contDiffAt_implicitFunction pn if₂).analyticAt,
    cdf.implicitFunction_apply_self pn if₂, ?_⟩
  filter_upwards [cdf.eventually_apply_implicitFunction pn if₂] with v hv
  rw [show p.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) v) (cdf.implicitFunction pn if₂ v) =
    F (v, cdf.implicitFunction pn if₂ v) from rfl, hv]
  exact h0


/-- A polynomial with analytic coefficients, evaluated along an analytic function. -/
private theorem adim9_analyticAt_eval₂ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : Polynomial (E → ℂ)) (τ : E → ℂ) (w : E)
    (hp : ∀ i, AnalyticAt ℂ (p.coeff i) w) (hτ : AnalyticAt ℂ τ w) :
    AnalyticAt ℂ (fun v ↦ p.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) v) (τ v)) w := by
  have h : (fun v ↦ p.eval₂ (Pi.evalRingHom (fun _ : E ↦ ℂ) v) (τ v)) =
      fun v ↦ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i v * τ v ^ i := by
    funext v
    simp only [Polynomial.eval₂_eq_sum_range, Pi.evalRingHom_apply]
  rw [h]
  exact Finset.analyticAt_fun_sum _ fun i _ ↦ (hp i).mul (hτ.pow i)

/-- As many distinct roots as the degree are all the roots. -/
private theorem adim9_roots_exhaust (p : Polynomial ℂ) (hp : p ≠ 0) (m : ℕ) (hm : p.natDegree ≤ m)
    (S : Finset ℂ) (hS : S.card = m) (hroot : ∀ s ∈ S, p.eval s = 0) (x : ℂ)
    (hx : p.eval x = 0) : x ∈ S := by
  classical
  have hsub : S ⊆ p.roots.toFinset := fun s hs ↦
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hroot s hs))
  have hcard : p.roots.toFinset.card ≤ S.card := by
    rw [hS]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans hm)
  rw [Finset.eq_of_subset_of_card_le hsub hcard]
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hx)

/-- Off the discriminants and the separating functions, the points of C near y over a
parameter are enumerated by analytic sheets through the simple roots of the primitive
relations of the components. -/
private theorem adim9_sheets_at_good_parameter (N D : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Set (Fin N → ℂ)) (y : Fin N → ℂ) (L : (Fin N → ℂ) →L[ℂ] (Fin D → ℂ))
    (ε₀ : ℝ) (Ω : Set (Fin D → ℂ)) (hΩ : IsOpen Ω)
    (s : ι → (Fin N → ℂ) → Prop) (ℓ : ι → (Fin N → ℂ) →L[ℂ] ℂ)
    (q b c : ι → Polynomial ((Fin D → ℂ) → ℂ)) (Δ : ι → (Fin D → ℂ) → ℂ)
    (r : ι → Fin N → Polynomial ((Fin D → ℂ) → ℂ)) (α : ι → ι → (Fin D → ℂ) → ℂ)
    (m : ι → ℕ)
    (hreal : ∀ w ∈ Ω, ∀ i t, Δ i w ≠ 0 →
      (q i).eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin N → ℂ := fun k ↦
        (r i k).eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) t / Δ i w
      ‖z‖ < ε₀ ∧ L z = w ∧ ℓ i z = t ∧ s i z)
    (hpt : ∀ z : Fin N → ℂ, ‖z‖ < ε₀ → ∀ i, s i z →
      (q i).eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) (L z)) (ℓ i z) = 0 ∧
      ∀ k, Δ i (L z) * z k =
        (r i k).eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) (L z)) (ℓ i z))
    (hsep : ∀ z : Fin N → ℂ, ‖z‖ < ε₀ → ∀ i j, i ≠ j → s i z → s j z → α i j (L z) = 0)
    (hcover : ∀ z : Fin N → ℂ, ‖z‖ < ε₀ → (y + z ∈ C ↔ ∃ i, s i z))
    (hbez : ∀ w ∈ Ω, ∀ i,
      (b i).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) *
          (q i).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) +
        (c i).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) *
          ((q i).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).derivative =
        Polynomial.C (Δ i w))
    (hmonic : ∀ w ∈ Ω, ∀ i, ((q i).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).Monic ∧
      ((q i).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).natDegree = m i)
    (hqan : ∀ w ∈ Ω, ∀ i k, AnalyticAt ℂ ((q i).coeff k) w)
    (hran : ∀ w ∈ Ω, ∀ i j k, AnalyticAt ℂ ((r i j).coeff k) w)
    (hΔan : ∀ w ∈ Ω, ∀ i, AnalyticAt ℂ (Δ i) w)
    (hαan : ∀ w ∈ Ω, ∀ i j, AnalyticAt ℂ (α i j) w)
    (w₀ : Fin D → ℂ) (hw₀ : w₀ ∈ Ω) (hΔw₀ : ∀ i, Δ i w₀ ≠ 0)
    (hαw₀ : ∀ i j, i ≠ j → α i j w₀ ≠ 0) :
    ∃ k, k ≤ ∑ i, m i ∧ ∃ (W : Set (Fin D → ℂ)) (σ : Fin k → (Fin D → ℂ) → (Fin N → ℂ)),
      IsOpen W ∧ w₀ ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (σ j) W) ∧
      ∀ v ∈ W, Function.Injective (fun j ↦ σ j v) ∧
        ∀ z, (z ∈ C ∧ z ∈ Metric.ball y ε₀ ∧ L z = L y + v) ↔ ∃ j, σ j v = z := by
  classical
  let ev : (Fin D → ℂ) → ((Fin D → ℂ) → ℂ) →+* ℂ :=
    fun w ↦ Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w
  have hne : ∀ w ∈ Ω, ∀ i, (q i).map (ev w) ≠ 0 := fun w hw i ↦ (hmonic w hw i).1.ne_zero
  let S : ι → Finset ℂ := fun i ↦ ((q i).map (ev w₀)).roots.toFinset
  have hSroot : ∀ i, ∀ t ∈ S i, (q i).eval₂ (ev w₀) t = 0 := by
    intro i t ht
    have := (Polynomial.mem_roots (hne w₀ hw₀ i)).mp (Multiset.mem_toFinset.mp ht)
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at this
  have hderiv : ∀ i t, (q i).eval₂ (ev w₀) t = 0 → (q i).derivative.eval₂ (ev w₀) t ≠ 0 := by
    intro i t ht hd
    have h := congrArg (Polynomial.eval t) (hbez w₀ hw₀ i)
    rw [Polynomial.derivative_map] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_map, Polynomial.eval_C]
      at h
    change _ * (q i).eval₂ (ev w₀) t + _ * (q i).derivative.eval₂ (ev w₀) t = _ at h
    rw [ht, hd, mul_zero, mul_zero, add_zero] at h
    exact hΔw₀ i h.symm
  have hScard : ∀ i, (S i).card = m i := by
    intro i
    have hsep : ((q i).map (ev w₀)).Separable := by
      refine ⟨Polynomial.C (Δ i w₀)⁻¹ * (b i).map (ev w₀),
        Polynomial.C (Δ i w₀)⁻¹ * (c i).map (ev w₀), ?_⟩
      have h := hbez w₀ hw₀ i
      calc Polynomial.C (Δ i w₀)⁻¹ * (b i).map (ev w₀) * (q i).map (ev w₀) +
            Polynomial.C (Δ i w₀)⁻¹ * (c i).map (ev w₀) * ((q i).map (ev w₀)).derivative =
          Polynomial.C (Δ i w₀)⁻¹ * ((b i).map (ev w₀) * (q i).map (ev w₀) +
            (c i).map (ev w₀) * ((q i).map (ev w₀)).derivative) := by ring
        _ = 1 := by
          rw [show (b i).map (ev w₀) * (q i).map (ev w₀) +
            (c i).map (ev w₀) * ((q i).map (ev w₀)).derivative = Polynomial.C (Δ i w₀) from h,
            ← Polynomial.C_mul, inv_mul_cancel₀ (hΔw₀ i), Polynomial.C_1]
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, (hmonic w₀ hw₀ i).2]
  let J := Σ i : ι, (S i)
  have hbranch : ∀ j : J, ∃ τ : (Fin D → ℂ) → ℂ, AnalyticAt ℂ τ w₀ ∧ τ w₀ = j.2 ∧
      ∀ᶠ v in 𝓝 w₀, (q j.1).eval₂ (ev v) (τ v) = 0 := fun j ↦
    adim9_root_branch (q j.1) w₀ (hqan w₀ hw₀ j.1) j.2 (hSroot _ _ j.2.2)
      (hderiv _ _ (hSroot _ _ j.2.2))
  choose τ hτan hτ0 hτroot using hbranch
  have hev : ∀ᶠ v in 𝓝 w₀, v ∈ Ω ∧ (∀ i, Δ i v ≠ 0) ∧ (∀ i j, i ≠ j → α i j v ≠ 0) ∧
      (∀ j : J, (q j.1).eval₂ (ev v) (τ j v) = 0) ∧
      (∀ j j' : J, j.1 = j'.1 → j ≠ j' → τ j v ≠ τ j' v) ∧
      (∀ j : J, AnalyticAt ℂ (τ j) v) := by
    refine (show ∀ᶠ v in 𝓝 w₀, v ∈ Ω from hΩ.mem_nhds hw₀).and ((Filter.eventually_all.mpr fun i ↦
      (hΔan w₀ hw₀ i).continuousAt.eventually_ne (hΔw₀ i)).and
      ((Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr fun i' ↦ ?_).and
      ((Filter.eventually_all.mpr hτroot).and
      ((Filter.eventually_all.mpr fun j ↦ Filter.eventually_all.mpr fun j' ↦ ?_).and
      (Filter.eventually_all.mpr fun j ↦ (hτan j).eventually_analyticAt)))))
    · by_cases h : i = i'
      · exact Filter.Eventually.of_forall fun _ h' ↦ absurd h h'
      · exact ((hαan w₀ hw₀ i i').continuousAt.eventually_ne (hαw₀ i i' h)).mono
          fun _ hv _ ↦ hv
    · by_cases h : j.1 = j'.1 ∧ j ≠ j'
      · have hval : τ j w₀ ≠ τ j' w₀ := by
          rw [hτ0, hτ0]
          obtain ⟨i, t⟩ := j
          obtain ⟨i', t'⟩ := j'
          obtain ⟨h1, h2⟩ := h
          dsimp only at h1
          subst h1
          intro ht
          exact h2 (Sigma.ext rfl (heq_of_eq (Subtype.ext ht)))
        exact ((ContinuousAt.ne_iff_eventually_ne (hτan j).continuousAt
          (hτan j').continuousAt).mp hval).mono fun _ hv _ _ ↦ hv
      · exact Filter.Eventually.of_forall fun _ h1 h2 ↦ absurd ⟨h1, h2⟩ h
  obtain ⟨W, hWsub, hWo, hw₀W⟩ := mem_nhds_iff.mp hev
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let recon : ι → (Fin D → ℂ) → ℂ → (Fin N → ℂ) := fun i w t k ↦
    (r i k).eval₂ (ev w) t / Δ i w
  refine ⟨Fintype.card J, ?_, W, fun j v ↦ y + recon (e j).1 v (τ (e j) v), hWo, hw₀W, ?_, ?_⟩
  · rw [Fintype.card_sigma]
    exact (Finset.sum_congr rfl fun i _ ↦ by rw [Fintype.card_coe, hScard i]).le
  · intro j v hv
    obtain ⟨hvΩ, hvΔ, -, -, -, hvτ⟩ := hWsub hv
    refine analyticAt_const.add (AnalyticAt.pi fun k ↦ ?_)
    exact (adim9_analyticAt_eval₂ _ _ v (hran v hvΩ _ k) (hvτ _)).div (hΔan v hvΩ _) (hvΔ _)
  intro v hv
  obtain ⟨hvΩ, hvΔ, hvα, hvroot, hvdist, -⟩ := hWsub hv
  have hrec (j : J) := hreal v hvΩ j.1 (τ j v) (hvΔ j.1) (hvroot j)
  refine ⟨?_, ?_⟩
  · intro j j' hjj'
    simp only [add_right_inj, recon] at hjj'
    obtain ⟨hn, hL, hℓ, hs⟩ := hrec (e j)
    obtain ⟨hn', hL', hℓ', hs'⟩ := hrec (e j')
    apply e.injective
    by_contra hne'
    by_cases h1 : (e j).1 = (e j').1
    · apply hvdist (e j) (e j') h1 hne'
      rw [← hℓ, ← hℓ', hjj', h1]
    · apply hvα _ _ h1
      have := hsep _ hn _ _ h1 hs (by rw [hjj']; exact hs')
      rwa [hL] at this
  · intro z
    constructor
    · rintro ⟨hzC, hzB, hzL⟩
      have hz' : ‖z - y‖ < ε₀ := by rwa [Metric.mem_ball, dist_eq_norm] at hzB
      have hLz : L (z - y) = v := by rw [map_sub, hzL, add_sub_cancel_left]
      obtain ⟨i, hi⟩ := (hcover _ hz').mp (by rwa [add_sub_cancel])
      obtain ⟨hroot, hcoord⟩ := hpt _ hz' i hi
      rw [hLz] at hroot hcoord
      have hmem : ℓ i (z - y) ∈ (S i).attach.image (fun t ↦ τ ⟨i, t⟩ v) := by
        refine adim9_roots_exhaust ((q i).map (ev v)) (hne v hvΩ i) (m i)
          (hmonic v hvΩ i).2.le _ ?_ ?_ _ ?_
        · rw [Finset.card_image_of_injective, Finset.card_attach, hScard i]
          intro t t' htt'
          by_contra hne'
          exact hvdist ⟨i, t⟩ ⟨i, t'⟩ rfl (fun h ↦ hne' (eq_of_heq (Sigma.mk.inj h).2)) htt'
        · intro x hx
          obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
          rw [Polynomial.eval_map]
          exact hvroot ⟨i, t⟩
        · rw [Polynomial.eval_map]
          exact hroot
      obtain ⟨t, -, hτt⟩ := Finset.mem_image.mp hmem
      refine ⟨e.symm ⟨i, t⟩, ?_⟩
      simp only [Equiv.apply_symm_apply]
      have hrz : recon i v (τ ⟨i, t⟩ v) = z - y := by
        funext k
        simp only [recon]
        rw [hτt, div_eq_iff (hvΔ i), mul_comm]
        exact (hcoord k).symm
      rw [hrz, add_sub_cancel]
    · rintro ⟨j, rfl⟩
      obtain ⟨hn, hL, -, hs⟩ := hrec (e j)
      refine ⟨(hcover _ hn).mpr ⟨_, hs⟩, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hn
      · rw [map_add, hL]


/-- A germ of the prime vanishes near the origin on every set germ inside its zero germ. -/
private theorem adim9_vanish_of_mem (N : ℕ) (P : Ideal (AnalyticGerm N))
    (s : (Fin N → ℂ) → Prop) (hs : (Germ.ofFun s : adim2_SetGerm N) ≤ adim2_zeroSet N P)
    (b : AnalyticGerm N) (hb : b ∈ P) (f : (Fin N → ℂ) → ℂ) (hf : Germ.ofFun f = b.val) :
    ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), s z → f z = 0 := by
  have hI : P ≤ adim2_ideal N (adim2_zeroSet N P) := (adim2_galois N _ P).mp le_rfl
  have h : (Germ.ofFun s : adim2_SetGerm N) ≤ adim2_zero N b := hs.trans (hI hb)
  change (Germ.ofFun s : adim2_SetGerm N) ≤ b.val.map (· = 0) at h
  rw [← hf, Germ.map_coe, Germ.coe_le] at h
  exact h

/-- Polynomial evaluation through compatible parameters is the class of the composed function. -/
private theorem adim9_primitive_eval_germ (N D : ℕ) (P : Ideal (AnalyticGerm N))
    (L : (Fin N → ℂ) →L[ℂ] (Fin D → ℂ))
    (θ : AnalyticGerm D →+* (AnalyticGerm N ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm D) (h : (Fin D → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm N,
      Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (ℓ : (Fin N → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm N) (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (T : Polynomial (AnalyticGerm D)) (t : Polynomial ((Fin D → ℂ) → ℂ))
    (ht : ∀ i, AnalyticAt ℂ (t.coeff i) 0 ∧ Germ.ofFun (t.coeff i) = (T.coeff i).val) :
    ∃ b : AnalyticGerm N,
      b.val = Germ.ofFun (fun z ↦ t.eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) (L z)) (ℓ z)) ∧
      T.eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b := by
  classical
  let B : ℕ → AnalyticGerm N := fun i ↦
    ⟨Germ.ofFun (fun z ↦ t.coeff i (L z)), _,
      (ht i).1.comp_of_eq (L.analyticAt 0) (map_zero L), rfl⟩
  have hdeg : T.natDegree < t.natDegree + 1 := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply Subtype.ext
    rw [← (ht i).2, Polynomial.coeff_eq_zero_of_natDegree_lt hi]
    rfl
  refine ⟨∑ i ∈ Finset.range (t.natDegree + 1), B i * v ^ i, ?_, ?_⟩
  · have h1 : (∑ i ∈ Finset.range (t.natDegree + 1), B i * v ^ i).val =
        (analyticGermSubring N).subtype (∑ i ∈ Finset.range (t.natDegree + 1), B i * v ^ i) :=
      rfl
    rw [h1, map_sum]
    simp only [map_mul, map_pow, Subring.subtype_apply, hv]
    change ∑ i ∈ Finset.range (t.natDegree + 1),
        Germ.coeRingHom (𝓝 (0 : Fin N → ℂ)) (fun z ↦ t.coeff i (L z)) *
          Germ.coeRingHom (𝓝 (0 : Fin N → ℂ)) (fun z ↦ ℓ z) ^ i = _
    simp only [← map_pow, ← map_mul, ← map_sum]
    refine congrArg (fun f : (Fin N → ℂ) → ℂ ↦ (f : Germ (𝓝 (0 : Fin N → ℂ)) ℂ))
      (funext fun z ↦ ?_)
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Polynomial.eval₂_eq_sum_range,
      Pi.evalRingHom_apply]
  · rw [Polynomial.eval₂_eq_sum_range' θ hdeg, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow,
      hcomp (T.coeff i) (t.coeff i) (ht i).1 (ht i).2 (B i) rfl]

/-- Points of the zero germ of the prime give roots of the primitive relation and the
reconstruction of their coordinates. -/
private theorem adim9_points_are_roots (N D : ℕ) (P : Ideal (AnalyticGerm N))
    (L : (Fin N → ℂ) →L[ℂ] (Fin D → ℂ))
    (θ : AnalyticGerm D →+* (AnalyticGerm N ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm D) (h : (Fin D → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm N,
      Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin N → AnalyticGerm N)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin N → ℂ ↦ z i))
    (ℓ : (Fin N → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm N) (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (Q : Polynomial (AnalyticGerm D)) (δ : AnalyticGerm D)
    (R : Fin N → Polynomial (AnalyticGerm D))
    (hmin : ∀ T : Polynomial (AnalyticGerm D),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin D → ℂ) → ℂ)) (Δ : (Fin D → ℂ) → ℂ)
    (r : Fin N → Polynomial ((Fin D → ℂ) → ℂ))
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧ Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : AnalyticAt ℂ Δ 0) (hΔrep : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, AnalyticAt ℂ ((r j).coeff i) 0 ∧
      Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (s : (Fin N → ℂ) → Prop) (hs : (Germ.ofFun s : adim2_SetGerm N) ≤ adim2_zeroSet N P) :
    ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), s z →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) (L z)) (ℓ z) = 0 ∧
      ∀ i, Δ (L z) * z i = (r i).eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) (L z)) (ℓ z) := by
  obtain ⟨b, hb, hbθ⟩ := adim9_primitive_eval_germ N D P L θ hcomp ℓ v hv Q q hq
  have hbP : b ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hbθ]
    exact (hmin Q).mpr dvd_rfl
  have hroot := adim9_vanish_of_mem N P s hs b hbP _ hb.symm
  have hrec (i : Fin N) : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), s z →
      Δ (L z) * z i -
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) (L z)) (ℓ z) = 0 := by
    obtain ⟨b', hb', hb'θ⟩ := adim9_primitive_eval_germ N D P L θ hcomp ℓ v hv (R i) (r i) (hr i)
    let e : AnalyticGerm N := ⟨Germ.ofFun (fun z ↦ Δ (L z)), _,
      hΔ.comp_of_eq (L.analyticAt 0) (map_zero L), rfl⟩
    have he : θ δ = Ideal.Quotient.mk P e := hcomp δ Δ hΔ hΔrep e rfl
    have hmem : e * c i - b' ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← he, hcoord i, hb'θ, sub_self]
    refine adim9_vanish_of_mem N P s hs _ hmem _ ?_
    change _ = (analyticGermSubring N).subtype (e * c i - b')
    rw [map_sub, map_mul]
    simp only [Subring.subtype_apply, hc, hb']
    rfl
  filter_upwards [hroot, Filter.eventually_all.mpr hrec] with z hz hz' hsz
  exact ⟨hz hsz, fun i ↦ sub_eq_zero.mp (hz' i hsz)⟩

/-- Two distinct components are separated off a nonzero parameter function. -/
private theorem adim9_separating_parameter (N D : ℕ) (P P' : Ideal (AnalyticGerm N))
    (hP : P.IsPrime) (hP'P : ¬ P' ≤ P)
    (L : (Fin N → ℂ) →L[ℂ] (Fin D → ℂ))
    (θ : AnalyticGerm D →+* (AnalyticGerm N ⧸ P)) (hθ : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm D) (h : (Fin D → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm N,
      Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (s s' : (Fin N → ℂ) → Prop)
    (hs : (Germ.ofFun s : adim2_SetGerm N) ≤ adim2_zeroSet N P)
    (hs' : (Germ.ofFun s' : adim2_SetGerm N) ≤ adim2_zeroSet N P') :
    ∃ a : AnalyticGerm D, a ≠ 0 ∧ ∃ α : (Fin D → ℂ) → ℂ, AnalyticAt ℂ α 0 ∧
      Germ.ofFun α = a.val ∧ ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), s z → s' z → α (L z) = 0 := by
  obtain ⟨h, hhP', hhP⟩ := Set.not_subset.mp hP'P
  have hne : Ideal.Quotient.mk P h ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨p, hpm, hp⟩ := hθ.to_isIntegral (Ideal.Quotient.mk P h)
  have hbot := Ideal.comap_ne_bot_of_root_mem hne
    (Ideal.mem_span_singleton_self (Ideal.Quotient.mk P h)) hpm.ne_zero hp
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp ha)
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨α, hα, hαrep⟩ := a.property
  obtain ⟨fu, hfu, hfurep⟩ := u.property
  obtain ⟨fh, hfh, hfhrep⟩ := h.property
  refine ⟨a, ha0, α, hα, hαrep, ?_⟩
  let e : AnalyticGerm N := ⟨Germ.ofFun (fun z ↦ α (L z)), _,
    hα.comp_of_eq (L.analyticAt 0) (map_zero L), rfl⟩
  have he : θ a = Ideal.Quotient.mk P e := hcomp a α hα hαrep e rfl
  have hmem : e - u * h ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← he, ← hu, sub_self]
  have h1 := adim9_vanish_of_mem N P s hs _ hmem (fun z ↦ α (L z) - fu z * fh z) (by
    change _ = (analyticGermSubring N).subtype (e - u * h)
    rw [map_sub, map_mul]
    simp only [Subring.subtype_apply, ← hfurep, ← hfhrep]
    rfl)
  have h2 := adim9_vanish_of_mem N P' s' hs' h hhP' fh hfhrep
  filter_upwards [h1, h2] with z hz1 hz2 hsz hs'z
  have := hz1 hsz
  rw [hz2 hs'z, mul_zero, sub_zero] at this
  exact this


open Classical in
/-- A chosen analytic representative of a germ, zero for zero and one for one. -/
private def adim9_rep {D : ℕ} (a : AnalyticGerm D) : (Fin D → ℂ) → ℂ :=
  if a = 0 then 0 else if a = 1 then 1 else a.property.choose

/-- The chosen representative is analytic at the origin and represents the germ. -/
private theorem adim9_rep_spec {D : ℕ} (a : AnalyticGerm D) :
    AnalyticAt ℂ (adim9_rep a) 0 ∧ Germ.ofFun (adim9_rep a) = a.val := by
  unfold adim9_rep
  split_ifs with h0 h1
  · subst h0
    exact ⟨analyticAt_const, rfl⟩
  · subst h1
    exact ⟨analyticAt_const, rfl⟩
  · exact a.property.choose_spec

/-- The chosen representative of zero is zero. -/
private theorem adim9_rep_zero {D : ℕ} : adim9_rep (0 : AnalyticGerm D) = 0 := by
  simp [adim9_rep]

/-- The chosen representative of one is one. -/
private theorem adim9_rep_one {D : ℕ} : adim9_rep (1 : AnalyticGerm D) = 1 := by
  have : Nontrivial (AnalyticGerm D) := (analyticGermValue D).domain_nontrivial
  simp [adim9_rep]

/-- Coefficientwise analytic representatives of a polynomial over analytic germs. -/
private def adim9_liftPoly {D : ℕ} (T : Polynomial (AnalyticGerm D)) :
    Polynomial ((Fin D → ℂ) → ℂ) :=
  ∑ i ∈ Finset.range (T.natDegree + 1), Polynomial.C (adim9_rep (T.coeff i)) * X ^ i

/-- The coefficients of the lift are the chosen representatives. -/
private theorem adim9_liftPoly_coeff {D : ℕ} (T : Polynomial (AnalyticGerm D)) (j : ℕ) :
    (adim9_liftPoly T).coeff j = adim9_rep (T.coeff j) := by
  classical
  simp only [adim9_liftPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at h; omega), adim9_rep_zero]

/-- The coefficients of the lift are analytic at the origin and represent the germs. -/
private theorem adim9_liftPoly_spec {D : ℕ} (T : Polynomial (AnalyticGerm D)) (j : ℕ) :
    AnalyticAt ℂ ((adim9_liftPoly T).coeff j) 0 ∧
      Germ.ofFun ((adim9_liftPoly T).coeff j) = (T.coeff j).val := by
  rw [adim9_liftPoly_coeff]
  exact adim9_rep_spec _

/-- Passing to germs undoes the lift. -/
private theorem adim9_liftPoly_map {D : ℕ} (T : Polynomial (AnalyticGerm D)) :
    (adim9_liftPoly T).map (Germ.coeRingHom (𝓝 (0 : Fin D → ℂ))) =
      T.map (analyticGermSubring D).subtype := by
  ext j
  simp only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply]
  exact (adim9_liftPoly_spec T j).2

/-- The representative of a monic polynomial stays monic of the same degree at every
parameter. -/
private theorem adim9_liftPoly_monic {D : ℕ} (T : Polynomial (AnalyticGerm D)) (hT : T.Monic)
    (w : Fin D → ℂ) :
    ((adim9_liftPoly T).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).Monic ∧
      ((adim9_liftPoly T).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).natDegree =
        T.natDegree := by
  have hc : ∀ j, ((adim9_liftPoly T).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).coeff j =
      adim9_rep (T.coeff j) w := by
    intro j
    rw [Polynomial.coeff_map, adim9_liftPoly_coeff]
    rfl
  have hle : ((adim9_liftPoly T).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).natDegree ≤
      T.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt hj, adim9_rep_zero]
    rfl
  have h1 : ((adim9_liftPoly T).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).coeff
      T.natDegree = 1 := by
    rw [hc, hT.coeff_natDegree, adim9_rep_one]
    rfl
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hle h1,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [h1]; exact one_ne_zero)⟩

/-- The representatives are analytic near the origin, all coefficients at once. -/
private theorem adim9_liftPoly_analytic {D : ℕ} (T : Polynomial (AnalyticGerm D)) :
    ∀ᶠ w in 𝓝 (0 : Fin D → ℂ), ∀ k, AnalyticAt ℂ ((adim9_liftPoly T).coeff k) w := by
  have h : ∀ᶠ w in 𝓝 (0 : Fin D → ℂ), ∀ k ∈ Finset.range (T.natDegree + 1),
      AnalyticAt ℂ ((adim9_liftPoly T).coeff k) w :=
    (Filter.eventually_all_finset _).mpr fun k _ ↦
      (adim9_liftPoly_spec T k).1.eventually_analyticAt
  filter_upwards [h] with w hw k
  by_cases hk : k ∈ Finset.range (T.natDegree + 1)
  · exact hw k hk
  · rw [adim9_liftPoly_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simp at hk; omega), adim9_rep_zero]
    exact analyticAt_const

/-- A germ Bezout identity holds for the representatives at every nearby parameter. -/
private theorem adim9_bezout_eventually {D : ℕ} (Q B C : Polynomial (AnalyticGerm D))
    (δ : AnalyticGerm D) (h : B * Q + C * Q.derivative = Polynomial.C δ) :
    ∀ᶠ w in 𝓝 (0 : Fin D → ℂ),
      (adim9_liftPoly B).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) *
          (adim9_liftPoly Q).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) +
        (adim9_liftPoly C).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) *
          ((adim9_liftPoly Q).map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w)).derivative =
        Polynomial.C (adim9_rep δ w) := by
  set E := adim9_liftPoly B * adim9_liftPoly Q +
    adim9_liftPoly C * (adim9_liftPoly Q).derivative - Polynomial.C (adim9_rep δ) with hE
  have hmap : E.map (Germ.coeRingHom (𝓝 (0 : Fin D → ℂ))) = 0 := by
    rw [hE, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, Polynomial.map_C, adim9_liftPoly_map, adim9_liftPoly_map,
      adim9_liftPoly_map, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, h, Polynomial.map_C, sub_eq_zero]
    congr 1
    exact (adim9_rep_spec δ).2.symm
  have hc : ∀ k, ∀ᶠ w in 𝓝 (0 : Fin D → ℂ), E.coeff k w = 0 := by
    intro k
    have := congrArg (fun p ↦ p.coeff k) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Germ.coe_coeRingHom] at this
    exact Germ.coe_eq.mp this
  have hall : ∀ᶠ w in 𝓝 (0 : Fin D → ℂ), ∀ k ∈ Finset.range (E.natDegree + 1),
      E.coeff k w = 0 := (Filter.eventually_all_finset _).mpr fun k _ ↦ hc k
  filter_upwards [hall] with w hw
  have hEw : E.map (Pi.evalRingHom (fun _ : Fin D → ℂ ↦ ℂ) w) = 0 := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hk : k ∈ Finset.range (E.natDegree + 1)
    · exact hw k hk
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega)]
      rfl
  rw [hE, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_C, sub_eq_zero, ← Polynomial.derivative_map] at hEw
  exact hEw

/-- The common zeros of the chosen generators of an ideal represent its zero germ. -/
private theorem adim9_generators_zeroSet {N : ℕ} (P : Ideal (AnalyticGerm N)) :
    (Germ.ofFun (fun z ↦ ∀ g ∈ adim2_generators N P, adim9_rep g z = 0) :
      adim2_SetGerm N) = adim2_zeroSet N P := by
  have hspan : Ideal.span (adim2_generators N P : Set (AnalyticGerm N)) = P :=
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian N) P).choose_spec
  have hg : ∀ g : AnalyticGerm N, adim2_zero N g =
      Germ.ofFun (fun z ↦ adim9_rep g z = 0) := by
    intro g
    change g.val.map (· = 0) = _
    rw [← (adim9_rep_spec g).2, Germ.map_coe]
    rfl
  apply le_antisymm
  · apply (adim2_galois N _ P).mpr
    refine hspan.symm.le.trans (Ideal.span_le.mpr fun g hgP ↦ ?_)
    rw [SetLike.mem_coe]
    change (Germ.ofFun (fun z ↦ ∀ g ∈ adim2_generators N P, adim9_rep g z = 0) :
      adim2_SetGerm N) ≤ adim2_zero N g
    rw [hg, Germ.coe_le]
    exact Filter.Eventually.of_forall fun z hz ↦ hz g hgP
  · obtain ⟨σ, hσ⟩ : ∃ σ : (Fin N → ℂ) → Prop, (Germ.ofFun σ : adim2_SetGerm N) =
        adim2_zeroSet N P := Quot.exists_rep _
    rw [← hσ, Germ.coe_le]
    have h : ∀ g ∈ adim2_generators N P, ∀ᶠ z in 𝓝 (0 : Fin N → ℂ),
        σ z → adim9_rep g z = 0 := by
      intro g hgP
      have hle : (Germ.ofFun σ : adim2_SetGerm N) ≤ adim2_zero N g := by
        rw [hσ]
        exact Finset.inf_le hgP
      rw [hg, Germ.coe_le] at hle
      exact hle
    filter_upwards [(Filter.eventually_all_finset _).mpr h] with z hz hσz g hgP
    exact hz g hgP hσz

/-- Near the anchor, a point lies in the set exactly when it lies in the common zeros of
the generators of one of the covering primes. -/
private theorem adim9_cover_eventually {N : ℕ} (C : Set (Fin N → ℂ)) (y : Fin N → ℂ)
    (F : Finset (Ideal (AnalyticGerm N)))
    (hcov : adim2_germ N C y = F.sup (adim2_zeroSet N))
    (hsub : ∀ P ∈ F, adim2_zeroSet N P ≤ adim2_germ N C y) :
    ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), (y + z ∈ C ↔
      ∃ P ∈ F, ∀ g ∈ adim2_generators N P, adim9_rep g z = 0) := by
  have h1 : adim2_germ N C y ≤ Germ.ofFun (fun z ↦
      ∃ P ∈ F, ∀ g ∈ adim2_generators N P, adim9_rep g z = 0) := by
    rw [hcov]
    apply Finset.sup_le
    intro P hP
    rw [← adim9_generators_zeroSet, Germ.coe_le]
    exact Filter.Eventually.of_forall fun z hz ↦ ⟨P, hP, hz⟩
  have h2 : ∀ P ∈ F, ∀ᶠ z in 𝓝 (0 : Fin N → ℂ),
      (∀ g ∈ adim2_generators N P, adim9_rep g z = 0) → y + z ∈ C := by
    intro P hP
    have := hsub P hP
    rw [← adim9_generators_zeroSet] at this
    exact Germ.coe_le.mp this
  have h1' : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), y + z ∈ C →
      ∃ P ∈ F, ∀ g ∈ adim2_generators N P, adim9_rep g z = 0 := Germ.coe_le.mp h1
  filter_upwards [h1', (Filter.eventually_all_finset _).mpr h2] with z hz1 hz2
  exact ⟨hz1, fun ⟨P, hP, hs⟩ ↦ hz2 P hP hs⟩

/-- A function analytic on a ball and not locally zero at its centre is nowhere locally
zero there. -/
private theorem adim9_not_locally_zero_ball {D : ℕ} (f : (Fin D → ℂ) → ℂ) (ε : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ε)) (h0 : ¬ (f =ᶠ[𝓝 0] fun _ ↦ 0)) :
    ∀ w ∈ Metric.ball (0 : Fin D → ℂ) ε, ¬ (f =ᶠ[𝓝 w] fun _ ↦ 0) := by
  intro w hw hz
  apply h0
  have hε : 0 < ε := lt_of_le_of_lt (norm_nonneg w) (by simpa using hw)
  have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : Fin D → ℂ) ε).isPreconnected hw hz
  filter_upwards [Metric.ball_mem_nhds (0 : Fin D → ℂ) hε] with x hx
  exact hall hx



/-- Local sheets of C over L at one point of C, from finite parameters along L on every
component of the germ of C there. -/
private theorem adim9_local_sheets_at (n d : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) (y : Fin (n + 1) → ℂ) (hy : y ∈ C)
    (hlocy : ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ y ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧ ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (hpurey : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hfiny : ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b) :
    ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z := by
  classical
  intro O' hO'
  obtain ⟨U, hU, hyU, m, f, hf, hA⟩ := hlocy
  have hdim : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P) := by
    intro P hP
    rw [hpurey P hP]
    exact_mod_cast Nat.succ_pos d
  obtain ⟨F, hFeq, hcov, hFP⟩ := adim7_component_comparison n C y hy U hU hyU m f hf hA hdim
  have hFmin : ∀ P ∈ F, P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes :=
    fun P hP ↦ by rw [← hFeq]; exact hP
  let : NoZeroDivisors (AnalyticGerm (d + 1)) := analyticGerm_noZeroDivisors_succ
  let : Nontrivial (AnalyticGerm (d + 1)) := (analyticGermValue (d + 1)).domain_nontrivial
  let cN : Fin (n + 1) → AnalyticGerm (n + 1) := fun i ↦
    ⟨Germ.ofFun (fun z ↦ z i), _,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).analyticAt 0, rfl⟩
  have hcN : ∀ i, (cN i).val = Germ.ofFun (fun z : Fin (n + 1) → ℂ ↦ z i) := fun _ ↦ rfl
  have hdata : ∀ P : F, ∃ (θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ P.1))
      (ℓ : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm (n + 1))
      (Q : Polynomial (AnalyticGerm (d + 1))) (δ : AnalyticGerm (d + 1))
      (R : Fin (n + 1) → Polynomial (AnalyticGerm (d + 1)))
      (B Cb : Polynomial (AnalyticGerm (d + 1))),
      P.1.IsPrime ∧ θ.Finite ∧
      (∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk P.1 b) ∧
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧ IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + Cb * Q.derivative = Polynomial.C δ ∧
      (∀ T : Polynomial (AnalyticGerm (d + 1)),
        T.eval₂ θ (Ideal.Quotient.mk P.1 v) = 0 ↔ Q ∣ T) ∧
      ∀ i, θ δ * Ideal.Quotient.mk P.1 (cN i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P.1 v) := by
    intro P
    have hP := hFmin P.1 P.2
    have hprime : P.1.IsPrime := hP.1.1
    obtain ⟨θ, hθ, hcomp⟩ := hfiny P.1 hP
    have hcomp' : ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L z)) = b.val → θ a = Ideal.Quotient.mk P.1 b :=
      fun a h ha hra b hb ↦ hcomp a h ha hra b (by simpa [map_add] using hb)
    have hinj := adim9_injective_of_finite_of_dim d θ hθ (hpurey P.1 hP)
    obtain ⟨ℓ, v, Q, δ, R, B, Cb, hv, -, hQ, hδ, hbez, hmin, hcoord⟩ :=
      adim7_primitive_form (n + 1) (d + 1) P.1 hprime L θ hθ hinj hcomp' cN hcN
    exact ⟨θ, ℓ, v, Q, δ, R, B, Cb, hprime, hθ, hcomp', hv, hQ, hδ, hbez, hmin, hcoord⟩
  choose θ ℓ v Q δ R B Cb hprime hθ hcomp hv hQ hδ hbez hmin hcoord using hdata
  let s : F → (Fin (n + 1) → ℂ) → Prop := fun P z ↦
    ∀ g ∈ adim2_generators (n + 1) P.1, adim9_rep g z = 0
  have hs : ∀ P : F, (Germ.ofFun (s P) : adim2_SetGerm (n + 1)) ≤
      adim2_zeroSet (n + 1) P.1 := fun P ↦ (adim9_generators_zeroSet P.1).le
  have hsepd : ∀ P P' : F, ∃ (α : (Fin (d + 1) → ℂ) → ℂ) (a : AnalyticGerm (d + 1)),
      AnalyticAt ℂ α 0 ∧ Germ.ofFun α = a.val ∧ a ≠ 0 ∧
      (P ≠ P' → ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), s P z → s P' z → α (L z) = 0) := by
    intro P P'
    by_cases hPP : P = P'
    · exact ⟨1, 1, analyticAt_const, rfl, one_ne_zero, fun h ↦ absurd hPP h⟩
    · have hle : ¬ P'.1 ≤ P.1 := by
        intro hle
        exact hPP (Subtype.ext (le_antisymm
          ((hFmin P.1 P.2).2 (hFmin P'.1 P'.2).1 hle) hle))
      obtain ⟨a, ha, α, hα, hαrep, hev⟩ := adim9_separating_parameter (n + 1) (d + 1) P.1 P'.1
        (hprime P) hle L (θ P) (hθ P) (hcomp P) (s P) (s P') (hs P) (hs P')
      exact ⟨α, a, hα, hαrep, ha, fun _ ↦ hev⟩
  choose α a hαan hαrep ha hαsep using hsepd
  let q : F → Polynomial ((Fin (d + 1) → ℂ) → ℂ) := fun P ↦ adim9_liftPoly (Q P)
  let bq : F → Polynomial ((Fin (d + 1) → ℂ) → ℂ) := fun P ↦ adim9_liftPoly (B P)
  let cq : F → Polynomial ((Fin (d + 1) → ℂ) → ℂ) := fun P ↦ adim9_liftPoly (Cb P)
  let Δ : F → (Fin (d + 1) → ℂ) → ℂ := fun P ↦ adim9_rep (δ P)
  let r : F → Fin (n + 1) → Polynomial ((Fin (d + 1) → ℂ) → ℂ) := fun P i ↦
    adim9_liftPoly (R P i)
  let offd : Finset (F × F) := Finset.univ.filter (fun x ↦ x.1 ≠ x.2)
  let Δt : (Fin (d + 1) → ℂ) → ℂ := fun w ↦ (∏ P, Δ P w) * ∏ x ∈ offd, α x.1 x.2 w
  have hΔt0 : ¬ (Δt =ᶠ[𝓝 0] fun _ ↦ 0) := by
    intro h
    have hX : (∏ P, δ P) * ∏ x ∈ offd, a x.1 x.2 ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun P _ ↦ hδ P)
        (Finset.prod_ne_zero_iff.mpr fun x _ ↦ ha x.1 x.2)
    apply hX
    apply Subtype.ext
    change (analyticGermSubring (d + 1)).subtype ((∏ P, δ P) * ∏ x ∈ offd, a x.1 x.2) =
      Germ.ofFun (fun _ : Fin (d + 1) → ℂ ↦ (0 : ℂ))
    rw [← Germ.coe_eq.mpr h]
    simp only [map_mul, map_prod, Subring.subtype_apply]
    simp_rw [← (adim9_rep_spec (δ _)).2, ← hαrep]
    change (∏ P, Germ.coeRingHom (𝓝 (0 : Fin (d + 1) → ℂ)) (Δ P)) *
        ∏ x ∈ offd, Germ.coeRingHom (𝓝 (0 : Fin (d + 1) → ℂ)) (α x.1 x.2) =
      Germ.coeRingHom (𝓝 (0 : Fin (d + 1) → ℂ)) Δt
    simp only [← map_prod, ← map_mul]
    refine congrArg (Germ.coeRingHom (𝓝 (0 : Fin (d + 1) → ℂ))) (funext fun w ↦ ?_)
    simp only [Pi.mul_apply, Finset.prod_apply, Δt]

  have hZ1 : ∀ P : F, ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), s P z →
      (q P).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) (L z)) (ℓ P z) = 0 ∧
      ∀ i, Δ P (L z) * z i =
        (r P i).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) (L z)) (ℓ P z) :=
    fun P ↦ adim9_points_are_roots (n + 1) (d + 1) P.1 L (θ P) (hcomp P) cN hcN (ℓ P) (v P)
      (hv P) (Q P) (δ P) (R P) (hmin P) (hcoord P) (q P) (Δ P) (r P)
      (adim9_liftPoly_spec _) (adim9_rep_spec _).1 (adim9_rep_spec _).2
      (fun _ ↦ adim9_liftPoly_spec _) (s P) (hs P)
  have hZ2 : ∀ P P' : F, ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ),
      P ≠ P' → s P z → s P' z → α P P' (L z) = 0 := by
    intro P P'
    by_cases h : P = P'
    · exact Filter.Eventually.of_forall fun _ h' ↦ absurd h h'
    · exact (hαsep P P' h).mono fun _ hz _ ↦ hz
  have hZ : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ),
      (∀ P : F, s P z →
        (q P).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) (L z)) (ℓ P z) = 0 ∧
        ∀ i, Δ P (L z) * z i =
          (r P i).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) (L z)) (ℓ P z)) ∧
      (∀ P P' : F, P ≠ P' → s P z → s P' z → α P P' (L z) = 0) ∧
      (y + z ∈ C ↔ ∃ P : F, s P z) := by
    filter_upwards [Filter.eventually_all.mpr hZ1,
      Filter.eventually_all.mpr fun P ↦ Filter.eventually_all.mpr (hZ2 P),
      adim9_cover_eventually C y F hcov (fun P hP ↦ (hFP P hP).1)] with z h1 h2 h3
    refine ⟨h1, h2, ?_⟩
    rw [h3]
    constructor
    · rintro ⟨P, hP, hsP⟩
      exact ⟨⟨P, hP⟩, hsP⟩
    · rintro ⟨P, hsP⟩
      exact ⟨P.1, P.2, hsP⟩
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff.mp hZ
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.mp hO'
  set ε₀ := min ε₁ ε₂ with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε₁ hε₂
  have hZε : ∀ z : Fin (n + 1) → ℂ, ‖z‖ < ε₀ → _ := fun z hz ↦
    hball₁ (show dist z 0 < ε₁ by rw [dist_zero_right]; exact hz.trans_le (min_le_left _ _))
  have hspan : ∀ P : F, ∀ g ∈ adim2_generators (n + 1) P.1, g ∈ P.1 := by
    intro P g hg
    have h : Ideal.span (adim2_generators (n + 1) P.1 : Set (AnalyticGerm (n + 1))) = P.1 :=
      ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian (n + 1)) P.1).choose_spec
    rw [← h]
    exact Ideal.subset_span hg
  have hW1 : ∀ P : F, ∀ᶠ w in 𝓝 (0 : Fin (d + 1) → ℂ), ∀ t : ℂ, Δ P w ≠ 0 →
      (q P).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin (n + 1) → ℂ := fun k ↦
        (r P k).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) t / Δ P w
      ‖z‖ < ε₀ ∧ L z = w ∧ ℓ P z = t ∧ s P z := by
    intro P
    have hreal := fun (g : AnalyticGerm (n + 1)) (hg : g ∈ P.1) ↦
      adim7_reconstructed_roots_realised (n + 1) (d + 1) P.1 (hprime P) L (θ P) (hθ P)
        (hcomp P) cN hcN (ℓ P) (v P) (hv P) (Q P) (δ P) (R P) (hmin P) (hcoord P) (q P) (Δ P)
        (r P) (fun i ↦ (adim9_liftPoly_spec _ i).2) (adim9_rep_spec _).2
        (fun j i ↦ (adim9_liftPoly_spec _ i).2) ε₀ hε₀ g hg (adim9_rep g)
        (adim9_rep_spec g).1 (adim9_rep_spec g).2
    filter_upwards [hreal 0 P.1.zero_mem, (Filter.eventually_all_finset _).mpr
      fun g hg ↦ hreal g (hspan P g hg)] with w h0 hg t hΔw ht
    obtain ⟨hn, hL, hℓ, -⟩ := h0 t hΔw ht
    exact ⟨hn, hL, hℓ, fun g hgP ↦ (hg g hgP t hΔw ht).2.2.2⟩
  have hW : ∀ᶠ w in 𝓝 (0 : Fin (d + 1) → ℂ),
      (∀ P : F, ∀ t : ℂ, Δ P w ≠ 0 →
        (q P).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) t = 0 →
        let z : Fin (n + 1) → ℂ := fun k ↦
          (r P k).eval₂ (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) t / Δ P w
        ‖z‖ < ε₀ ∧ L z = w ∧ ℓ P z = t ∧ s P z) ∧
      (∀ P : F, (bq P).map (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) *
          (q P).map (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) +
        (cq P).map (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w) *
          ((q P).map (Pi.evalRingHom (fun _ : Fin (d + 1) → ℂ ↦ ℂ) w)).derivative =
        Polynomial.C (Δ P w)) ∧
      (∀ P : F, ∀ k, AnalyticAt ℂ ((q P).coeff k) w) ∧
      (∀ (P : F) i k, AnalyticAt ℂ ((r P i).coeff k) w) ∧
      (∀ P : F, AnalyticAt ℂ (Δ P) w) ∧
      (∀ P P' : F, AnalyticAt ℂ (α P P') w) := by
    filter_upwards [Filter.eventually_all.mpr hW1,
      Filter.eventually_all.mpr fun P ↦ adim9_bezout_eventually (Q P) (B P) (Cb P) (δ P) (hbez P),
      Filter.eventually_all.mpr fun P ↦ adim9_liftPoly_analytic (Q P),
      Filter.eventually_all.mpr fun P ↦ Filter.eventually_all.mpr fun i ↦
        adim9_liftPoly_analytic (R P i),
      Filter.eventually_all.mpr fun P ↦ (adim9_rep_spec (δ P)).1.eventually_analyticAt,
      Filter.eventually_all.mpr fun P ↦ Filter.eventually_all.mpr fun P' ↦
        (hαan P P').eventually_analyticAt] with w h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.eventually_nhds_iff.mp hW
  have hWε : ∀ w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) ε₃, _ := fun w hw ↦
    hball₃ (by rwa [Metric.mem_ball] at hw)
  have hΔtan : AnalyticOnNhd ℂ Δt (Metric.ball 0 ε₃) := by
    intro w hw
    obtain ⟨-, -, -, -, h5, h6⟩ := hWε w hw
    exact (Finset.univ.analyticAt_fun_prod fun P _ ↦ h5 P).mul
      (offd.analyticAt_fun_prod fun x _ ↦ h6 x.1 x.2)
  have hshift : ∀ w ∈ Metric.ball (L y) ε₃, w - L y ∈ Metric.ball (0 : Fin (d + 1) → ℂ) ε₃ := by
    intro w hw
    rwa [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
  refine ⟨Metric.ball y ε₀, Metric.ball (L y) ε₃, fun w ↦ Δt (w - L y),
    ∑ P : F, (Q P).natDegree, Metric.isOpen_ball, Metric.mem_ball_self hε₀,
    (Metric.ball_subset_ball (min_le_right _ _)).trans hball₂, Metric.isOpen_ball,
    Metric.mem_ball_self hε₃, ?_, ?_, ?_⟩
  · intro w hw
    exact (hΔtan _ (hshift w hw)).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
  · intro w hw h
    apply adim9_not_locally_zero_ball Δt ε₃ hΔtan hΔt0 (w - L y) (hshift w hw)
    have ht : Tendsto (fun u : Fin (d + 1) → ℂ ↦ u + L y) (𝓝 (w - L y)) (𝓝 w) := by
      have hc : Continuous (fun u : Fin (d + 1) → ℂ ↦ u + L y) :=
        continuous_id.add continuous_const
      simpa using hc.tendsto (w - L y)
    filter_upwards [ht.eventually h] with u hu
    simpa using hu
  · intro w hw hδw
    have hw₀ := hshift w hw
    have hδw' : Δt (w - L y) ≠ 0 := hδw
    obtain ⟨hΔne, hαne⟩ := mul_ne_zero_iff.mp hδw'
    have hΔw₀ : ∀ P : F, Δ P (w - L y) ≠ 0 := fun P ↦
      Finset.prod_ne_zero_iff.mp hΔne P (Finset.mem_univ P)
    have hαw₀ : ∀ P P' : F, P ≠ P' → α P P' (w - L y) ≠ 0 := fun P P' h ↦
      Finset.prod_ne_zero_iff.mp hαne (P, P') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨k, hk, W, σ, hWo, hw₀W, hσan, hσ⟩ := adim9_sheets_at_good_parameter (n + 1) (d + 1)
      C y L ε₀ (Metric.ball 0 ε₃) Metric.isOpen_ball s ℓ q bq cq Δ r α
      (fun P ↦ (Q P).natDegree)
      (fun w hw ↦ (hWε w hw).1) (fun z hz ↦ (hZε z hz).1)
      (fun z hz ↦ (hZε z hz).2.1) (fun z hz ↦ (hZε z hz).2.2)
      (fun w hw ↦ (hWε w hw).2.1) (fun w _ P ↦ adim9_liftPoly_monic (Q P) (hQ P).1 w)
      (fun w hw ↦ (hWε w hw).2.2.1) (fun w hw ↦ (hWε w hw).2.2.2.1)
      (fun w hw ↦ (hWε w hw).2.2.2.2.1) (fun w hw ↦ (hWε w hw).2.2.2.2.2)
      (w - L y) hw₀ hΔw₀ hαw₀
    refine ⟨k, hk, (fun v ↦ v - L y) ⁻¹' W, fun j v ↦ σ j (v - L y),
      hWo.preimage (continuous_sub_right _), hw₀W, ?_, ?_⟩
    · intro j v hv
      exact (hσan j _ hv).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
    · intro v hv
      obtain ⟨hinj, henum⟩ := hσ (v - L y) hv
      refine ⟨hinj, fun z ↦ ?_⟩
      rw [← henum z, add_sub_cancel]


/-- Local sheets over L at every point of C, from finite parameters along L on every
component of the germ of C at every point. -/
private theorem adim9_hlocal_of_hfinpar (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hfinpar : ∀ y ∈ C, ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b) :
    ∀ y ∈ C, ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z := by
  intro y hy
  obtain ⟨U, hU, hyU, -, m, f, hf, hA⟩ := hloc y hy
  exact adim9_local_sheets_at n d C L y hy ⟨U, hU, hyU, m, f, hf, hA⟩ (hpure y hy)
    (hfinpar y hy)

/-- The amended vertex extension from local sheets over L alone: finite parameters
come from the premises. -/
private theorem adim9_cone_vertex_extension_of_hlocal (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (hlocal : ∀ y ∈ C, ∀ O' ∈ 𝓝 y, ∃ (O : Set (Fin (n + 1) → ℂ)) (V : Set (Fin (d + 1) → ℂ))
      (δ : (Fin (d + 1) → ℂ) → ℂ) (K : ℕ), IsOpen O ∧ y ∈ O ∧ O ⊆ O' ∧ IsOpen V ∧
      L y ∈ V ∧ AnalyticOnNhd ℂ δ V ∧ (∀ w ∈ V, ¬ (δ =ᶠ[𝓝 w] fun _ ↦ 0)) ∧
      ∀ w ∈ V, δ w ≠ 0 → ∃ k, k ≤ K ∧ ∃ (W : Set (Fin (d + 1) → ℂ))
        (r : Fin k → (Fin (d + 1) → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen W ∧ w ∈ W ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
        ∀ v ∈ W, Function.Injective (fun j ↦ r j v) ∧
          ∀ z, (z ∈ C ∧ z ∈ O ∧ L z = v) ↔ ∃ j, r j v = z) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) :=
  adim9_cone_vertex_extension_of_local_data n C hzero hne hclosed hscale hloc d L hpure
    hproper hfib hcentral hlocal (adim9_hfinpar_of_premises n C hloc d L hfib)

/-- The amended vertex extension from finite parameters along L on every component of the
germ at every point of the pure cone. -/
private theorem adim9_cone_vertex_extension_of_finite_parameters (n : ℕ)
    (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0})
    (hfinpar : ∀ y ∈ C, ∀ Q ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C y)).minimalPrimes,
      ∃ θ : AnalyticGerm (d + 1) →+* (AnalyticGerm (n + 1) ⧸ Q), θ.Finite ∧
      ∀ (a : AnalyticGerm (d + 1)) (h : (Fin (d + 1) → ℂ) → ℂ),
        AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
        Germ.ofFun (fun z ↦ h (L (y + z) - L y)) = b.val → θ a = Ideal.Quotient.mk Q b) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) := by
  refine adim9_cone_vertex_extension_of_local_data n C hzero hne hclosed hscale hloc d L hpure
    hproper hfib hcentral (adim9_hlocal_of_hfinpar n C hloc d L hpure hfinpar) ?_
  intro y hy
  have htop : adim2_ideal (n + 1) (adim2_germ (n + 1) C y) ≠ ⊤ := by
    intro htop
    have h1 : (1 : AnalyticGerm (n + 1)) ∈ adim2_ideal (n + 1) (adim2_germ (n + 1) C y) :=
      htop ▸ Submodule.mem_top
    change ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), y + z ∈ C → (1 : ℂ) = 0 at h1
    exact one_ne_zero (h1.self_of_nhds (by simpa using hy))
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes htop
  exact ⟨Q, hQ, hfinpar y hy Q hQ⟩

/-- Implication from a finite proper linear projection of the whole homogeneous
cone to vertex extension. Linearity supplies compatibility with scalar multiplication.
The cone is pure of the target dimension, and the projection maps the cone onto the target.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
cone proof of Chow; Demailly, Complex Analytic and Differential Geometry (2012),
II, proof of Theorem 8.7, pp. 119--120, bounded symmetric sheet coefficients. -/
theorem adim9_cone_vertex_extension_aux (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (honto : Function.Surjective
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hsurj : Function.Surjective L)
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0}) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) :=
  adim9_cone_vertex_extension_of_finite_parameters n C hzero hne hclosed hscale hloc d L hpure
    hproper hfib hcentral (adim9_hfinpar_all_of_premises n C hloc d L hfib)

/-- Finitely many cones closed analytic through the vertex have a closed analytic union.
Source: Schnell, Complex Manifolds (lecture notes), Definition 3.2;
finite unions of analytic sets, `IsClosedAnalytic.biUnion_finset`. -/
theorem adim9_cone_vertex_extension_finite_union_aux (n k : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (Cι : Fin k → Set (Fin (n + 1) → ℂ))
    (hcover : insert 0 C = ⋃ i, insert 0 (Cι i))
    (hext : ∀ i, IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 (Cι i))) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) := by
  rw [hcover]
  simpa only [Finset.mem_univ, iUnion_true] using
    IsClosedAnalytic.biUnion_finset Finset.univ (fun i _ ↦ hext i)

end HodgeLean.Foundations
