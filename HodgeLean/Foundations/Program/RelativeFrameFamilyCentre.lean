import HodgeLean.Foundations.Program.RelativeFrameFamilyGeometry

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The open locus where a continuous function differs from a specified value.
Source: Mathlib `isClosed_singleton`, `IsOpen.preimage`. -/
def rf7_nonzeroLocus {Y : Type} [TopologicalSpace Y] (q : Y → ℂ)
    (hq : Continuous q) (c : ℂ) : TopologicalSpace.Opens Y :=
  ⟨{y | q y ≠ c}, isClosed_singleton.isOpen_compl.preimage hq⟩

example {Y : Type} [TopologicalSpace Y] (q : Y → ℂ) (hq : Continuous q) (c : ℂ) (y : Y) :
    y ∈ rf7_nonzeroLocus q hq c ↔ q y ≠ c := Iff.rfl

theorem rf7_punctured_nhds_neBot {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : (𝓝[≠] x).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  apply mem_closure_iff.mpr
  intro N hN hxN
  obtain ⟨T, hTN, _, _, _, hne⟩ := b4cov_goodPoint (Module.finrank_self ℂ) x N (hN.mem_nhds hxN)
  obtain ⟨z, hz⟩ := hne
  exact ⟨z, hTN hz.1, hz.2⟩

theorem rf7_unique_centre_of_coordinate {C : Type} [TopologicalSpace C]
    [CompactSpace C] [T2Space C] {Y : Type} [TopologicalSpace Y] [T1Space Y]
    [ChartedSpace ℂ Y] (a : Y → C) (ha : Continuous a) (hai : Function.Injective a)
    (q : Y → ℂ) (hq : Continuous q)
    (f : C → OnePoint ℂ) (hf : Continuous f) (c : ℂ)
    (hfin : (f ⁻¹' {(c : OnePoint ℂ)}).Finite)
    (hproj : ∀ y : Y, f (a y) = (q y : OnePoint ℂ))
    (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 0 < k)
    [Nonempty (rf7_nonzeroLocus q hq c)]
    (v : rf7_nonzeroLocus q hq c → ℂ) (hv : IsOpenEmbedding v)
    (hrange : range v = {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ k < ρ})
    (hpower : ∀ y, q y.val = c + v y ^ k)
    (x y : Y) (hx : q x = c) (hy : q y = c) : x = y := by
  classical
  let U := rf7_nonzeroLocus q hq c
  let w : Y → ℂ := fun y ↦ if h : q y ≠ c then v ⟨y, h⟩ else 0
  have hwv (u : U) : w u.val = v u := by
    dsimp only [w]
    rw [dite_eq_left (show q u.val ≠ c from u.2)]
  have hwpow (u : Y) : w u ^ k = q u - c := by
    by_cases h : q u ≠ c
    · rw [show w u = v ⟨u, h⟩ by simp only [w, dite_eq_left h], hpower ⟨u, h⟩]
      ring
    · simp only [w, dite_eq_right h, zero_pow hk.ne', not_not] at *
      rw [h, sub_self]
  have hwzero (u : Y) : w u = 0 ↔ q u = c := by
    constructor
    · intro h
      have hp := hwpow u
      rw [h, zero_pow hk.ne'] at hp
      exact sub_eq_zero.mp hp.symm
    · intro h
      simp [w, h]
  have hwU : Continuous (w ∘ (Subtype.val : U → Y)) := by
    have heq : w ∘ (Subtype.val : U → Y) = v := funext hwv
    rw [heq]
    exact hv.continuous
  have hwpowcont : Continuous (fun u : Y ↦ w u ^ k) := by
    have heq : (fun u : Y ↦ w u ^ k) = fun u ↦ q u - c := funext hwpow
    rw [heq]
    exact hq.sub continuous_const
  have hw : Continuous w := by
    apply continuous_iff_continuousAt.mpr
    intro u
    by_cases hu : q u = c
    · exact rf7_continuousAt_zero_of_pow w k hk u ((hwzero u).mpr hu) hwpowcont.continuousAt
    · exact (rf7_nonzeroLocus q hq c).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
        (hwU.continuousAt (x := ⟨u, hu⟩))
  have hqfin : (q ⁻¹' {c}).Finite := by
    have hh := Set.Finite.preimage hai.injOn hfin
    apply hh.subset
    intro u hu
    change f (a u) = (c : OnePoint ℂ)
    rw [hproj, show q u = c from hu]
  haveI : ∀ u : Y, (𝓝[≠] u).NeBot := rf7_punctured_nhds_neBot
  have hdense : Dense {u : Y | w u ≠ 0} := by
    have hh : Dense (q ⁻¹' {c})ᶜ := by
      simpa only [Set.sdiff_eq, Set.univ_inter] using dense_univ.sdiff_finite hqfin
    have heq : (q ⁻¹' {c})ᶜ = {u : Y | w u ≠ 0} := by
      ext u
      exact (not_congr (hwzero u)).symm
    rw [heq] at hh
    exact hh
  let e : OpenPartialHomeomorph U ℂ := hv.toOpenPartialHomeomorph v
  let j : ℂ → C := fun z ↦ a (e.symm z).val
  have hetarget : e.target = {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ k < ρ} := by
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_target] using hrange
  have hrootopen : IsOpen {z : ℂ | ‖z‖ ^ k < ρ} :=
    isOpen_lt (continuous_norm.pow k) continuous_const
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hrootopen 0 (by change ‖(0 : ℂ)‖ ^ k < ρ; simpa only [norm_zero, zero_pow hk.ne'] using hρ)
  have hRtarget : Metric.ball (0 : ℂ) R \ {0} ⊆ e.target := by
    intro z hz
    rw [hetarget]
    exact ⟨hz.2, hRsub hz.1⟩
  have hj : ContinuousOn j (Metric.ball (0 : ℂ) R \ {0}) :=
    ((ha.comp continuous_subtype_val).comp_continuousOn e.continuousOn_symm).mono hRtarget
  have hjpower (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R \ {0}) :
      f (j z) = ((c + z ^ k : ℂ) : OnePoint ℂ) := by
    have he := hv.toOpenPartialHomeomorph_right_inv (f := v) (by
      rw [← IsOpenEmbedding.toOpenPartialHomeomorph_target (f := v)]
      exact hRtarget hz)
    change f (a (e.symm z).val) = _
    rw [hproj, hpower, he]
  obtain ⟨z₀, _, hjlim⟩ := rf7_punctured_power_limit f hf c hfin R hR k hk j hj hjpower
  have hinv (u : Y) (hu : w u ≠ 0) : j (w u) = a u := by
    have hqu : q u ≠ c := fun h ↦ hu ((hwzero u).mpr h)
    have hwu : w u = v ⟨u, hqu⟩ := by simp only [w, dite_eq_left hqu]
    rw [hwu]
    change a (e.symm (v ⟨u, hqu⟩)).val = a u
    rw [show e.symm (v ⟨u, hqu⟩) = ⟨u, hqu⟩ from hv.toOpenPartialHomeomorph_left_inv]
  have heqx : a x = z₀ := rf7_zero_fibre_of_inverse_limit a ha
    w hw hdense j z₀ hjlim hinv x ((hwzero x).mpr hx)
  have heqy : a y = z₀ := rf7_zero_fibre_of_inverse_limit a ha
    w hw hdense j z₀ hjlim hinv y ((hwzero y).mpr hy)
  exact hai (heqx.trans heqy.symm)


theorem rf7_disc_cover_coordinate {Y : Type} [TopologicalSpace Y] [T1Space Y]
    [ChartedSpace ℂ Y] [ConnectedSpace Y] (q : Y → ℂ) (hq : Continuous q)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hrange : ∀ y, q y ∈ Metric.ball c ρ)
    (hfin : ∀ z, (q ⁻¹' {z}).Finite) (hnonzero : ∃ y, q y ≠ c)
    (hcov : IsCoveringMapOn q (Metric.ball c ρ \ {c})) :
    ∃ k : ℕ, 0 < k ∧ ∃ v : rf7_nonzeroLocus q hq c → ℂ,
      IsOpenEmbedding v ∧ range v = {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ k < ρ} ∧
      ∀ y, q y.val = c + v y ^ k := by
  classical
  let U := rf7_nonzeroLocus q hq c
  obtain ⟨y₀, hy₀⟩ := hnonzero
  let u₀ : U := ⟨y₀, hy₀⟩
  letI : Nonempty U := ⟨u₀⟩
  letI : LocallyPathConnectedSpace Y := ChartedSpace.locallyPathConnectedSpace ℂ Y
  letI : LocallyPathConnectedSpace U := U.isOpen.locallyPathConnectedSpace
  have hUset : (U : Set Y) = univ \ q ⁻¹' {c} := by
    ext y
    exact (and_iff_right trivial).symm
  have hUconn : IsPreconnected (U : Set Y) := by
    rw [hUset]
    exact b4cov_isPreconnected_diff_finite isOpen_univ isPreconnected_univ (hfin c)
      (fun y _ ↦ b4cov_goodPoint (Module.finrank_self ℂ) y)
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp ⟨⟨y₀, hy₀⟩, hUconn⟩
  letI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  let S := Metric.ball c ρ \ {c}
  let qU : U → ℂ := fun u ↦ q u.val
  have hUr (u : U) : qU u ∈ S := ⟨hrange u.val, u.2⟩
  have hpre : (U : Set Y) = q ⁻¹' S := by
    ext y
    exact ⟨fun h ↦ ⟨hrange y, h⟩, fun h ↦ h.2⟩
  let p : U → S := fun u ↦ ⟨qU u, hUr u⟩
  have hp : IsCoveringMap p := by
    exact hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)
  have hS : IsOpen S := Metric.isOpen_ball.sdiff isClosed_singleton
  have hcovU : IsCoveringMapOn qU S :=
    IsCoveringMapOn.of_isCoveringMap_subtype hS hUr hp
  have hfinU (z : ℂ) : (qU ⁻¹' {z}).Finite := by
    have hh : ((Subtype.val : U → Y) ⁻¹' (q ⁻¹' {z})).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn (hfin z)
    exact hh
  let k := Nat.card (qU ⁻¹' {qU u₀})
  have hk : 0 < k := by
    letI := (hfinU (qU u₀)).fintype
    exact Nat.card_pos_iff.mpr ⟨⟨⟨u₀, rfl⟩⟩, inferInstance⟩
  letI : PathConnectedSpace S := rf7_puncturedDisc_pathConnected c c ρ (by simpa using hρ)
  have hdeg (z : ℂ) (hz : z ∈ S) : Nat.card (qU ⁻¹' {z}) = k := by
    let z' : S := ⟨z, hz⟩
    let γ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath z' (p u₀))
    let E := Equiv.ofBijective (hp.monodromy γ) (hp.monodromy_bijective γ)
    calc
      Nat.card (qU ⁻¹' {z}) = Nat.card (p ⁻¹' {z'}) :=
        (rf7_codRestrict_fibre_card qU S hUr z').symm
      _ = Nat.card (p ⁻¹' {p u₀}) := Nat.card_congr E
      _ = k := rf7_codRestrict_fibre_card qU S hUr (p u₀)
  obtain ⟨v, hv, _, hvR, hvP⟩ := rf7_offcentre_topological
    c c ρ (by simpa using hρ) k hk qU hUr hcovU hdeg
  refine ⟨k, hk, v, hv, ?_, hvP⟩
  simpa only [add_sub_cancel_left, norm_pow] using hvR

end HodgeLean.Foundations.Program
