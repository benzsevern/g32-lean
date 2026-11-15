import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceDefs
import HodgeLean.Foundations.AnalyticGermExtension

/-! # Reduced complex analytic spaces: basic chart and sheaf lemmas

Helpers for the F2 proof obligations, prefixed `anb_`: continuity of chart maps, restriction and
locality of holomorphic functions, and local compactness.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations

universe u v w

/-- A local model is locally closed in `ℂⁿ`: the open `U` meets the closed complement of the open
set of points of `U` where some equation does not vanish. -/
theorem anb_isLocallyClosed_zeroLocus {n k : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → (Fin k → ℂ)} (hf : AnalyticOnNhd ℂ f U) :
    IsLocallyClosed (an_zeroLocus U f) := by
  have hO : IsOpen (U ∩ f ⁻¹' {0}ᶜ) :=
    hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  refine ⟨U, (U ∩ f ⁻¹' {0}ᶜ)ᶜ, hU, hO.isClosed_compl, ?_⟩
  ext z
  simp only [an_zeroLocus, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_preimage,
    mem_singleton_iff, not_and, not_not]
  exact ⟨fun h ↦ ⟨h.1, fun _ ↦ h.2⟩, fun h ↦ ⟨h.1, h.2 h.1⟩⟩

section Chart

variable {X : Type u} [TopologicalSpace X]

/-- A chart map is continuous on its domain. -/
theorem anb_continuousOn_toFun (c : an_Chart X) : ContinuousOn c.toFun c.dom :=
  continuousOn_iff_continuous_domRestrict.2 c.isEmbedding.continuous

/-- A chart map is continuous at every point of its domain. -/
theorem anb_continuousAt_toFun (c : an_Chart X) {x : X} (hx : x ∈ c.dom) :
    ContinuousAt c.toFun x :=
  (anb_continuousOn_toFun c).continuousAt (c.isOpen_dom.mem_nhds hx)

/-- A chart domain is locally compact. -/
theorem anb_locallyCompact_dom (c : an_Chart X) : LocallyCompactSpace c.dom := by
  refine c.isEmbedding.isInducing.locallyCompactSpace ?_
  rw [range_domRestrict, c.image_eq]
  exact anb_isLocallyClosed_zeroLocus c.isOpen_U c.analyticOnNhd_eqns

/-- An open subset of `X`, traced on a chart domain, is the preimage of an open subset of `ℂⁿ`. -/
theorem anb_exists_open_trace (c : an_Chart X) {N : Set X} (hN : IsOpen N) :
    ∃ O : Set (Fin c.n → ℂ), IsOpen O ∧ ∀ y ∈ c.dom, (c.toFun y ∈ O ↔ y ∈ N) := by
  have h : IsOpen ((Subtype.val : c.dom → X) ⁻¹' N) := hN.preimage continuous_subtype_val
  rw [c.isEmbedding.isInducing.isOpen_iff] at h
  obtain ⟨O, hO, hON⟩ := h
  refine ⟨O, hO, fun y hy ↦ ?_⟩
  have := congrArg (fun s : Set c.dom ↦ (⟨y, hy⟩ : c.dom) ∈ s) hON
  simpa using this

/-- A chart map is injective on its domain. -/
theorem anb_injOn_toFun (c : an_Chart X) : InjOn c.toFun c.dom := fun x hx y hy h ↦
  congrArg Subtype.val (c.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

end Chart

section HolFun

variable {X : Type u} [TopologicalSpace X]

/-- Restriction of a holomorphic function to a smaller set. -/
theorem anb_isHolFun_restrict (A : an_Atlas X) {U V : Set X} (hVU : V ⊆ U) {g : U → ℂ}
    (hg : A.IsHolFun g) : A.IsHolFun (fun y : V ↦ g ⟨y, hVU y.2⟩) := by
  intro x j hx
  obtain ⟨N, hN, hxN, G, hG, h⟩ := hg ⟨x, hVU x.2⟩ j hx
  exact ⟨N, hN, hxN, G, hG, fun y hy ↦ h ⟨y, hVU y.2⟩ hy⟩

/-- Holomorphic functions are continuous: near each point they are a function analytic at the
image point composed with a chart map continuous on its open domain. -/
theorem anb_isHolFun_continuous (A : an_Atlas X) {U : Set X} {g : U → ℂ} (hg : A.IsHolFun g) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  obtain ⟨N, hN, hxN, G, hG, h⟩ := hg x i hi
  have hcont : ContinuousAt (fun y : U ↦ G ((A.chart i).toFun y)) x :=
    (hG.continuousAt.comp (anb_continuousAt_toFun (A.chart i) hi)).comp
      continuous_subtype_val.continuousAt
  refine hcont.congr ?_
  have hmem : (N ∩ (A.chart i).dom) ∈ 𝓝 (x : X) :=
    (hN.inter (A.chart i).isOpen_dom).mem_nhds ⟨hxN, hi⟩
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hmem] with y hy
  exact (h y hy).symm

/-- In an analytic atlas, near a point of two chart domains, the second chart map is an analytic
map of the first. -/
theorem anb_transition (A : an_Atlas X) (hA : A.IsAnalytic) (i j : A.ι) {x : X}
    (hi : x ∈ (A.chart i).dom) (hj : x ∈ (A.chart j).dom) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (A.chart i).dom ∩ (A.chart j).dom ∧
      ∃ H : (Fin (A.chart i).n → ℂ) → (Fin (A.chart j).n → ℂ),
        ∀ y ∈ N, AnalyticAt ℂ H ((A.chart i).toFun y) ∧
          (A.chart j).toFun y = H ((A.chart i).toFun y) := by
  obtain ⟨W, hW, hxW, H, hH, h⟩ := hA i j x ⟨hj, hi⟩
  have hO := (anb_continuousOn_toFun (A.chart i)).isOpen_inter_preimage (A.chart i).isOpen_dom hW
  refine ⟨((A.chart i).dom ∩ (A.chart i).toFun ⁻¹' W) ∩ (A.chart j).dom,
    hO.inter (A.chart j).isOpen_dom, ⟨⟨hi, hxW⟩, hj⟩, fun y hy ↦ ⟨hy.1.1, hy.2⟩, H,
    fun y hy ↦ ⟨hH _ hy.1.2, h y ⟨hy.2, hy.1.1⟩ hy.1.2⟩⟩

/-- In an analytic atlas, a function is holomorphic as soon as near each point it is, in one chart
at that point, a function analytic at the image point composed with the chart. -/
theorem anb_isHolFun_of_chart (A : an_Atlas X) (hA : A.IsAnalytic) {U : Set X} {g : U → ℂ}
    (h : ∀ x : U, ∃ i, (x : X) ∈ (A.chart i).dom ∧ ∃ N : Set X, IsOpen N ∧ (x : X) ∈ N ∧
      ∃ G : (Fin (A.chart i).n → ℂ) → ℂ, AnalyticAt ℂ G ((A.chart i).toFun x) ∧
        ∀ y : U, (y : X) ∈ N ∩ (A.chart i).dom → g y = G ((A.chart i).toFun y)) :
    A.IsHolFun g := by
  intro x j hxj
  obtain ⟨i, hxi, N, hN, hxN, G, hG, hg⟩ := h x
  obtain ⟨N', hN', hxN', hN'sub, H, hH⟩ := anb_transition A hA j i hxj hxi
  refine ⟨N ∩ N', hN.inter hN', ⟨hxN, hxN'⟩, G ∘ H,
    hG.comp_of_eq (hH x hxN').1 (hH x hxN').2.symm, fun y hy ↦ ?_⟩
  rw [hg y ⟨hy.1.1, (hN'sub hy.1.2).2⟩, Function.comp_apply, (hH y hy.1.2).2]

end HolFun

section Germ

open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- The vanishing ideal of the germ of a neighbourhood is zero: a germ vanishing on a
neighbourhood of the anchor is the zero germ. -/
theorem anb_ideal_germ_of_mem_nhds {n : ℕ} {A : Set (Fin n → ℂ)} {x : Fin n → ℂ}
    (h : A ∈ 𝓝 x) : adim2_ideal n (adim2_germ n A x) = ⊥ := by
  ext f
  simp only [Ideal.mem_bot]
  constructor
  · intro hf
    obtain ⟨F, -, hFf⟩ := f.property
    change adim2_germ n A x ≤ f.val.map (· = 0) at hf
    rw [← hFf] at hf
    have hA : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ A := by
      have : Tendsto (fun z : Fin n → ℂ ↦ x + z) (𝓝 0) (𝓝 x) := by
        simpa using (continuous_const_add x).tendsto (0 : Fin n → ℂ)
      exact this h
    have hF : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), F z = 0 := by
      filter_upwards [Filter.Germ.coe_le.1 hf, hA] with z hz hzA
      exact hz hzA
    apply Subtype.ext
    rw [← hFf]
    exact Filter.Germ.coe_eq.2 hF
  · rintro rfl
    exact (adim2_ideal n _).zero_mem

/-- The germ of a neighbourhood in `ℂⁿ` has dimension `n`. -/
theorem anb_dimension_germ_of_mem_nhds {n : ℕ} {A : Set (Fin n → ℂ)} {x : Fin n → ℂ}
    (h : A ∈ 𝓝 x) : adim2_dimension n (adim2_germ n A x) = ((n : ℕ∞) : WithBot ℕ∞) := by
  rw [adim2_dimension, anb_ideal_germ_of_mem_nhds h,
    ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), adim6_parameter_dimension]
  rfl

/-- Membership in the vanishing ideal of a set germ, read on a representative. -/
theorem anb_mem_ideal_germ_iff {n : ℕ} {A : Set (Fin n → ℂ)} {p : Fin n → ℂ}
    {f : AnalyticGerm n} {F : (Fin n → ℂ) → ℂ} (hFf : Filter.Germ.ofFun F = f.val) :
    f ∈ adim2_ideal n (adim2_germ n A p) ↔ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ A → F z = 0 := by
  change adim2_germ n A p ≤ f.val.map (· = 0) ↔ _
  rw [← hFf]
  exact Filter.Germ.coe_le

theorem anb_tendsto_of_analyticAt {n m : ℕ} {φ : (Fin n → ℂ) → (Fin m → ℂ)}
    (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) : Tendsto φ (𝓝 0) (𝓝 0) := by
  simpa [h0] using hφ.continuousAt.tendsto

/-- Composition of analytic germs with an analytic map fixing the origin. -/
def anb_germComp {n m : ℕ} (φ : (Fin n → ℂ) → (Fin m → ℂ)) (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) : AnalyticGerm m →+* AnalyticGerm n where
  toFun f := ⟨f.val.compTendsto φ (anb_tendsto_of_analyticAt hφ h0), by
    obtain ⟨F, hF, hFf⟩ := f.property
    exact ⟨F ∘ φ, hF.comp_of_eq hφ h0, by rw [← hFf]; rfl⟩⟩
  map_one' := rfl
  map_mul' f g := by
    apply Subtype.ext
    obtain ⟨F, -, hFf⟩ := f.property
    obtain ⟨G, -, hGg⟩ := g.property
    change (f.val * g.val).compTendsto φ (anb_tendsto_of_analyticAt hφ h0) =
      f.val.compTendsto φ (anb_tendsto_of_analyticAt hφ h0) *
        g.val.compTendsto φ (anb_tendsto_of_analyticAt hφ h0)
    rw [← hFf, ← hGg]
    rfl
  map_zero' := rfl
  map_add' f g := by
    apply Subtype.ext
    obtain ⟨F, -, hFf⟩ := f.property
    obtain ⟨G, -, hGg⟩ := g.property
    change (f.val + g.val).compTendsto φ (anb_tendsto_of_analyticAt hφ h0) =
      f.val.compTendsto φ (anb_tendsto_of_analyticAt hφ h0) +
        g.val.compTendsto φ (anb_tendsto_of_analyticAt hφ h0)
    rw [← hFf, ← hGg]
    rfl

theorem anb_germComp_val {n m : ℕ} {φ : (Fin n → ℂ) → (Fin m → ℂ)} (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) {f : AnalyticGerm m} {F : (Fin m → ℂ) → ℂ}
    (hFf : Filter.Germ.ofFun F = f.val) :
    Filter.Germ.ofFun (F ∘ φ) = (anb_germComp φ hφ h0 f).val := by
  change _ = f.val.compTendsto φ (anb_tendsto_of_analyticAt hφ h0)
  rw [← hFf]
  rfl

/-- Composition with `φ` maps the vanishing ideal of `B` at `q` into that of `A` at `p` when `φ`,
read from `p` to `q`, maps `A` into `B` near `p`. -/
theorem anb_germComp_ideal_le {n m : ℕ} {φ : (Fin n → ℂ) → (Fin m → ℂ)} (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) {A : Set (Fin n → ℂ)} {B : Set (Fin m → ℂ)} {p : Fin n → ℂ} {q : Fin m → ℂ}
    (hAB : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ A → q + φ z ∈ B) :
    adim2_ideal m (adim2_germ m B q) ≤
      (adim2_ideal n (adim2_germ n A p)).comap (anb_germComp φ hφ h0) := by
  intro f hf
  obtain ⟨F, -, hFf⟩ := f.property
  rw [Ideal.mem_comap, anb_mem_ideal_germ_iff (anb_germComp_val hφ h0 hFf)]
  rw [anb_mem_ideal_germ_iff hFf] at hf
  have hf' := (anb_tendsto_of_analyticAt hφ h0).eventually hf
  filter_upwards [hAB, hf'] with z hz hz' hzA
  exact hz' (hz hzA)

/-- Composing with `ψ` and then `φ` is the identity modulo the vanishing ideal of `B` at `q` when
`φ ∘ ψ` is the identity on `B` near `q`. -/
theorem anb_germComp_comp_sub_mem {n m : ℕ} {φ : (Fin n → ℂ) → (Fin m → ℂ)}
    (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {ψ : (Fin m → ℂ) → (Fin n → ℂ)}
    (hψ : AnalyticAt ℂ ψ 0) (h0' : ψ 0 = 0) {B : Set (Fin m → ℂ)} {q : Fin m → ℂ}
    (hφψ : ∀ᶠ w in 𝓝 (0 : Fin m → ℂ), q + w ∈ B → φ (ψ w) = w) (f : AnalyticGerm m) :
    anb_germComp ψ hψ h0' (anb_germComp φ hφ h0 f) - f ∈ adim2_ideal m (adim2_germ m B q) := by
  obtain ⟨F, -, hFf⟩ := f.property
  have h1 := anb_germComp_val hψ h0' (anb_germComp_val hφ h0 hFf)
  have h2 : Filter.Germ.ofFun (fun w : Fin m → ℂ ↦ (F ∘ φ ∘ ψ) w - F w) =
      (anb_germComp ψ hψ h0' (anb_germComp φ hφ h0 f) - f).val := by
    change _ = (anb_germComp ψ hψ h0' (anb_germComp φ hφ h0 f)).val - f.val
    rw [← h1, ← hFf]
    rfl
  rw [anb_mem_ideal_germ_iff h2]
  filter_upwards [hφψ] with w hw hwB
  simp [hw hwB]

/-- Two set germs related by analytic maps that are mutually inverse on them have the same
dimension: the maps induce inverse isomorphisms of the reduced local rings. -/
theorem anb_dimension_eq_of_inverse {n m : ℕ} {A : Set (Fin n → ℂ)} {B : Set (Fin m → ℂ)}
    {p : Fin n → ℂ} {q : Fin m → ℂ} {φ : (Fin n → ℂ) → (Fin m → ℂ)}
    (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {ψ : (Fin m → ℂ) → (Fin n → ℂ)}
    (hψ : AnalyticAt ℂ ψ 0) (h0' : ψ 0 = 0)
    (hAB : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ A → q + φ z ∈ B)
    (hBA : ∀ᶠ w in 𝓝 (0 : Fin m → ℂ), q + w ∈ B → p + ψ w ∈ A)
    (hψφ : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ A → ψ (φ z) = z)
    (hφψ : ∀ᶠ w in 𝓝 (0 : Fin m → ℂ), q + w ∈ B → φ (ψ w) = w) :
    adim2_dimension n (adim2_germ n A p) = adim2_dimension m (adim2_germ m B q) := by
  let I := adim2_ideal n (adim2_germ n A p)
  let J := adim2_ideal m (adim2_germ m B q)
  let u : AnalyticGerm m ⧸ J →+* AnalyticGerm n ⧸ I :=
    Ideal.quotientMap I (anb_germComp φ hφ h0) (anb_germComp_ideal_le hφ h0 hAB)
  let v : AnalyticGerm n ⧸ I →+* AnalyticGerm m ⧸ J :=
    Ideal.quotientMap J (anb_germComp ψ hψ h0') (anb_germComp_ideal_le hψ h0' hBA)
  have hvu : v.comp u = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext f
    simp only [RingHom.comp_apply, u, v, Ideal.quotientMap_mk, RingHom.id_apply]
    exact Ideal.Quotient.eq.2 (anb_germComp_comp_sub_mem hφ h0 hψ h0' hφψ f)
  have huv : u.comp v = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext f
    simp only [RingHom.comp_apply, u, v, Ideal.quotientMap_mk, RingHom.id_apply]
    exact Ideal.Quotient.eq.2 (anb_germComp_comp_sub_mem hψ h0' hφ h0 hψφ f)
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofRingHom u v huv hvu).symm

theorem anb_eventually_add_mem {n : ℕ} {O : Set (Fin n → ℂ)} (hO : IsOpen O) {p : Fin n → ℂ}
    (hp : p ∈ O) : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ O := by
  have : Tendsto (fun z : Fin n → ℂ ↦ p + z) (𝓝 0) (𝓝 p) := by
    simpa using (continuous_const_add p).tendsto (0 : Fin n → ℂ)
  exact this (hO.mem_nhds hp)

theorem anb_analyticAt_shift {n m : ℕ} {H : (Fin n → ℂ) → (Fin m → ℂ)} {p : Fin n → ℂ}
    (hH : AnalyticAt ℂ H p) (q : Fin m → ℂ) :
    AnalyticAt ℂ (fun z ↦ H (p + z) - q) 0 :=
  (hH.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)).sub analyticAt_const

variable {X : Type u} [TopologicalSpace X]

/-- One direction of a chart change on the germs of the images of `Z`: near `a x`, the shifted
transition maps the image of `Z` in chart `a` into its image in chart `b`, and the reverse
transition undoes it there. -/
theorem anb_chart_change (A : an_Atlas X) (Z : Set X) (a b : A.ι) {x : X} {N : Set X}
    (hN : IsOpen N) (hxN : x ∈ N) (hNsub : N ⊆ (A.chart a).dom ∩ (A.chart b).dom)
    (H1 : (Fin (A.chart a).n → ℂ) → (Fin (A.chart b).n → ℂ))
    (hH1 : ∀ y ∈ N, (A.chart b).toFun y = H1 ((A.chart a).toFun y))
    (H2 : (Fin (A.chart b).n → ℂ) → (Fin (A.chart a).n → ℂ))
    (hH2 : ∀ y ∈ N, (A.chart a).toFun y = H2 ((A.chart b).toFun y)) :
    ∀ᶠ z in 𝓝 (0 : Fin (A.chart a).n → ℂ),
      (A.chart a).toFun x + z ∈ (A.chart a).toFun '' (Z ∩ (A.chart a).dom) →
        (A.chart b).toFun x + (H1 ((A.chart a).toFun x + z) - (A.chart b).toFun x) ∈
            (A.chart b).toFun '' (Z ∩ (A.chart b).dom) ∧
          H2 ((A.chart b).toFun x + (H1 ((A.chart a).toFun x + z) - (A.chart b).toFun x)) -
            (A.chart a).toFun x = z := by
  obtain ⟨O, hO, hON⟩ := anb_exists_open_trace (A.chart a) hN
  filter_upwards [anb_eventually_add_mem hO ((hON x (hNsub hxN).1).2 hxN)] with z hzO hzA
  obtain ⟨y, ⟨hyZ, hya⟩, hyz⟩ := hzA
  have hyN : y ∈ N := (hON y hya).1 (hyz ▸ hzO)
  rw [add_sub_cancel, ← hyz, ← hH1 y hyN, ← hH2 y hyN, hyz, add_sub_cancel_left]
  exact ⟨⟨y, ⟨hyZ, (hNsub hyN).2⟩, rfl⟩, rfl⟩

/-- In an analytic atlas, any two charts at `x` give the same Krull dimension of the germ of `Z`. -/
theorem anb_dimension_chart_eq (A : an_Atlas X) (hA : A.IsAnalytic) (Z : Set X) (a b : A.ι)
    {x : X} (ha : x ∈ (A.chart a).dom) (hb : x ∈ (A.chart b).dom) :
    adim2_dimension (A.chart a).n
        (adim2_germ (A.chart a).n ((A.chart a).toFun '' (Z ∩ (A.chart a).dom))
          ((A.chart a).toFun x)) =
      adim2_dimension (A.chart b).n
        (adim2_germ (A.chart b).n ((A.chart b).toFun '' (Z ∩ (A.chart b).dom))
          ((A.chart b).toFun x)) := by
  obtain ⟨N1, hN1, hxN1, hN1sub, H1, hH1⟩ := anb_transition A hA a b ha hb
  obtain ⟨N2, hN2, hxN2, hN2sub, H2, hH2⟩ := anb_transition A hA b a hb ha
  have hNsub : N1 ∩ N2 ⊆ (A.chart a).dom ∩ (A.chart b).dom := fun y hy ↦ hN1sub hy.1
  have hNsub' : N1 ∩ N2 ⊆ (A.chart b).dom ∩ (A.chart a).dom := fun y hy ↦ hN2sub hy.2
  have e1 : ∀ y ∈ N1 ∩ N2, (A.chart b).toFun y = H1 ((A.chart a).toFun y) :=
    fun y hy ↦ (hH1 y hy.1).2
  have e2 : ∀ y ∈ N1 ∩ N2, (A.chart a).toFun y = H2 ((A.chart b).toFun y) :=
    fun y hy ↦ (hH2 y hy.2).2
  have hab := anb_chart_change A Z a b (hN1.inter hN2) ⟨hxN1, hxN2⟩ hNsub H1 e1 H2 e2
  have hba := anb_chart_change A Z b a (hN1.inter hN2) ⟨hxN1, hxN2⟩ hNsub' H2 e2 H1 e1
  have hq : H1 ((A.chart a).toFun x) = (A.chart b).toFun x := (e1 x ⟨hxN1, hxN2⟩).symm
  have hp : H2 ((A.chart b).toFun x) = (A.chart a).toFun x := (e2 x ⟨hxN1, hxN2⟩).symm
  refine anb_dimension_eq_of_inverse
    (anb_analyticAt_shift (hH1 x hxN1).1 ((A.chart b).toFun x)) (by simp [hq])
    (anb_analyticAt_shift (hH2 x hxN2).1 ((A.chart a).toFun x)) (by simp [hp])
    ?_ ?_ ?_ ?_
  · filter_upwards [hab] with z hz hzA using (hz hzA).1
  · filter_upwards [hba] with z hz hzA using (hz hzA).1
  · filter_upwards [hab] with z hz hzA using (hz hzA).2
  · filter_upwards [hba] with z hz hzA using (hz hzA).2

end Germ

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M']

/-- `C^ω` at a point, read in the preferred charts: continuity and analyticity of the chart
expression. -/
theorem anb_contMDiffAt_iff (f : M → M') (x : M) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E') ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (chartAt E' (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x) := by
  rw [contMDiffAt_iff, show range (𝓘(ℂ, E)) = univ by simp, contDiffWithinAt_univ]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ h.analyticAt, fun h ↦ h.contDiffAt⟩

variable [FiniteDimensional ℂ E] [T2Space M] [SecondCountableTopology M]
  [IsManifold 𝓘(ℂ, E) ω M]

/-- On an open set of an analytic manifold, the sections of the structure sheaf of the manifold
space are the `C^ω` functions. -/
theorem anb_manifold_isHolFun_iff (g : M → ℂ) {U : Set M} (hU : IsOpen U) :
    (an_manifoldSpace E M).IsHolFun (fun x : U ↦ g x) ↔ ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω g U := by
  constructor
  · intro hg x hx
    refine ContMDiffAt.contMDiffWithinAt ((anb_contMDiffAt_iff g x).2 ⟨?_, ?_⟩)
    · exact (continuousOn_iff_continuous_domRestrict.2
        (anb_isHolFun_continuous _ hg)).continuousAt (hU.mem_nhds hx)
    · rw [chartAt_self_eq]
      obtain ⟨N, hN, hxN, G, hG, hgG⟩ := hg ⟨x, hx⟩ x (mem_chart_source E x)
      set e := chartAt E x
      have hS : U ∩ N ∩ e.source ∈ 𝓝 x :=
        ((hU.inter hN).inter e.open_source).mem_nhds ⟨⟨hx, hxN⟩, mem_chart_source E x⟩
      have hS' : e.symm ⁻¹' (U ∩ N ∩ e.source) ∈ 𝓝 (e x) := by
        refine (e.continuousAt_symm (e.map_source (mem_chart_source E x))).preimage_mem_nhds ?_
        rwa [e.left_inv (mem_chart_source E x)]
      have hG' : AnalyticAt ℂ G (an_coord E (e x)) := hG
      have hGc : AnalyticAt ℂ (G ∘ an_coord E) (e x) :=
        hG'.comp_of_eq ((an_coord E).toContinuousLinearMap.analyticAt (e x)) rfl
      refine hGc.congr ?_
      filter_upwards [hS', e.open_target.mem_nhds (e.map_source (mem_chart_source E x))]
        with z hz hzt
      have := hgG ⟨e.symm z, hz.1.1⟩ ⟨hz.1.2, hz.2⟩
      change g (e.symm z) = G (an_coord E (e (e.symm z))) at this
      rw [e.right_inv hzt] at this
      exact this.symm
  · intro hcm
    refine anb_isHolFun_of_chart _ (an_manifoldSpace E M).isAnalytic fun x ↦
      ⟨x.1, mem_chart_source E x.1, univ, isOpen_univ, mem_univ _, ?_⟩
    set e := chartAt E x.1
    have hA := ((anb_contMDiffAt_iff g x.1).1 (hcm.contMDiffAt (hU.mem_nhds x.2))).2
    rw [chartAt_self_eq] at hA
    refine ⟨(g ∘ e.symm) ∘ (an_coord E).symm, ?_, fun y hy ↦ ?_⟩
    · refine hA.comp_of_eq ((an_coord E).symm.toContinuousLinearMap.analyticAt _) ?_
      change (an_coord E).symm (an_coord E (e x.1)) = e x.1
      simp
    · change g y = g (e.symm ((an_coord E).symm (an_coord E (e y))))
      rw [ContinuousLinearEquiv.symm_apply_apply, e.left_inv hy.2]

end Manifold

section Node

open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- A germ whose representative takes nonzero values arbitrarily near the origin is nonzero. -/
theorem anb_germ_ne_zero {n : ℕ} (F : (Fin n → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0)
    (h : ∀ ε : ℝ, 0 < ε → ∃ z : Fin n → ℂ, ‖z‖ < ε ∧ F z ≠ 0) :
    (⟨Filter.Germ.ofFun F, F, hF, rfl⟩ : AnalyticGerm n) ≠ 0 := by
  intro h0
  have h1 : Filter.Germ.ofFun F = Filter.Germ.ofFun (fun _ : Fin n → ℂ ↦ (0 : ℂ)) :=
    congrArg Subtype.val h0
  obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.1 (Filter.Germ.coe_eq.1 h1)
  obtain ⟨z, hz, hFz⟩ := h ε hε
  exact hFz (hεF (by simpa using hz))

theorem anb_const_vec_norm {n : ℕ} (t : ℝ) (ht : 0 ≤ t) :
    ‖(fun _ : Fin (n + 1) ↦ (t : ℂ))‖ = t := by
  exact (pi_norm_const (t : ℂ)).trans (by simp [abs_of_nonneg ht])

/-- The projection `w ↦ (w₀, 0)` of `ℂ¹` onto the first axis of `ℂ²`. -/
def anb_axis : (Fin 1 → ℂ) → (Fin 2 → ℂ) := fun w ↦ ![w 0, 0]

theorem anb_axis_analyticAt (w : Fin 1 → ℂ) : AnalyticAt ℂ anb_axis w := by
  refine analyticAt_pi_iff.2 fun i ↦ ?_
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt w
  · exact analyticAt_const

theorem anb_axis_zero : anb_axis 0 = 0 := by
  funext i; fin_cases i <;> rfl

/-- **The node is one-dimensional at the origin.** The ring `ℂ{z₀, z₁}` modulo the vanishing
ideal of `{z₀ z₁ = 0}` has Krull dimension `1`: the ideal contains the nonzerodivisor `z₀ z₁`,
which bounds the dimension by `2 - 1`, and the germs vanishing on the axis `{z₁ = 0}` and those
vanishing at the origin form a chain of two primes containing it. -/
theorem anb_dimension_node (A : Set (Fin 2 → ℂ)) (hA : ∀ z, z ∈ A ↔ z 0 * z 1 = 0) :
    adim2_dimension 2 (adim2_germ 2 A 0) = 1 := by
  let : NoZeroDivisors (AnalyticGerm 2) := analyticGerm_noZeroDivisors_succ (n := 1)
  let : IsDomain (AnalyticGerm 2) := {}
  let : NoZeroDivisors (AnalyticGerm 1) := analyticGerm_noZeroDivisors_succ (n := 0)
  let : IsDomain (AnalyticGerm 1) := {}
  set I := adim2_ideal 2 (adim2_germ 2 A 0)
  have hpr : ∀ k : Fin 2, AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z k) 0 := fun k ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) k).analyticAt 0
  let r : AnalyticGerm 2 := ⟨Filter.Germ.ofFun (fun z ↦ z 0 * z 1), _, (hpr 0).mul (hpr 1), rfl⟩
  have hrI : r ∈ I := by
    rw [anb_mem_ideal_germ_iff (F := fun z ↦ z 0 * z 1) rfl]
    exact Filter.Eventually.of_forall fun z hz ↦ by simpa using (hA _).1 hz
  have hr0 : r ≠ 0 := by
    refine anb_germ_ne_zero _ ((hpr 0).mul (hpr 1)) fun ε hε ↦
      ⟨fun _ ↦ ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [anb_const_vec_norm _ (by positivity)]; linarith
    · have hne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
      exact mul_ne_zero hne hne
  -- upper bound
  have hup : ringKrullDim (AnalyticGerm 2 ⧸ I) + 1 ≤ 2 := by
    have h1 : ringKrullDim (AnalyticGerm 2 ⧸ I) ≤ ringKrullDim (AnalyticGerm 2 ⧸ Ideal.span {r}) :=
      ringKrullDim_le_of_surjective
        (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).2 hrI))
        (Ideal.Quotient.factor_surjective _)
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
    rw [adim6_parameter_dimension] at h2
    calc ringKrullDim (AnalyticGerm 2 ⧸ I) + 1
        ≤ ringKrullDim (AnalyticGerm 2 ⧸ Ideal.span {r}) + 1 := by gcongr
      _ ≤ _ := h2
  -- lower bound
  let ψ := anb_germComp anb_axis (anb_axis_analyticAt 0) anb_axis_zero
  have hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hQ : (RingHom.ker (analyticGermValue 2)).IsPrime := RingHom.ker_isPrime _
  have hIP : I ≤ RingHom.ker ψ := by
    intro f hf
    obtain ⟨F, -, hFf⟩ := f.property
    rw [anb_mem_ideal_germ_iff hFf] at hf
    rw [RingHom.mem_ker]
    apply Subtype.ext
    rw [← anb_germComp_val (anb_axis_analyticAt 0) anb_axis_zero hFf]
    apply Filter.Germ.coe_eq.2
    have := (anb_tendsto_of_analyticAt (anb_axis_analyticAt 0) anb_axis_zero).eventually hf
    filter_upwards [this] with w hw
    exact hw (by rw [zero_add, hA]; simp [anb_axis])
  have hPQ : RingHom.ker ψ ≤ RingHom.ker (analyticGermValue 2) := by
    intro f hf
    obtain ⟨F, -, hFf⟩ := f.property
    rw [RingHom.mem_ker] at hf ⊢
    have h1 : Filter.Germ.value (ψ f).val = Filter.Germ.value (0 : AnalyticGerm 1).val := by
      rw [hf]
    rw [← anb_germComp_val (anb_axis_analyticAt 0) anb_axis_zero hFf] at h1
    change F (anb_axis 0) = 0 at h1
    rw [anb_axis_zero] at h1
    change Filter.Germ.value f.val = 0
    rw [← hFf]
    exact h1
  let z0 : AnalyticGerm 2 := ⟨Filter.Germ.ofFun (fun z ↦ z 0), _, hpr 0, rfl⟩
  have hz0Q : z0 ∈ RingHom.ker (analyticGermValue 2) := rfl
  have hz0P : z0 ∉ RingHom.ker ψ := by
    rw [RingHom.mem_ker]
    intro h
    have h' : (⟨Filter.Germ.ofFun ((fun z : Fin 2 → ℂ ↦ z 0) ∘ anb_axis), _,
        (hpr 0).comp_of_eq (anb_axis_analyticAt 0) anb_axis_zero, rfl⟩ : AnalyticGerm 1) = 0 := by
      rw [← h]
      exact Subtype.ext (anb_germComp_val (anb_axis_analyticAt 0) anb_axis_zero rfl)
    refine anb_germ_ne_zero _ ((hpr 0).comp_of_eq (anb_axis_analyticAt 0) anb_axis_zero)
      (fun ε hε ↦ ⟨fun _ ↦ ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩) h'
    · rw [anb_const_vec_norm _ (by positivity)]; linarith
    · exact Complex.ofReal_ne_zero.2 (by positivity)
  have hlow : 1 ≤ ringKrullDim (AnalyticGerm 2 ⧸ I) := by
    rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
    refine ⟨⟨⟨RingHom.ker ψ, hP⟩, hIP⟩, ⟨⟨RingHom.ker (analyticGermValue 2), hQ⟩,
      hIP.trans hPQ⟩, ?_⟩
    refine lt_of_le_of_ne hPQ ?_
    intro h
    apply hz0P
    have : RingHom.ker ψ = RingHom.ker (analyticGermValue 2) :=
      congrArg (fun p : PrimeSpectrum.zeroLocus (I : Set (AnalyticGerm 2)) ↦ p.1.asIdeal) h
    rw [this]; exact hz0Q
  change ringKrullDim (AnalyticGerm 2 ⧸ I) = 1
  generalize ringKrullDim (AnalyticGerm 2 ⧸ I) = d at hup hlow
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hlow (by simp)
  | coe m =>
    have h1 : m + 1 ≤ 2 := by
      have : ((m + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := hup
      exact WithBot.coe_le_coe.1 this
    have h2 : 1 ≤ m := by
      have : ((1 : ℕ∞) : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := hlow
      exact WithBot.coe_le_coe.1 this
    induction m using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe m =>
      have h1' : m + 1 ≤ 2 := by exact_mod_cast h1
      have h2' : 1 ≤ m := by exact_mod_cast h2
      have : m = 1 := by omega
      subst this; rfl

end Node

end HodgeLean.Foundations.Analytic
