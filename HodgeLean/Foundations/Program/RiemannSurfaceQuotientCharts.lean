import HodgeLean.Foundations.Program.RiemannSurfaceQuotientDefs

noncomputable section

open Manifold
open scoped ContDiff Topology BigOperators

namespace HodgeLean.Foundations.Program

def rsq_weightedAverage {G X : Type} [Group G] [Fintype G] [MulAction G X]
    (χ : G →* ℂˣ) (φ : X → ℂ) (y : X) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, (χ g : ℂ)⁻¹ * φ (g • y)

theorem rsq_weightedAverage_equivariant {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (χ : G →* ℂˣ) (φ : X → ℂ) (h : G) (y : X) :
    rsq_weightedAverage χ φ (h • y) = (χ h : ℂ) * rsq_weightedAverage χ φ y := by
  classical
  have hs : (∑ g : G, (χ g : ℂ)⁻¹ * φ ((g * h) • y)) =
      (χ h : ℂ) * ∑ g : G, (χ g : ℂ)⁻¹ * φ (g • y) := by
    rw [Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    change (χ g : ℂ)⁻¹ * φ ((g * h) • y) =
      (χ h : ℂ) * ((χ (g * h) : ℂ)⁻¹ * φ ((g * h) • y))
    simp only [map_mul, Units.val_mul, mul_inv_rev]
    field_simp
  simp only [rsq_weightedAverage, ← mul_smul]
  rw [hs]
  ring

theorem rsq_weightedSum_hasStrictFDerivAt
    {G V : Type} [Group G] [Fintype G]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (χ : G →* ℂˣ) (A : G → V → ℂ) (L : V →L[ℂ] ℂ) (z : V)
    (hA : ∀ g, HasStrictFDerivAt (A g) ((χ g : ℂ) • L) z) :
    HasStrictFDerivAt
      (fun w ↦ (Fintype.card G : ℂ)⁻¹ * ∑ g : G, (χ g : ℂ)⁻¹ * A g w) L z := by
  have ht : ∀ g : G, HasStrictFDerivAt (fun w ↦ (χ g : ℂ)⁻¹ * A g w) L z := by
    intro g
    convert (hA g).const_smul ((χ g : ℂ)⁻¹) using 1
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) fun g _ ↦ ht g
  convert hs.const_smul ((Fintype.card G : ℂ)⁻¹) using 1
  · funext w
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  · rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

theorem rsq_character_norm {G : Type} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (g : G) : ‖(χ g : ℂ)‖ = 1 := by
  have hp : (χ g : ℂ) ^ Fintype.card G = 1 := by
    change ((χ g ^ Fintype.card G : ℂˣ) : ℂ) = 1
    rw [← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hp Fintype.card_ne_zero

theorem rsq_invariant_open_neighborhood {G X : Type} [Group G] [Finite G]
    [MulAction G X] [TopologicalSpace X]
    (hc : ∀ g : G, Continuous (fun y : X ↦ g • y))
    (x : X) (hfix : ∀ g : G, g • x = x)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ g : G, Set.MapsTo (fun y : X ↦ g • y) V V := by
  let V : Set X := ⋂ g : G, (fun y : X ↦ g • y) ⁻¹' U
  have ho : IsOpen V := isOpen_iInter_of_finite fun g ↦ (hc g).isOpen_preimage U hU
  have hx : x ∈ V := Set.mem_iInter.2 fun g ↦ by
    change g • x ∈ U
    rw [hfix g]
    exact hxU
  refine ⟨V, ho, hx, ?_, ?_⟩
  · intro y hy
    have ht := Set.mem_iInter.1 hy (1 : G)
    simpa only [Set.mem_preimage, one_smul] using ht
  · intro g y hy
    apply Set.mem_iInter.2
    intro k
    have ht := Set.mem_iInter.1 hy (k * g)
    simpa only [Set.mem_preimage, mul_smul] using ht

theorem rsq_character_pow_eq_iff {G : Type} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (hinj : Function.Injective χ) (z w : ℂ) :
    z ^ Fintype.card G = w ^ Fintype.card G ↔ ∃ g : G, (χ g : ℂ) * z = w := by
  classical
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have hp : ∀ g : G, (χ g : ℂ) ^ Fintype.card G = 1 := by
    intro g
    change ((χ g ^ Fintype.card G : ℂˣ) : ℂ) = 1
    rw [← map_pow, pow_card_eq_one, map_one, Units.val_one]
  constructor
  · intro hzw
    by_cases hz : z = 0
    · have hw : w = 0 := pow_eq_zero_iff hn.ne' |>.1 (by rw [← hzw, hz, zero_pow hn.ne'])
      exact ⟨1, by simp [hz, hw]⟩
    have hsub : Finset.univ.image (fun g : G ↦ (χ g : ℂ)) ⊆
        Polynomial.nthRootsFinset (Fintype.card G) (1 : ℂ) := by
      intro c hc
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hc
      exact (Polynomial.mem_nthRootsFinset hn (1 : ℂ)).2 (hp g)
    have hcard : (Finset.univ.image (fun g : G ↦ (χ g : ℂ))).card = Fintype.card G := by
      have hi : Function.Injective (fun g : G ↦ (χ g : ℂ)) :=
        fun a b h ↦ hinj (Units.val_injective h)
      rw [Finset.card_image_of_injective _ hi, Finset.card_univ]
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [hcard, b4cov_card_nthRootsFinset hn one_ne_zero])
    have hr : w / z ∈ Polynomial.nthRootsFinset (Fintype.card G) (1 : ℂ) := by
      apply (Polynomial.mem_nthRootsFinset hn (1 : ℂ)).2
      rw [div_pow, ← hzw, div_self (pow_ne_zero _ hz)]
    rw [← heq] at hr
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 hr
    exact ⟨g, by rw [hg, div_mul_cancel₀ _ hz]⟩
  · rintro ⟨g, rfl⟩
    rw [mul_pow, hp g, one_mul]

theorem rsq_equivariant_disc_restriction {G X : Type} [Group G] [Fintype G]
    [MulAction G X] [TopologicalSpace X]
    (χ : G →* ℂˣ) (u : X → ℂ)
    (hu : ∀ g : G, ∀ y : X, u (g • y) = (χ g : ℂ) * u y)
    (e₀ : OpenPartialHomeomorph X ℂ) (x : X) (he₀ : e₀ x = 0)
    (heu : Set.EqOn e₀ u e₀.source)
    (V : Set X) (hVo : IsOpen V) (hxV : x ∈ V) (hVe : V ⊆ e₀.source)
    (hVi : ∀ g : G, Set.MapsTo (fun y : X ↦ g • y) V V) :
    ∃ (r : ℝ) (e : OpenPartialHomeomorph X ℂ), 0 < r ∧ x ∈ e.source ∧
      e.source ⊆ V ∧ e.target = Metric.ball 0 r ∧ (e : X → ℂ) = e₀ ∧
      (e.symm : ℂ → X) = e₀.symm ∧
      ∀ g : G, Set.MapsTo (fun y : X ↦ g • y) e.source e.source := by
  have ho : IsOpen (e₀ '' V) := e₀.isOpen_image_of_subset_source hVo hVe
  have hx : (0 : ℂ) ∈ e₀ '' V := ⟨x, hxV, he₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ho 0 hx
  let W := V ∩ e₀ ⁻¹' Metric.ball 0 r
  have hWo : IsOpen W :=
    (e₀.continuousOn.mono hVe).isOpen_inter_preimage hVo Metric.isOpen_ball
  let e := e₀.restrOpen W hWo
  have hsrc : e.source = W := Set.inter_eq_right.2 fun y hy ↦ hVe hy.1
  have htar : e.target = Metric.ball 0 r := by
    rw [← e.image_source_eq_target, hsrc]
    change e₀ '' W = Metric.ball 0 r
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.2
    · intro hz
      obtain ⟨y, hy, he⟩ := hball hz
      exact ⟨y, ⟨hy, by change e₀ y ∈ Metric.ball 0 r; rw [he]; exact hz⟩, he⟩
  refine ⟨r, e, hr, ?_, ?_, htar, rfl, rfl, ?_⟩
  · rw [hsrc]
    exact ⟨hxV, by change e₀ x ∈ Metric.ball 0 r; rw [he₀]; exact Metric.mem_ball_self hr⟩
  · rw [hsrc]
    exact Set.inter_subset_left
  · intro g y hy
    rw [hsrc] at hy ⊢
    have hgy := hVi g hy.1
    refine ⟨hgy, ?_⟩
    change e₀ (g • y) ∈ Metric.ball 0 r
    rw [mem_ball_zero_iff, heu (hVe hgy), hu, norm_mul,
      rsq_character_norm, one_mul, ← heu (hVe hy.1)]
    exact mem_ball_zero_iff.1 hy.2

theorem rsq_homeomorph_of_quotientMaps {A B C : Type}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A → B) (g : A → C) (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (hfg : ∀ a a', f a = f a' ↔ g a = g a') :
    ∃ e : B ≃ₜ C, ∀ a : A, e (f a) = g a := by
  classical
  let t : B → C := g ∘ Function.surjInv hf.surjective
  let s : C → B := f ∘ Function.surjInv hg.surjective
  have ht : ∀ a, t (f a) = g a := fun a ↦ (hfg _ _).1
    (Function.surjInv_eq hf.surjective (f a))
  have hs : ∀ a, s (g a) = f a := fun a ↦ (hfg _ _).2
    (Function.surjInv_eq hg.surjective (g a))
  have hl : Function.LeftInverse s t := by
    intro b
    obtain ⟨a, rfl⟩ := hf.surjective b
    rw [ht, hs]
  have hr : Function.RightInverse s t := by
    intro c
    obtain ⟨a, rfl⟩ := hg.surjective c
    rw [hs, ht]
  have htc : Continuous t := hf.continuous_iff.2
    (by convert hg.continuous using 1; exact funext ht)
  have hsc : Continuous s := hg.continuous_iff.2
    (by convert hf.continuous using 1; exact funext hs)
  exact ⟨{
    toFun := t
    invFun := s
    left_inv := hl
    right_inv := hr
    continuous_toFun := htc
    continuous_invFun := hsc }, ht⟩

theorem rsq_analyticAt_of_comp_pow_regular {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : ℂ → V} {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : w ≠ 0)
    (hf : ∀ z : ℂ, z ^ n = w → AnalyticAt ℂ (fun t ↦ f (t ^ n)) z) :
    AnalyticAt ℂ f w := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w hn
  have hz0 : z ≠ 0 := fun h ↦ hw (by rw [← hz, h, zero_pow hn.ne'])
  have ha : AnalyticAt ℂ (fun t : ℂ ↦ t ^ n) z := analyticAt_id.pow n
  have hd : deriv (fun t : ℂ ↦ t ^ n) z ≠ 0 := by
    rw [(hasDerivAt_pow n z).deriv]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (pow_ne_zero _ hz0)
  rw [← hz]
  exact (analyticAt_comp_iff_of_deriv_ne_zero ha hd).1 (hf z hz)

theorem rsq_analyticOnNhd_of_comp_pow {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {f : ℂ → V} {n : ℕ} (hn : 0 < n) {U : Set ℂ} (hU : IsOpen U)
    (hc : ContinuousOn f U)
    (hf : ∀ z : ℂ, z ^ n ∈ U → AnalyticAt ℂ (fun t ↦ f (t ^ n)) z) :
    AnalyticOnNhd ℂ f U := by
  have hr : ∀ w ∈ U, w ≠ 0 → AnalyticAt ℂ f w := by
    intro w hw hw0
    exact rsq_analyticAt_of_comp_pow_regular hn hw0 fun z hz ↦ hf z (hz ▸ hw)
  intro w hw
  by_cases hw0 : w ≠ 0
  · exact hr w hw hw0
  · have hwz : w = 0 := not_ne_iff.1 hw0
    subst w
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hw),
        self_mem_nhdsWithin] with z hz hz0
      exact (hr z hz hz0).differentiableAt
    · exact hc.continuousAt (hU.mem_nhds hw)

section Stabilizer

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]
variable {H : Type} [Group H] [Finite H] [MulAction H X]

def rsq_stabilizerCoordinate (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) : X → ℂ :=
  letI := Fintype.ofFinite (MulAction.stabilizer H x)
  rsq_weightedAverage (b4cov_lamHom hE hH x).toHomUnits
    (fun y ↦ (b4cov_lineEquiv hE).symm
      (extChartAt 𝓘(ℂ, E) x y - extChartAt 𝓘(ℂ, E) x x))

theorem rsq_stabilizerCoordinate_center (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) : rsq_stabilizerCoordinate hE hH x x = 0 := by
  classical
  simp only [rsq_stabilizerCoordinate, rsq_weightedAverage]
  have hz : ∀ g : MulAction.stabilizer H x, g • x = x := fun g ↦ g.property
  simp only [hz, sub_self, map_zero, mul_zero, Finset.sum_const_zero]

theorem rsq_stabilizerCoordinate_equivariant (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) (g : MulAction.stabilizer H x) (y : X) :
    rsq_stabilizerCoordinate hE hH x (g • y) =
      b4cov_lam hE x (g : H) * rsq_stabilizerCoordinate hE hH x y := by
  letI := Fintype.ofFinite (MulAction.stabilizer H x)
  exact rsq_weightedAverage_equivariant (b4cov_lamHom hE hH x).toHomUnits _ g y

theorem rsq_centeredChartAction_hasStrictFDerivAt (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) (g : MulAction.stabilizer H x) :
    HasStrictFDerivAt
      (fun z : E ↦ (b4cov_lineEquiv hE).symm
        (extChartAt 𝓘(ℂ, E) x ((g : H) • (extChartAt 𝓘(ℂ, E) x).symm z) -
          extChartAt 𝓘(ℂ, E) x x))
      (b4cov_lam hE x (g : H) • (b4cov_lineEquiv hE).symm.toContinuousLinearMap)
      (extChartAt 𝓘(ℂ, E) x x) := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hg : (g : H) • x = x := g.property
  let φ := extChartAt 𝓘(ℂ, E) x
  let A : E → E := fun z ↦ φ ((g : H) • φ.symm z)
  have han : AnalyticAt ℂ A (φ x) :=
    b4cov_analyticAt_chart (fun y : X ↦ (g : H) • y) (hH g) x x (φ x)
      (mem_extChartAt_target x) (by
        simp only [φ, extChartAt_to_inv, hg]
        exact mem_extChartAt_source x)
  have hmd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : X ↦ (g : H) • y) x :=
    ((hH g) x).mdifferentiableAt (by simp)
  have hab := hmd.mfderiv_abuse
  rw [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ] at hab
  have hw : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E) x (fun y : X ↦ (g : H) • y) = A := by
    simp only [writtenInExtChartAt, hg]
    rfl
  rw [hw] at hab
  have hd : fderiv ℂ A (φ x) = b4cov_der E x (g : H) := hab.symm
  have hs : HasStrictFDerivAt A (b4cov_der E x (g : H)) (φ x) := by
    rw [← hd]
    exact han.hasStrictFDerivAt
  have hc := (b4cov_lineEquiv hE).symm.toContinuousLinearMap.hasStrictFDerivAt.comp
    (φ x) (hs.sub_const (φ x))
  have hdeq : (b4cov_lineEquiv hE).symm.toContinuousLinearMap.comp
      (b4cov_der E x (g : H)) =
      b4cov_lam hE x (g : H) • (b4cov_lineEquiv hE).symm.toContinuousLinearMap := by
    ext v
    change (b4cov_lineEquiv hE).symm (b4cov_der E x (g : H) v) =
      b4cov_lam hE x (g : H) • (b4cov_lineEquiv hE).symm v
    rw [b4cov_der_apply hE, map_smul]
  rw [hdeq] at hc
  exact hc

theorem rsq_stabilizerCoordinate_hasStrictFDerivAt (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) :
    HasStrictFDerivAt
      (rsq_stabilizerCoordinate hE hH x ∘ (extChartAt 𝓘(ℂ, E) x).symm)
      (b4cov_lineEquiv hE).symm.toContinuousLinearMap
      (extChartAt 𝓘(ℂ, E) x x) := by
  letI := Fintype.ofFinite (MulAction.stabilizer H x)
  exact rsq_weightedSum_hasStrictFDerivAt (b4cov_lamHom hE hH x).toHomUnits
    (fun g z ↦ (b4cov_lineEquiv hE).symm
      (extChartAt 𝓘(ℂ, E) x ((g : H) • (extChartAt 𝓘(ℂ, E) x).symm z) -
        extChartAt 𝓘(ℂ, E) x x))
    (b4cov_lineEquiv hE).symm.toContinuousLinearMap _
    (rsq_centeredChartAction_hasStrictFDerivAt hE hH x)

theorem rsq_stabilizerCoordinate_contMDiffAt (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_stabilizerCoordinate hE hH x) x := by
  classical
  letI := Fintype.ofFinite (MulAction.stabilizer H x)
  let φ := extChartAt 𝓘(ℂ, E) x
  have ht : ∀ g : MulAction.stabilizer H x,
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω
        (fun y ↦ (b4cov_lamHom hE hH x g)⁻¹ *
          (b4cov_lineEquiv hE).symm (φ ((g : H) • y) - φ x)) x := by
    intro g
    have hg : (g : H) • x = x := g.property
    have hφ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω φ ((g : H) • x) := by
      rw [hg]
      exact contMDiffAt_extChartAt
    have hsub := (hφ.comp x ((hH g) x)).sub (contMDiffAt_const (c := φ x))
    have hL := (b4cov_lineEquiv hE).symm.contDiff.contMDiff.contMDiffAt.comp x hsub
    exact contMDiffAt_const.mul hL
  have hs := contMDiffAt_finsetSum (t := Finset.univ) (fun g _ ↦ ht g)
  exact contMDiffAt_const.mul hs

theorem rsq_exists_stabilizerLocalChart (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) :
    ∃ e : OpenPartialHomeomorph X ℂ,
      x ∈ e.source ∧ e x = 0 ∧
      Set.EqOn e (rsq_stabilizerCoordinate hE hH x) e.source ∧
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e x ∧
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e.symm 0 := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let u := rsq_stabilizerCoordinate hE hH x
  let φ := extChartAt 𝓘(ℂ, E) x
  let F := u ∘ φ.symm
  have hs : HasStrictFDerivAt F
      ((b4cov_lineEquiv hE).symm : E →L[ℂ] ℂ) (φ x) :=
    rsq_stabilizerCoordinate_hasStrictFDerivAt hE hH x
  let P := hs.toOpenPartialHomeomorph F
  have hP : (P : E → ℂ) = F := hs.toOpenPartialHomeomorph_coe
  have hxP : φ x ∈ P.source := hs.mem_toOpenPartialHomeomorph_source
  have hφ : (chartAt E x : X → E) = φ := by
    funext y
    simp [φ, extChartAt_coe]
  let e := (chartAt E x).trans P
  have hxe : x ∈ e.source := by
    refine ⟨mem_chart_source E x, ?_⟩
    change chartAt E x x ∈ P.source
    rw [hφ]
    exact hxP
  have heu : Set.EqOn e u e.source := by
    intro y hy
    change P (chartAt E x y) = u y
    rw [hP, hφ]
    change u (φ.symm (φ y)) = u y
    rw [φ.left_inv (by simpa only [φ, extChartAt_source, OpenPartialHomeomorph.symm_target] using hy.1)]
  have he0 : e x = 0 := (heu hxe).trans (rsq_stabilizerCoordinate_center hE hH x)
  have hF0 : F (φ x) = 0 := by
    change u (φ.symm (φ x)) = 0
    rw [φ.left_inv (mem_extChartAt_source x)]
    exact rsq_stabilizerCoordinate_center hE hH x
  have hPt : (0 : ℂ) ∈ P.target := by
    rw [← hF0, ← hP]
    exact P.map_source hxP
  have hPinv : P.symm 0 = φ x := by
    rw [← hF0, ← hP]
    exact P.left_inv hxP
  have hu := rsq_stabilizerCoordinate_contMDiffAt hE hH x
  have hF : ContDiffAt ℂ ω F (φ x) := by
    have ht := (contMDiffAt_iff.1 hu).2
    simpa only [extChartAt_self_eq, modelWithCornersSelf_coe, Function.id_comp,
      Set.range_id, contDiffWithinAt_univ] using ht
  have hPi : ContDiffAt ℂ ω P.symm 0 := P.contDiffAt_symm hPt
    (by rw [hPinv, hP]; exact hs.hasFDerivAt)
    (by rw [hPinv, hP]; exact hF)
  have hφs : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E x).symm (φ x) := by
    have ht := (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, E)) (n := ω) x)).contMDiffAt
      ((chartAt E x).open_target.mem_nhds (mem_chart_target E x))
    simpa only [hφ] using ht
  refine ⟨e, hxe, he0, heu, ?_, ?_⟩
  · exact (Filter.EventuallyEq.contMDiffAt_iff
      (Filter.Eventually.mono (e.open_source.mem_nhds hxe) heu)).2 hu
  · have ht := (show ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E x).symm
        (P.symm 0) from by rw [hPinv]; exact hφs).comp 0 hPi.contMDiffAt
    exact ht

theorem rsq_exists_stabilizerDiscChart [T2Space X]
    (hE : Module.finrank ℂ E = 1)
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (x : X) :
    ∃ (r : ℝ) (e : OpenPartialHomeomorph X ℂ), 0 < r ∧ x ∈ e.source ∧ e x = 0 ∧
      e.target = Metric.ball 0 r ∧
      Set.EqOn e (rsq_stabilizerCoordinate hE hH x) e.source ∧
      (∀ g : MulAction.stabilizer H x, Set.MapsTo (fun y : X ↦ g • y) e.source e.source) ∧
      (∀ y ∈ e.source, ∀ g : H, g • y ∈ e.source → g • x = x) ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e e.source ∧
      ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e.symm e.target := by
  classical
  letI := Fintype.ofFinite (MulAction.stabilizer H x)
  obtain ⟨e₀, hxe, he₀, heu, he, hei⟩ := rsq_exists_stabilizerLocalChart hE hH x
  obtain ⟨N, hN, hsep⟩ := b4cov_exists_separating hH x
  have he' : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e₀ y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 he
  have hei' : ∀ᶠ z in 𝓝 (0 : ℂ), ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e₀.symm z :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hei
  have hei'' : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e₀.symm (e₀ y) :=
    he.continuousAt.tendsto.eventually (by rw [he₀]; exact hei')
  have hn : {y | y ∈ e₀.source ∧ y ∈ N ∧
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e₀ y ∧
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e₀.symm (e₀ y)} ∈ 𝓝 x := by
    filter_upwards [e₀.open_source.mem_nhds hxe, hN, he', hei''] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.1 hn
  obtain ⟨V, hVo, hxV, hVA, hVi⟩ := rsq_invariant_open_neighborhood
    (fun g : MulAction.stabilizer H x ↦ (hH g).continuous) x
    (fun g ↦ g.property) A hAo hxA
  have hVe : V ⊆ e₀.source := fun y hy ↦ (hA (hVA hy)).1
  obtain ⟨r, e, hr, hxe', heV, het, heq, heqi, hest⟩ :=
    rsq_equivariant_disc_restriction (b4cov_lamHom hE hH x).toHomUnits
      (rsq_stabilizerCoordinate hE hH x)
      (rsq_stabilizerCoordinate_equivariant hE hH x)
      e₀ x he₀ heu V hVo hxV hVe hVi
  have hes : e.source ⊆ e₀.source := heV.trans hVe
  refine ⟨r, e, hr, hxe', ?_, het, ?_, hest, ?_, ?_, ?_⟩
  · rw [heq]
    exact he₀
  · intro y hy
    rw [heq]
    exact heu (hes hy)
  · intro y hy g hgy
    exact hsep y (hA (hVA (heV hy))).2.1 g (hA (hVA (heV hgy))).2.1
  · intro y hy
    rw [heq]
    exact (hA (hVA (heV hy))).2.2.1.contMDiffWithinAt
  · intro z hz
    have hy := e.map_target hz
    have hez : e₀ (e.symm z) = z := by rw [← heq]; exact e.right_inv hz
    rw [heqi, ← hez]
    exact (hA (hVA (heV hy))).2.2.2.contMDiffWithinAt

end Stabilizer

end HodgeLean.Foundations.Program
