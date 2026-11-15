import HodgeLean.Foundations.Program.RiemannSurfaceQuotientAtlas

noncomputable section

open Manifold
open scoped ContDiff Topology

namespace HodgeLean.Foundations.Program

section Surface

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]
variable {H : Type} [Group H] [Finite H] [MulAction H X]

theorem rsq_infinite [Nonempty X] (hE : Module.finrank ℂ E = 1) : Infinite X := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨x⟩ := ‹Nonempty X›
  have hi := infinite_of_mem_nhds (chartAt E x x) (chart_target_mem_nhds E x)
  by_contra h
  have : Finite X := not_infinite_iff_finite.mp h
  exact hi ((Set.toFinite (chartAt E x).source).image _ |>.subset
    (by rw [(chartAt E x).image_source_eq_target]))

theorem rsq_proj_nonconstant_aux [ConnectedSpace X] (hE : Module.finrank ℂ E = 1) :
    ∃ x x' : X, rsq_proj H X x ≠ rsq_proj H X x' := by
  classical
  have : Infinite X := rsq_infinite hE
  by_contra h
  push Not at h
  have : Subsingleton (rsq_Quot H X) := ⟨fun a b ↦ by
    induction a using Quotient.inductionOn' with
    | h x =>
      induction b using Quotient.inductionOn' with
      | h y => exact h x y⟩
  have : Finite X := Finite.of_finite_mulAction_orbitRel_quotient H X
  exact not_finite X

theorem rsq_exists_manifold_aux [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x)) :
    ∃ cs : ChartedSpace ℂ (rsq_Quot H X), letI := cs
      IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X) ∧ ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X) := by
  classical
  choose r e hr hx he₀ het heu hest hsep he hei using
    (fun x : X ↦ rsq_exists_stabilizerDiscChart hE hH x)
  have hχ : ∀ x : X, Function.Injective (b4cov_lamHom hE hH x).toHomUnits := by
    intro x a b hab
    apply b4cov_lamHom_injective hE hH x
    exact congrArg Units.val hab
  choose c hcs hct hce using (fun x : X ↦
    rsq_orbit_localChart (fun g ↦ (hH g).continuous) x
      (b4cov_lamHom hE hH x).toHomUnits (hχ x)
      (rsq_stabilizerCoordinate hE hH x)
      (rsq_stabilizerCoordinate_equivariant hE hH x)
      (e x) (hx x) (heu x) (hest x) (hsep x))
  have hcover : ∀ x : X, rsq_proj H X x ∈ (c x).source := by
    intro x
    rw [hcs x]
    exact ⟨x, hx x, rfl⟩
  let cs : ChartedSpace ℂ (rsq_Quot H X) := {
    atlas := Set.range c
    chartAt := fun q ↦ c (Quotient.out q)
    mem_chart_source := fun q ↦ by
      have ht := hcover (Quotient.out q)
      simpa only [rsq_proj, Quotient.out_eq] using ht
    chart_mem_atlas := fun q ↦ ⟨Quotient.out q, rfl⟩ }
  letI := cs
  have hm : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X) := by
    apply isManifold_of_contDiffOn
    intro ca cb hca hcb
    change ca ∈ Set.range c at hca
    change cb ∈ Set.range c at hcb
    obtain ⟨a, rfl⟩ := hca
    obtain ⟨b, rfl⟩ := hcb
    have ht := rsq_orbitChart_transition_analytic hH (e a) (e b) (c a) (c b)
      (Nat.card (MulAction.stabilizer H a)) (Nat.card (MulAction.stabilizer H b))
      Nat.card_pos (r a) (het a) (hcs a) (hct a) (hcs b) (hce a) (hce b) (hei a) (he b)
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using ht
  letI := hm
  refine ⟨cs, hm, ?_⟩
  intro y
  let a := Quotient.out (rsq_proj H X y)
  have hya : rsq_proj H X y ∈ (c a).source := mem_chart_source ℂ (rsq_proj H X y)
  have hcomp := rsq_contMDiffAt_orbit_chart_composite hH (e a) (he a) (c a)
    (Nat.card (MulAction.stabilizer H a)) (hce a) y ((hcs a) ▸ hya)
  rw [contMDiffAt_iff]
  refine ⟨continuous_quotient_mk'.continuousAt, ?_⟩
  have htarget : (extChartAt 𝓘(ℂ, ℂ) (rsq_proj H X y) : rsq_Quot H X → ℂ) = c a := rfl
  rw [htarget]
  have ht := (contMDiffAt_iff.1 hcomp).2
  simpa only [extChartAt_self_eq, modelWithCornersSelf_coe, Function.id_comp,
    Function.comp_assoc] using ht

theorem rsq_analyticAt_regular
    (hE : Module.finrank ℂ E = 1)
    {Q : Type} [TopologicalSpace Q] [ChartedSpace ℂ Q] [IsManifold 𝓘(ℂ, ℂ) ω Q]
    (π : X → Q) (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω π)
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (f : Q → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω (f ∘ π))
    (x : X) (q : Q) (y : Y)
    (hx : π x ∈ (extChartAt 𝓘(ℂ, ℂ) q).source)
    (hy : f (π x) ∈ (extChartAt 𝓘(ℂ, E') y).source)
    (hd : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) π x ≠ 0) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, E') y ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm)
      (extChartAt 𝓘(ℂ, ℂ) q (π x)) := by
  let φ := extChartAt 𝓘(ℂ, E) x
  let ψ := extChartAt 𝓘(ℂ, ℂ) q
  let χ := extChartAt 𝓘(ℂ, E') y
  let G := ψ ∘ π ∘ φ.symm
  have hφ : x ∈ φ.source := mem_extChartAt_source x
  have hG : AnalyticAt ℂ G (φ x) :=
    b4cov_analyticAt_chart π hπ x q (φ x) (φ.map_source hφ)
      (by rw [φ.left_inv hφ]; exact hx)
  have hdG : fderiv ℂ G (φ x) ≠ 0 :=
    (b4cov_mfderiv_ne_zero_iff_expr π hπ x q x hφ hx).1 hd
  obtain ⟨σ, hσ, hσx, hGσ, -⟩ :=
    b4cov_exists_localInverse hE (Module.finrank_self ℂ) hG hdG
  have hGx : G (φ x) = ψ (π x) := by simp only [G, Function.comp_apply, φ.left_inv hφ]
  rw [hGx] at hσ hσx hGσ
  have hF : AnalyticAt ℂ (χ ∘ (f ∘ π) ∘ φ.symm) (φ x) :=
    b4cov_analyticAt_chart (f ∘ π) hf x y (φ x) (φ.map_source hφ)
      (by change f (π (φ.symm (φ x))) ∈ χ.source
          rw [φ.left_inv hφ]; exact hy)
  have hcσ : ContinuousAt (φ.symm ∘ σ) (ψ (π x)) :=
    (show ContinuousAt φ.symm (σ (ψ (π x))) from by
      rw [hσx]; exact continuousAt_extChartAt_symm x).comp hσ.continuousAt
  have hπsrc : ∀ᶠ w in 𝓝 (ψ (π x)), π (φ.symm (σ w)) ∈ ψ.source :=
    (hπ.continuous.continuousAt.comp hcσ).preimage_mem_nhds
      (by change ψ.source ∈ 𝓝 (π (φ.symm (σ (ψ (π x)))))
          rw [hσx, φ.left_inv hφ]
          exact isOpen_extChartAt_source q |>.mem_nhds hx)
  have heq : (χ ∘ f ∘ ψ.symm) =ᶠ[𝓝 (ψ (π x))]
      ((χ ∘ (f ∘ π) ∘ φ.symm) ∘ σ) := by
    filter_upwards [hGσ, hπsrc] with w hw hwp
    change χ (f (ψ.symm w)) = χ (f (π (φ.symm (σ w))))
    have hw' : ψ (π (φ.symm (σ w))) = w := hw
    exact congrArg (fun q ↦ χ (f q))
      ((congrArg ψ.symm hw'.symm).trans (ψ.left_inv hwp))
  have hFc : AnalyticAt ℂ ((χ ∘ (f ∘ π) ∘ φ.symm) ∘ σ) (ψ (π x)) :=
    (show AnalyticAt ℂ (χ ∘ (f ∘ π) ∘ φ.symm) (σ (ψ (π x))) from by
      rw [hσx]; exact hF).comp hσ
  exact hFc.congr heq.symm

theorem rsq_contMDiff_of_comp_aux [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    [ChartedSpace ℂ (rsq_Quot H X)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot H X)]
    (hπ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (rsq_proj H X))
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
    {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (f : rsq_Quot H X → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω (f ∘ rsq_proj H X)) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E') ω f := by
  have : CompleteSpace E' := FiniteDimensional.complete ℂ E'
  have hc : Continuous f := isQuotientMap_quotient_mk'.continuous_iff.2 hf.continuous
  have hcrit := b4cov_critical_finite hE (rsq_proj H X) hπ
    (rsq_proj_nonconstant_aux hE)
  intro q
  rw [contMDiffAt_iff]
  refine ⟨hc.continuousAt, ?_⟩
  let ψ := extChartAt 𝓘(ℂ, ℂ) q
  let χ := extChartAt 𝓘(ℂ, E') (f q)
  have hψq : ψ.symm (ψ q) = q := ψ.left_inv (mem_extChartAt_source q)
  have hgood : ∀ᶠ z in 𝓝 (ψ q), z ∈ b4cov_good ℂ E' f q :=
    (b4cov_good_isOpen f hc q).mem_nhds (b4cov_mem_good f q)
  let S := ψ '' (rsq_proj H X ''
    {x | mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (rsq_proj H X) x = 0})
  have hS : S.Finite := (hcrit.image (rsq_proj H X)).image ψ
  have havoid : ∀ᶠ z in 𝓝[≠] (ψ q), z ∉ S :=
    nhdsNE_le_cofinite _ hS.compl_mem_cofinite
  have hd : ∀ᶠ z in 𝓝[≠] (ψ q), DifferentiableAt ℂ (χ ∘ f ∘ ψ.symm) z := by
    filter_upwards [havoid, Filter.Eventually.filter_mono nhdsWithin_le_nhds hgood]
      with z hzS hz
    obtain ⟨x, hx⟩ := Quotient.mk_surjective (ψ.symm z)
    change rsq_proj H X x = ψ.symm z at hx
    have hxψ : rsq_proj H X x ∈ ψ.source := by
      rw [hx]; exact ψ.map_target hz.1
    have hxχ : f (rsq_proj H X x) ∈ χ.source := by
      rw [hx]; exact hz.2
    have hxreg : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (rsq_proj H X) x ≠ 0 := by
      intro he
      apply hzS
      exact ⟨rsq_proj H X x, ⟨x, he, rfl⟩, by rw [hx, ψ.right_inv hz.1]⟩
    have han := rsq_analyticAt_regular hE (rsq_proj H X) hπ f hf x q (f q) hxψ hxχ hxreg
    have he : ψ (rsq_proj H X x) = z := by rw [hx, ψ.right_inv hz.1]
    rw [he] at han
    exact han.differentiableAt
  have hcψ : ContinuousAt (f ∘ ψ.symm) (ψ q) :=
    (hc.continuousAt (x := ψ.symm (ψ q))).comp
      (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) q)
  have hχ : ContinuousAt χ ((f ∘ ψ.symm) (ψ q)) := by
    change ContinuousAt χ (f (ψ.symm (ψ q)))
    rw [hψq]
    exact continuousAt_extChartAt (f q)
  have hcont : ContinuousAt (χ ∘ f ∘ ψ.symm) (ψ q) := hχ.comp hcψ
  have han := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont
  simpa only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
    using han.contDiffAt

theorem rsq_faithful_quotient_aux [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : X ↦ g • x))
    (K : Subgroup H) [K.Normal] :
    FaithfulSMul (H ⧸ K) (rsq_Quot K X) := by
  classical
  have : Infinite X := rsq_infinite hE
  obtain ⟨x, hx⟩ := (HurwitzPrymRex_fixedPoints_finite hE hH).exists_notMem
  have hfree : ∀ g : H, g • x = x → g = 1 := by
    intro g hg
    by_contra hn
    exact hx ⟨g, hn, hg⟩
  refine ⟨fun {a b} hab ↦ ?_⟩
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have he := hab (rsq_proj K X x)
      change rsq_proj K X (a • x) = rsq_proj K X (b • x) at he
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact he)
      have he1 : (a⁻¹ * k * b) • x = x := by
        simpa [mul_smul, Subgroup.smul_def] using congrArg (fun y : X ↦ a⁻¹ • y) hk
      have he2 := hfree _ he1
      have he3 : a = (k : H) * b := by
        have := congrArg (fun g : H ↦ a * g) he2
        simpa [mul_assoc] using this.symm
      rw [he3, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (k : H)).2 k.2, one_mul]

end Surface

theorem rsq_card_stabilizer_quotient_aux {H X : Type} [Group H] [Finite H] [MulAction H X]
    (K : Subgroup H) [K.Normal] (x : X) :
    Nat.card (MulAction.stabilizer (H ⧸ K) (rsq_proj K X x)) *
      Nat.card (MulAction.stabilizer K x) = Nat.card (MulAction.stabilizer H x) := by
  let f : MulAction.stabilizer H x →*
      MulAction.stabilizer (H ⧸ K) (rsq_proj K X x) :=
    { toFun := fun g ↦ ⟨(g : H), by
        change rsq_proj K X ((g : H) • x) = rsq_proj K X x
        rw [g.property]⟩
      map_one' := Subtype.ext (by rfl)
      map_mul' := fun a b ↦ Subtype.ext (by rfl) }
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (a : H ⧸ K)
    have ha := a.property
    rw [← hh] at ha
    change rsq_proj K X (h • x) = rsq_proj K X x at ha
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact ha)
    refine ⟨⟨(k : H)⁻¹ * h, ?_⟩, ?_⟩
    · change ((k : H)⁻¹ * h) • x = x
      rw [mul_smul, ← hk]
      simp [Subgroup.smul_def]
    · apply Subtype.ext
      change (((k : H)⁻¹ * h : H) : H ⧸ K) = (a : H ⧸ K)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff (k : H)).2 k.2, inv_one, one_mul, hh]
  let e : MulAction.stabilizer K x ≃ f.ker :=
    { toFun := fun k ↦ ⟨⟨(k : K), k.property⟩,
        show f ⟨(k : K), k.property⟩ = 1 from
          Subtype.ext ((QuotientGroup.eq_one_iff (k : H)).2 k.val.property)⟩
      invFun := fun g ↦ ⟨⟨(g.val : H),
        (QuotientGroup.eq_one_iff (g.val : H)).1 (congrArg Subtype.val g.property)⟩,
        g.val.property⟩
      left_inv := fun k ↦ by rfl
      right_inv := fun g ↦ by rfl }
  rw [mul_comm, Nat.card_congr e]
  exact Subgroup.card_ker_mul_card_of_surjective hs

theorem rsq_tower_isHomeomorph_aux {H X : Type} [Group H] [MulAction H X] [TopologicalSpace X]
    (K : Subgroup H) [K.Normal] :
    IsHomeomorph (rsq_tower (X := X) K) := by
  let j : rsq_Quot H X → rsq_Quot (H ⧸ K) (rsq_Quot K X) :=
    rsq_lift (fun x ↦ rsq_proj (H ⧸ K) (rsq_Quot K X) (rsq_proj K X x))
      (fun g x ↦ by
        change rsq_proj (H ⧸ K) (rsq_Quot K X)
          ((g : H ⧸ K) • rsq_proj K X x) = _
        exact MulAction.orbitRel.Quotient.quotient_smul_eq)
  have hj : Continuous j :=
    (continuous_quotient_mk'.comp continuous_quotient_mk').quotient_lift _
  have hl : Function.LeftInverse j (rsq_tower (X := X) K) := by
    intro q
    induction q using Quotient.inductionOn' with
    | h q =>
      induction q using Quotient.inductionOn' with
      | h x => rfl
  have hr : Function.RightInverse j (rsq_tower (X := X) K) := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x => rfl
  exact (show rsq_Quot (H ⧸ K) (rsq_Quot K X) ≃ₜ rsq_Quot H X from
    { toFun := rsq_tower K
      invFun := j
      left_inv := hl
      right_inv := hr
      continuous_toFun := (continuous_quotient_mk'.quotient_lift _).quotient_lift _
      continuous_invFun := hj }).isHomeomorph

end HodgeLean.Foundations.Program
