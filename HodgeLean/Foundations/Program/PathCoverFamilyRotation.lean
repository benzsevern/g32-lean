import HodgeLean.Foundations.Program.PathCoverFamilyCircles

/-! # B6-5: the marked cover and its rotation generators along the polydisc

At an admissible centre `c` and a Nielsen tuple `g`: a connected punctured `G`-cover whose
compact holomorphic fillings have rotation generator `g j` over every mark `j`
(`b65z_marked_cover`), and the transfer of these rotation generators to the fillings of its
radial transports over the polydisc about `c` (`b65z_rot_transfer`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Every loop downstairs lifts to a path upstairs whose end is a translate of its start. -/
theorem b65z_loop_lift {X U G : Type} [TopologicalSpace X] [TopologicalSpace U] [Group G]
    [MulAction G U] (π : U → X) (hπ : IsQuotientCoveringMap π G) {y : X} (ℓ : Path y y) :
    ∃ (L : C(unitInterval, U)) (l : G), (∀ x, π (L x) = ℓ x) ∧ L 1 = l • L 0 := by
  obtain ⟨u, hu⟩ := hπ.surjective y
  have hcov := hπ.isCoveringMap
  let L := hcov.liftPath ℓ.toContinuousMap u (ℓ.source.trans hu.symm)
  have hL := hcov.liftPath_lifts ℓ.toContinuousMap u (ℓ.source.trans hu.symm)
  have h01 : π (L 1) = π (L 0) := by
    have h1 := congrFun hL 1
    have h0 := congrFun hL 0
    simp only [Function.comp_apply] at h1 h0
    rw [h1, h0]
    simp
  obtain ⟨l, hl⟩ := (hπ.apply_eq_iff_mem_orbit).mp h01
  exact ⟨L, l, fun x ↦ congrFun hL x, hl.symm⟩

/-- Two rotation generators over one point of a Galois cover are conjugate. -/
theorem b65z_rotGen_conj {C G : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    {Y : Type} (f : C → Y) (hgal : b4_IsGaloisCover G f) (x q : C) (hxq : f x = f q)
    (g l : G) (hx : b4_IsRotGen ℂ x g) (hq : b4_IsRotGen ℂ q l) :
    ∃ h : G, l = h * g * h⁻¹ := by
  obtain ⟨h, rfl⟩ := hgal.2 x q hxq
  exact ⟨h, b4_rotGen_unique (by simp) hG _ l _ hq (RiemannRochTop_rotGen_conjugate hG x h g hx)⟩

/-- Conjugating back a conjugate rotation generator. -/
theorem b65z_rotGen_unconj {C G : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [Group G] [MulAction G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    (q : C) (g h : G) (hq : b4_IsRotGen ℂ q (h * g * h⁻¹)) :
    b4_IsRotGen ℂ (h⁻¹ • q) g := by
  have := RiemannRochTop_rotGen_conjugate hG q h⁻¹ _ hq
  simpa [mul_assoc] using this

/-- **Rotation generators along the polydisc.** Let `π` be a `G`-cover of the sphere punctured
at the marks of `c`, with two compact holomorphic Galois fillings: `ι₁` over `c` itself, with
rotation generator `g j` over each mark `j`, and `ι₂` over `s` in the polydisc, whose projection
is the radial push `b6t_sphere c s ∘ π`. Then the second filling has rotation generator `g j`
over each mark `j` of `s`. The circles of `b65z_circle_rotGen` and `b65z_outer_rotGen` are
fixed by the push, so one lift through `π` serves both fillings.
Source: `b65z_circle_rotGen`, `b65z_outer_rotGen`, `b6t_fixed`, `b4_rotGen_unique`; Hatcher,
*Algebraic Topology*, Proposition 1.30 (path lifting). -/
theorem b65z_rot_transfer (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) {G : Type} [Group G] [Finite G]
    (g : Fin 13 → G) (s : Fin 10 → ℂ) (hs : s ∈ b6t_polydisc c)
    {U : Type} [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured c) (hπ : IsQuotientCoveringMap π G)
    {C₁ : Type} [TopologicalSpace C₁] [ChartedSpace ℂ C₁] [IsManifold 𝓘(ℂ, ℂ) ω C₁]
    [T2Space C₁] [CompactSpace C₁] [ConnectedSpace C₁] [MulAction G C₁] [FaithfulSMul G C₁]
    (hG₁ : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C₁ ↦ k • x))
    (f₁ : C₁ → OnePoint ℂ) (hf₁ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f₁)
    (hgal₁ : b4_IsGaloisCover G f₁)
    (hfree₁ : ∀ x, f₁ x ∉ Set.range (b6_branch c) → MulAction.stabilizer G x = ⊥)
    (ι₁ : U → C₁) (hι₁ : Continuous ι₁) (hfι₁ : ∀ u, f₁ (ι₁ u) = π u)
    (hιeq₁ : ∀ (k : G) (u : U), ι₁ (k • u) = k • ι₁ u)
    (hrot₁ : ∀ j, ∃ x, f₁ x = b6_branch c j ∧ b4_IsRotGen ℂ x (g j))
    {C₂ : Type} [TopologicalSpace C₂] [ChartedSpace ℂ C₂] [IsManifold 𝓘(ℂ, ℂ) ω C₂]
    [T2Space C₂] [CompactSpace C₂] [ConnectedSpace C₂] [MulAction G C₂] [FaithfulSMul G C₂]
    (hG₂ : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C₂ ↦ k • x))
    (f₂ : C₂ → OnePoint ℂ) (hf₂ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f₂)
    (hgal₂ : b4_IsGaloisCover G f₂)
    (hfree₂ : ∀ x, f₂ x ∉ Set.range (b6_branch s) → MulAction.stabilizer G x = ⊥)
    (ι₂ : U → C₂) (hι₂ : Continuous ι₂) (hfι₂ : ∀ u, f₂ (ι₂ u) = b6t_sphere c s (π u))
    (hιeq₂ : ∀ (k : G) (u : U), ι₂ (k • u) = k • ι₂ u) :
    ∀ j, ∃ x, f₂ x = b6_branch s j ∧ b4_IsRotGen ℂ x (g j) := by
  have hcc : c ∈ b6t_polydisc c := b65z_centre_mem c
  have hfix := (b6t_fixed c hc s hs).2.2.2
  intro j
  induction j using Fin.lastCases with
  | last =>
    let M := b65z_outerRadius c
    have hM := b65z_outerRadius_ge c
    have hmem : ∀ u : Circle, ((0 + (u : ℂ) * (M : ℂ) : ℂ) : OnePoint ℂ) ∈ b6t_punctured c := by
      intro u
      apply b65z_outer_avoid c hc c hcc
      rw [zero_add, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    let J := b65z_circleMap c 0 M hmem
    let ℓ := (b65z_turn.map J.continuous).symm
    have hℓ : ∀ x : unitInterval, ((ℓ x : b6t_punctured c) : OnePoint ℂ) = ((Complex.exp
        ((((unitInterval.symm x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
          ((M : ℝ) : ℂ) : ℂ) : OnePoint ℂ) := by
      intro x
      change ((J (b65z_turn (unitInterval.symm x)) : b6t_punctured c) : OnePoint ℂ) = _
      rw [b65z_circleMap_turn, zero_add]
    obtain ⟨L, l, hL, hLend⟩ := b65z_loop_lift π hπ ℓ
    have hfixℓ : ∀ x, b6t_sphere c s (π (L x)) = π (L x) := by
      intro x
      apply hfix
      rw [hL, hℓ]
      apply b65z_outer_fixed c hc
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    let Γ₁ : C(unitInterval, C₁) := ⟨ι₁ ∘ L, hι₁.comp L.continuous⟩
    let Γ₂ : C(unitInterval, C₂) := ⟨ι₂ ∘ L, hι₂.comp L.continuous⟩
    obtain ⟨q₁, hq₁, hl₁⟩ := b65z_outer_rotGen c hc c hcc hG₁ f₁ hf₁ hgal₁ hfree₁ Γ₁ l
      (fun x ↦ by
        change f₁ (ι₁ (L x)) = _
        rw [hfι₁, hL, hℓ])
      (by change ι₁ (L 1) = l • ι₁ (L 0); rw [hLend, hιeq₁])
    obtain ⟨q₂, hq₂, hl₂⟩ := b65z_outer_rotGen c hc s hs hG₂ f₂ hf₂ hgal₂ hfree₂ Γ₂ l
      (fun x ↦ by
        change f₂ (ι₂ (L x)) = _
        rw [hfι₂, hfixℓ, hL, hℓ])
      (by change ι₂ (L 1) = l • ι₂ (L 0); rw [hLend, hιeq₂])
    obtain ⟨x₁, hx₁, hr₁⟩ := hrot₁ (Fin.last 12)
    rw [mr_branch_last] at hx₁
    obtain ⟨h, rfl⟩ := b65z_rotGen_conj hG₁ f₁ hgal₁ x₁ q₁ (hx₁.trans hq₁.symm) _ l hr₁ hl₁
    refine ⟨h⁻¹ • q₂, ?_, b65z_rotGen_unconj hG₂ q₂ _ h hl₂⟩
    rw [hgal₂.1, hq₂, mr_branch_last]
  | cast j =>
    have hsj := b65z_mark_near c s hs j
    have hcj : dist (mr_fin c j) (mr_fin c j) < b6t_radius c := by
      rw [dist_self]; exact b65z_radius_pos c
    let w : ℝ := 2 * b6t_radius c
    let J := b65z_circleMap c (mr_fin s j) w (b65z_circle_mem c hc c hcc j _ hsj)
    let J' := b65z_circleMap c (mr_fin c j) w (b65z_circle_mem c hc c hcc j _ hcj)
    let ℓ := b65z_turn.map J.continuous
    let ℓ' := b65z_turn.map J'.continuous
    obtain ⟨L, l, hL, hLend⟩ := b65z_loop_lift π hπ ℓ
    obtain ⟨L', k, hL', hL'end⟩ := b65z_loop_lift π hπ ℓ'
    have hℓ : ∀ x, ((ℓ x : b6t_punctured c) : OnePoint ℂ) = _ :=
      fun x ↦ b65z_circleMap_turn c (mr_fin s j) w _ x
    have hℓ' : ∀ x, ((ℓ' x : b6t_punctured c) : OnePoint ℂ) = _ :=
      fun x ↦ b65z_circleMap_turn c (mr_fin c j) w _ x
    have hfixℓ : ∀ x, b6t_sphere c s (π (L x)) = π (L x) := by
      intro x
      apply hfix
      rw [hL, hℓ]
      have h := b65z_circle_fixed c hc j (mr_fin s j) hsj
        (Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I))
        (Complex.norm_exp_ofReal_mul_I _)
      convert h using 3
      dsimp only [w]
      push_cast
      ring
    let Γ₁ : C(unitInterval, C₁) := ⟨ι₁ ∘ L, hι₁.comp L.continuous⟩
    let Δ₁ : C(unitInterval, C₁) := ⟨ι₁ ∘ L', hι₁.comp L'.continuous⟩
    let Γ₂ : C(unitInterval, C₂) := ⟨ι₂ ∘ L, hι₂.comp L.continuous⟩
    obtain ⟨q₁, hq₁, hl₁⟩ := b65z_circle_rotGen c hc c hcc j (mr_fin s j) hsj hG₁ f₁ hf₁ hgal₁
      hfree₁ Δ₁ k
      (fun x ↦ by
        change f₁ (ι₁ (L' x)) = _
        rw [hfι₁, hL', hℓ'])
      (by change ι₁ (L' 1) = k • ι₁ (L' 0); rw [hL'end, hιeq₁])
      Γ₁ l
      (fun x ↦ by
        change f₁ (ι₁ (L x)) = _
        rw [hfι₁, hL, hℓ])
      (by change ι₁ (L 1) = l • ι₁ (L 0); rw [hLend, hιeq₁])
    have hΓ₂ : ∀ x : unitInterval, f₂ (Γ₂ x) = ((mr_fin s j +
        Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
          ((2 * b6t_radius c : ℝ) : ℂ) : ℂ) : OnePoint ℂ) := fun x ↦ by
      change f₂ (ι₂ (L x)) = _
      rw [hfι₂, hfixℓ, hL, hℓ]
    have hΓ₂end : Γ₂ 1 = l • Γ₂ 0 := by
      change ι₂ (L 1) = l • ι₂ (L 0); rw [hLend, hιeq₂]
    obtain ⟨q₂, hq₂, hl₂⟩ := b65z_circle_rotGen c hc s hs j (mr_fin s j) hsj hG₂ f₂ hf₂ hgal₂
      hfree₂ Γ₂ l hΓ₂ hΓ₂end Γ₂ l hΓ₂ hΓ₂end
    obtain ⟨x₁, hx₁, hr₁⟩ := hrot₁ j.castSucc
    rw [mr_branch_castSucc] at hx₁
    obtain ⟨h, rfl⟩ := b65z_rotGen_conj hG₁ f₁ hgal₁ x₁ q₁ (hx₁.trans hq₁.symm) _ l hr₁ hl₁
    refine ⟨h⁻¹ • q₂, ?_, b65z_rotGen_unconj hG₂ q₂ _ h hl₂⟩
    rw [hgal₂.1, hq₂, mr_branch_castSucc]

/-- **The punctured cover at an admissible centre.** For a Nielsen tuple `g`, there is a
connected `G`-cover of the sphere punctured at the marks of `c` such that every compact
holomorphic Galois filling, free off the marks, has rotation generator `g j` over every mark
`j`. The cover has based monodromy `op (g j)` on the presentation loops of
`b4_punctured_presentation`, in the reversed order used by `b4_riemannExistence`.
Source: `b4_punctured_presentation`, `b4_exists_galoisCovering`; Völklein, *Groups as Galois
Groups*, Theorem 2.13. -/
theorem b65z_marked_cover (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) {G : Type} [Group G] [Finite G]
    (g : Fin 13 → G) (hg : b4_Nielsen g) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction G U) (_ : ConnectedSpace U)
      (π : U → b6t_punctured c) (_ : IsQuotientCoveringMap π G),
      ∀ (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
        [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C] [FaithfulSMul G C],
        (∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x)) →
        ∀ f : C → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover G f →
        (∀ x, f x ∉ Set.range (b6_branch c) → MulAction.stabilizer G x = ⊥) →
        ∀ ι : U → C, Continuous ι → (∀ u, f (ι u) = π u) →
        (∀ (k : G) (u : U), ι (k • u) = k • ι u) →
        ∀ j, ∃ x, f x = b6_branch c j ∧ b4_IsRotGen ℂ x (g j) := by
  have hY : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
    have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
    rw [h, finrank_bot]
  set b' : Fin 13 → OnePoint ℂ := b6_branch c ∘ Fin.rev
  have hb' : Function.Injective b' := hc.comp Fin.rev_injective
  have hrange : Set.range b' = Set.range (b6_branch c) := Fin.rev_surjective.range_comp _
  have hBfin : (Set.range b').Finite := Set.finite_range b'
  obtain ⟨y₀, hy₀⟩ := HurwitzPrymRR_exists_not_mem (E' := ℂ) (by simp) hBfin
  obtain ⟨γ, -, huniv, hlift⟩ := b4_punctured_presentation (E := ℂ) (E' := ℂ)
    (by simp) (by simp) hY b' hb' ⟨y₀, hy₀⟩
  obtain ⟨φ, hφ, -⟩ := huniv Gᵐᵒᵖ (fun j ↦ MulOpposite.op (g j.rev))
    ((HurwitzPrymRR_prod_op_rev g).trans (by rw [hg.1, MulOpposite.op_one]))
  have hφs : Function.Surjective φ := by
    intro z
    have hz : z.unop ∈ Subgroup.closure (Set.range g) := by rw [hg.2]; trivial
    have key : ∀ x ∈ Subgroup.closure (Set.range g), ∃ a, φ a = MulOpposite.op x := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨γ i.rev, by rw [hφ, Fin.rev_rev]⟩
      | one => exact ⟨1, by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨c, hc⟩ := hy
        exact ⟨c * a, by rw [map_mul, ha, hc, MulOpposite.op_mul]⟩
      | inv x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨a⁻¹, by rw [map_inv, ha, MulOpposite.op_inv]⟩
    obtain ⟨a, ha⟩ := key _ hz
    exact ⟨a, by rw [ha, MulOpposite.op_unop]⟩
  obtain ⟨U, _, _, p, hp, hUc, e₀, he₀⟩ :=
    b4_exists_galoisCovering (E' := ℂ) (by simp) (Set.range b') hBfin ⟨y₀, hy₀⟩ φ hφs
  let eS : ((Set.range b')ᶜ : Set (OnePoint ℂ)) ≃ₜ b6t_punctured c :=
    Homeomorph.setCongr (congrArg compl hrange)
  refine ⟨U, inferInstance, inferInstance, hUc, eS ∘ p, hp.homeomorph_comp eS, ?_⟩
  intro C _ _ _ _ _ _ _ _ hG f hf hgal hfree ι hι hfι hιeq j
  have hfree' : ∀ x, f x ∉ Set.range b' → MulAction.stabilizer G x = ⊥ := by
    rw [hrange]; exact hfree
  obtain ⟨P, hP⟩ := Quotient.exists_rep (FundamentalGroup.toPath (γ j.rev))
  have hPc : FundamentalGroup.fromPath ⟦P⟧ = γ j.rev := by
    rw [hP]
  have hcov := hp.isCoveringMap
  let L := hcov.liftPath P.toContinuousMap e₀.val (P.source.trans e₀.property.symm)
  have hL1 : L 1 = g j • e₀.val := by
    have h1 := hcov.monodromy_eq_apply_one (γ := P) (e := e₀) (Γ := L)
      (hcov.liftPath_lifts _ _ _) (hcov.liftPath_zero _ _ _)
    have h2 := hp.unop_fundamentalGroupToMulOpposite_smul (e := e₀) (γ := γ j.rev)
    rw [he₀, hφ, MulOpposite.unop_op, Fin.rev_rev] at h2
    change L 1 = _
    rw [← h1, h2, ← hPc]
    rfl
  obtain ⟨x, hx, hrot⟩ := hlift C G hG f hf hgal hfree' j.rev P hPc
    ⟨ι ∘ L, hι.comp L.continuous⟩ (g j) (fun t ↦ by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hfι]
      exact congrArg Subtype.val (congrFun (hcov.liftPath_lifts _ _ _) t))
    (by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hιeq]
      exact congrArg (g j • ·) (congrArg ι (hcov.liftPath_zero _ _ _).symm))
  refine ⟨x, ?_, hrot⟩
  rw [hx]
  simp [b']

end HodgeLean.Foundations.Program
