import HodgeLean.Foundations.Program.RelativeFrameFamilyDefs
import HodgeLean.Foundations.Program.RelativeFrameFamilyStabilizer

noncomputable section
open Set Metric Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
open HurwitzPrymRexPunct HurwitzPrymRexFill
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold b4b_group

/-- The constructive filling can use the standard complex coordinate on the sphere.
Source: `HurwitzPrymRexFill.exists_setup`, with the identity coordinate identification. -/
theorem rf7_marked_setup (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (u₀ : U) :
    ∃ S : Setup ℂ π, S.κ' = ContinuousLinearEquiv.refl ℂ ℂ := by
  classical
  let B := Set.range (b6_branch mr_base)
  have hB : B.Finite := Set.finite_range _
  let κ' := ContinuousLinearEquiv.refl ℂ ℂ
  obtain ⟨O, hO, hOd⟩ := hB.t2_separation
  have hex : ∀ b : B, ∃ r > 0, ball (0 : ℂ) r ⊆ Tgt κ' b.1 ∧
      ∀ z ∈ ball (0 : ℂ) r, ξY κ' b.1 z ∈ O b.1 :=
    fun b ↦ exists_radius b.1 ((hO b.1).2.mem_nhds (hO b.1).1)
  choose r hr hTgt hO' using hex
  have hmemO : ∀ b b' : B, b'.1 ∈ O b.1 → b' = b := by
    intro b b' hb'
    by_contra hne
    exact Set.disjoint_left.1 (hOd b'.2 b.2 (fun h ↦ hne (Subtype.ext h)))
      (hO b'.1).1 hb'
  have havoid : ∀ b : B, ∀ z ∈ ball (0 : ℂ) (r b), ξY κ' b.1 z ∈ B → z = 0 := by
    intro b z hz hzB
    have h1 := hmemO b ⟨_, hzB⟩ (hO' b z hz)
    have h2 : ξY κ' b.1 z = ξY κ' b.1 0 := by
      rw [ξY_zero]; exact congrArg Subtype.val h1
    exact injOn_ξY b.1 (hTgt b hz) (zero_mem_Tgt b.1) h2
  have hdisj : ∀ b b' : B, b ≠ b' → ∀ z ∈ ball (0 : ℂ) (r b),
      ∀ z' ∈ ball (0 : ℂ) (r b'), ξY κ' b.1 z ≠ ξY κ' b'.1 z' := by
    intro b b' hbb' z hz z' hz' heq
    exact Set.disjoint_left.1 (hOd b.2 b'.2 (fun h ↦ hbb' (Subtype.ext h)))
      (hO' b z hz) (heq ▸ hO' b' z' hz')
  exact ⟨⟨κ', r, hr, hTgt, havoid, hdisj, u₀, hB.isClosed⟩, rfl⟩

/-- The centred sphere coordinate is the coordinate used in the moving power model.
Source: `HurwitzPrymRexPunct.ξY`, `b6a_value`. -/
theorem rf7_marked_value (j : Fin 13) (w : ℂ) :
    ξY (ContinuousLinearEquiv.refl ℂ ℂ) (b6_branch mr_base j) w =
      b6a_value mr_base j w := by
  fin_cases j <;>
    simp [ξY, b6_branch, Fin.append, Fin.addCases, b6a_value,
      b4cov_chartAt_coe, b4cov_chartAt_infty, b4cov_chart0_coe, b4cov_chart0_symm,
      b4cov_chartInf_apply, b4cov_chartInf_symm, b4cov_sphInv_infty]

/-- Ramification orders in the constructive filling.
Source: `HurwitzPrymRexPunct.Datum.e`. -/
def rf7_markedOrder (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ) → ℕ :=
  Sum.elim (fun _ ↦ 1) (fun c ↦ (S.D hπ c.1).e)

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) (u : U) :
    rf7_markedOrder U π S hπ (S.ι hπ (ContinuousLinearEquiv.refl ℂ ℂ) u) = 1 := rfl

local instance rf7_markedTop (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    TopologicalSpace (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instTopologicalSpaceCC hπ _

local instance rf7_markedChart (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ChartedSpace ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instChartedSpaceCC hπ _

local instance rf7_markedAction (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    MulAction b4b_Group (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instMulActionCC hπ _

/-- The filling charts give the branch power formulas and the stabilizer rotations.
Source: `Setup.f_eq_on_pChart`, `Setup.smul_pChart_symm`. -/
theorem rf7_marked_local (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hκ : S.κ' = ContinuousLinearEquiv.refl ℂ ℂ)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ∀ x (j : Fin 13), S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) x = b6_branch mr_base j →
      ∃ P : OpenPartialHomeomorph (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ∧ P x = 0 ∧
        (∀ y ∈ P.source, S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) y =
          b6a_value mr_base j (P y ^ rf7_markedOrder U π S hπ x)) ∧
        ∀ g : MulAction.stabilizer b4b_Group x, ∃ ζ : ℂ,
          ζ ^ rf7_markedOrder U π S hπ x = 1 ∧
          Set.MapsTo (fun y ↦ (g : b4b_Group) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : b4b_Group) • y) = ζ * P y := by
  classical
  intro x j hx
  rcases x with u | c
  · exact False.elim ((π u).property ⟨j, hx.symm⟩)
  · let κ := ContinuousLinearEquiv.refl ℂ ℂ
    let P := chartAt ℂ (S.ofP hπ κ c)
    have hPs : P.source = (S.pChart hπ c).source := by
      change ((S.pChart hπ c).trans (κPE κ)).source = _
      simp [PartialEquiv.trans_source, κPE, κ]
    have hPt : P.target = (S.pChart hπ c).target := by
      change ((S.pChart hπ c).trans (κPE κ)).target = _
      simp [PartialEquiv.trans_target, κPE, κ]
    refine ⟨P, mem_chart_source _ _, chart_mem_atlas _ _, S.chartAt_ofP_self hπ κ c, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ (S.pChart hπ c).source := hPs ▸ hy
      have hf := S.f_eq_on_pChart hπ κ c hy'
      change c.1.val = b6_branch mr_base j at hx
      rw [hκ, hx, rf7_marked_value] at hf
      exact hf
    · intro g
      have hgc : (g : b4b_Group) • c = c := by
        have hg := g.property
        change Sum.inr ((g : b4b_Group) • c) = Sum.inr c at hg
        exact Sum.inr.inj hg
      obtain ⟨k, hk⟩ := S.exists_rot hπ (g : b4b_Group) c
      let ζ := (S.D hπ c.1).ζ ^ k
      have hζ : ζ ^ (S.D hπ c.1).e = 1 := by
        dsimp [ζ, Datum.ζ]
        rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast,
          (Complex.isPrimitiveRoot_exp _ (S.D hπ c.1).e_pos.ne').pow_eq_one, one_zpow]
      have hrot (y) (hy : y ∈ P.source) :
          (g : b4b_Group) • y = P.symm (ζ * P y) := by
        have h := S.smul_pChart_symm hπ (g : b4b_Group) c hk
          (hPt ▸ P.map_source hy)
        rw [hgc] at h
        exact (congrArg (fun z ↦ (g : b4b_Group) • z) (P.left_inv hy)).symm.trans h
      have ht (y) (hy : y ∈ P.source) : ζ * P y ∈ P.target := by
        rw [hPt]
        change ‖ζ * P y‖ ^ (S.D hπ c.1).e < S.r c.1
        rw [norm_mul, Datum.norm_ζ_pow, one_mul]
        have hyT := P.map_source hy
        rw [hPt] at hyT
        exact hyT
      refine ⟨ζ, hζ, ?_, ?_⟩
      · intro y hy
        change (g : b4b_Group) • y ∈ P.source
        rw [hrot y hy]
        exact P.map_target (ht y hy)
      · intro y hy
        rw [hrot y hy, P.right_inv (ht y hy)]


/-- At a filled puncture the order is the size of its cyclic isotropy group.
Source: `HurwitzPrymRexPunct.Datum.e`, `rf7_sum_quotient_stabilizer_card`. -/
theorem rf7_marked_order_stabilizer (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group)
    (x : S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) (j : Fin 13)
    (hx : S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) x = b6_branch mr_base j) :
    rf7_markedOrder U π S hπ x = Nat.card (MulAction.stabilizer b4b_Group x) := by
  rcases x with u | ⟨b, q⟩
  · exact False.elim ((π u).property ⟨j, hx.symm⟩)
  · exact (rf7_sum_quotient_stabilizer_card (U := U) (fun b ↦ (S.D hπ b).h) b q).symm

/-- The constructive filling of the marked root cover is an atlas package over `mr_base`, and
its cover carries the root marking.
Source: `mr_rootCover`, `rf7_marked_setup`, `rf7_marked_local`, `b6a_isolatedFamilyChart` and
its manifold and formula theorems (the construction of `b64c_fill_totalSpace` on `main`). -/
theorem rf7_marked_atlas (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C)
      (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C))
      (P : rf7_HurwitzAtlas mr_base b4b_Group C),
      (∃ u₀ : P.π ⁻¹' {y₀}, ∀ i,
        P.hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∀ x (j : Fin 13), P.f x = b6_branch mr_base j → P.n x = orderOf (b4b_root j) := by
  classical
  obtain ⟨U, _, _, _, π, hπ, u₀, hmon, -⟩ := mr_rootCover y₀ γ hγ
  obtain ⟨S, hκ⟩ := rf7_marked_setup U π u₀.val
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : TopologicalSpace C := rf7_markedTop U π S hπ
  let : ChartedSpace ℂ C := rf7_markedChart U π S hπ
  let : MulAction b4b_Group C := rf7_markedAction U π S hπ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let : Nonempty U := ⟨S.u₀⟩
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  let n := rf7_markedOrder U π S hπ
  have hn : ∀ x, 0 < n x := by
    rintro (u | c)
    · exact Nat.zero_lt_one
    · exact (S.D hπ c.1).e_pos
  have hunram : ∀ x, f x ∉ Set.range (b6_branch mr_base) → n x = 1 := by
    rintro (u | c) hx
    · rfl
    · exact False.elim (hx c.1.property)
  have hlocal := rf7_marked_local U π S hκ hπ
  have hf := S.contMDiff_f hπ κ
  have hgal : b4_IsGaloisCover b4b_Group f :=
    ⟨S.f_smul hπ κ, fun _ _ h ↦ S.exists_smul_of_f_eq hπ κ h⟩
  have hs : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ Set.range (b6_branch mr_base)
    · exact ⟨S.ofP hπ κ ⟨⟨y, hy⟩, QuotientGroup.mk (1 : b4b_Group)⟩, rfl⟩
    · obtain ⟨u, hu⟩ := hπ.surjective ⟨y, hy⟩
      exact ⟨ι u, congrArg Subtype.val hu⟩
  have hG := S.contMDiff_smul hπ κ
  have hι := S.isOpenEmbedding_ι hπ κ
  have hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ := by
    ext x
    rcases x with u | c
    · exact ⟨fun _ ↦ (π u).property, fun _ ↦ ⟨u, rfl⟩⟩
    · exact ⟨fun ⟨u, hu⟩ ↦ False.elim (Sum.inl_ne_inr hu),
        fun h ↦ False.elim (h c.1.property)⟩
  have hproj : ∀ u, f (ι u) = π u := fun _ ↦ rfl
  have hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u := fun _ _ ↦ rfl
  let A := b6a_isolatedFamilyChart mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  have hA := b6a_mem_isolatedFamilyChart_source mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  let cs := b6a_familyChartedSpace mr_base C A hA
  let : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) := cs
  have hm := b6a_isolatedFamilyChart_isManifold mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hform := b6a_isolatedFamilyChart_formulas mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hAt : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) :=
    fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩
  let P : rf7_HurwitzAtlas mr_base b4b_Group C :=
    { hb := mr_base_mem_chart, U := U, π := π, hπ := hπ, f := f, ι := ι, hf := hf,
      hgal := hgal, hsurj := hs, hact := hG, hι := hι, hrange := hrange, hproj := hproj,
      hequiv := hequiv, total_isManifold := hm, A := A, n := n, hn := hn, hA := hAt,
      hparam := hform.1, hfree := fun q hq ↦ ⟨hunram q.2 hq, hform.2.1 q hq⟩,
      hmark := hform.2.2 }
  have hfree : ∀ (k : b4b_Group) (u : U), k • u = u → k = 1 := by
    intro k u hku
    obtain ⟨V, hV, hV'⟩ := hπ.disjoint u
    exact hV' k ⟨u, ⟨u, mem_of_mem_nhds hV, hku⟩, mem_of_mem_nhds hV⟩
  have hstab : ∀ x, f x ∉ Set.range (b6_branch mr_base) →
      MulAction.stabilizer b4b_Group x = ⊥ := by
    intro x hx
    have : x ∈ Set.range ι := by rw [hrange]; exact hx
    obtain ⟨u, rfl⟩ := this
    rw [eq_bot_iff]
    intro k hk
    rw [MulAction.mem_stabilizer_iff, ← hequiv] at hk
    exact hfree k u (hι.injective hk)
  letI : FaithfulSMul b4b_Group C := by
    refine ⟨fun {k₁ k₂} h ↦ ?_⟩
    have h1 : (k₂⁻¹ * k₁) • ι u₀.1 = ι u₀.1 := by rw [mul_smul, h, inv_smul_smul]
    rw [← hequiv] at h1
    have := hfree _ u₀.1 (hι.injective h1)
    rwa [inv_mul_eq_one, eq_comm] at this
  refine ⟨C, _, _, _, _, _, _, _, cs, P, ⟨u₀, hmon⟩, ?_⟩
  intro x j hx
  obtain ⟨c, -, hc⟩ := hγ j
  have hcov := hπ.isCoveringMap
  let L := hcov.liftPath c.toContinuousMap u₀.1 (c.source.trans u₀.2.symm)
  have hL1 : L 1 = b4b_root j • u₀.1 := by
    have h1 := hcov.monodromy_eq_apply_one (γ := c) (e := u₀) (Γ := L)
      (hcov.liftPath_lifts _ _ _) (hcov.liftPath_zero _ _ _)
    have h2 := hπ.unop_fundamentalGroupToMulOpposite_smul (e := u₀) (γ := γ j)
    rw [hmon, MulOpposite.unop_op] at h2
    change L 1 = _
    rw [← h1, h2, ← hc]
    rfl
  have hbase := (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).1
  obtain ⟨xj, hxj, hrot⟩ := mr_loops_positive mr_base hbase y₀ γ hγ C b4b_Group hG f hf hgal hstab j c hc
    ⟨ι ∘ L, hι.continuous.comp L.continuous⟩ (b4b_root j) (fun t ↦ by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hproj]
      exact congrArg Subtype.val (congrFun (hcov.liftPath_lifts _ _ _) t))
    (by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hequiv]
      exact congrArg (b4b_root j • ·) (congrArg ι (hcov.liftPath_zero _ _ _).symm))
  obtain ⟨g, hg⟩ := hgal.2 x xj (hx.trans hxj.symm)
  have hcard := Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  exact (rf7_marked_order_stabilizer U π S hπ x j hx).trans
    (hcard.trans hrot.2.1.symm)


end HodgeLean.Foundations.Program
