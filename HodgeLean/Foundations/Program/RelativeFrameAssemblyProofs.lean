import HodgeLean.Foundations.Program.RelativeFrameAssemblyDefs
import HodgeLean.Foundations.Program.RelativeFrameFamily

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-! ## The constructive filling, retained with its atlas and fibre structures -/

section SharedConstruction
open HurwitzPrymRexPunct HurwitzPrymRexFill Metric
attribute [local instance] b4b_group

/-- The constructive filling can use the standard complex coordinate on the sphere.
Source: `HurwitzPrymRexFill.exists_setup`, as `b64c_standard_setup` on `origin/main`. -/
theorem rf8_standard_setup (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
theorem rf8_standard_value (j : Fin 13) (w : ℂ) :
    ξY (ContinuousLinearEquiv.refl ℂ ℂ) (b6_branch mr_base j) w =
      b6a_value mr_base j w := by
  fin_cases j <;>
    simp [ξY, b6_branch, Fin.append, Fin.addCases, b6a_value,
      b4cov_chartAt_coe, b4cov_chartAt_infty, b4cov_chart0_coe, b4cov_chart0_symm,
      b4cov_chartInf_apply, b4cov_chartInf_symm, b4cov_sphInv_infty]

/-- Ramification orders in the constructive filling.
Source: `HurwitzPrymRexPunct.Datum.e`. -/
def rf8_fillOrder (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ) → ℕ :=
  Sum.elim (fun _ ↦ 1) (fun c ↦ (S.D hπ c.1).e)

local instance rf8_fillTop (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    TopologicalSpace (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instTopologicalSpaceCC hπ _

local instance rf8_fillChart (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ChartedSpace ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instChartedSpaceCC hπ _

local instance rf8_fillAction (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    MulAction b4b_Group (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instMulActionCC hπ _

/-- The filling charts give the branch power formulas and the stabilizer rotations.
Source: `Setup.f_eq_on_pChart`, `Setup.smul_pChart_symm`. -/
theorem rf8_fill_local (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hκ : S.κ' = ContinuousLinearEquiv.refl ℂ ℂ)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ∀ x (j : Fin 13), S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) x = b6_branch mr_base j →
      ∃ P : OpenPartialHomeomorph (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ∧ P x = 0 ∧
        (∀ y ∈ P.source, S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) y =
          b6a_value mr_base j (P y ^ rf8_fillOrder U π S hπ x)) ∧
        ∀ g : MulAction.stabilizer b4b_Group x, ∃ ζ : ℂ,
          ζ ^ rf8_fillOrder U π S hπ x = 1 ∧
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
      rw [hκ, hx, rf8_standard_value] at hf
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

/-- A homeomorphism transports analytic charts to the fixed topological fibre.
Source: Mathlib `Homeomorph.transOpenPartialHomeomorph`, `isManifold_of_contDiffOn`;
`b64c_pullback_charts` on `origin/main`. -/
theorem rf8_pullback_charts (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] (e : X ≃ₜ Y) :
    ∃ (_ : ChartedSpace ℂ X) (_ : IsManifold 𝓘(ℂ, ℂ) ω X),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧ ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm := by
  let cs : ChartedSpace ℂ X := {
    atlas := Set.range (fun y : Y ↦ e.transOpenPartialHomeomorph (chartAt ℂ y))
    chartAt := fun x ↦ e.transOpenPartialHomeomorph (chartAt ℂ (e x))
    mem_chart_source := fun x ↦ mem_chart_source ℂ (e x)
    chart_mem_atlas := fun x ↦ ⟨e x, rfl⟩ }
  let : ChartedSpace ℂ X := cs
  have hm : IsManifold 𝓘(ℂ, ℂ) ω X := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    have h := HurwitzPrymRexFill.Y_transition_contDiffOn (E' := ℂ) y y'
    convert h using 1 <;>
      ext z <;> simp [Homeomorph.transOpenPartialHomeomorph]
    change (chartAt ℂ y') (e (e.symm ((chartAt ℂ y).symm z))) = _
    rw [e.apply_symm_apply]
  let : IsManifold 𝓘(ℂ, ℂ) ω X := hm
  refine ⟨cs, hm, ?_, ?_⟩
  · intro x
    apply HurwitzPrymRexFill.contMDiffAt_of_chart e.continuous.continuousAt id contDiffAt_id
    filter_upwards [(chartAt ℂ (e x)).open_target.mem_nhds
      ((chartAt ℂ (e x)).map_source (mem_chart_source ℂ (e x)))] with z hz
    change (chartAt ℂ (e x)) (e (e.symm ((chartAt ℂ (e x)).symm z))) = z
    rw [e.apply_symm_apply, (chartAt ℂ (e x)).right_inv hz]
  · intro y
    apply HurwitzPrymRexFill.contMDiffAt_of_chart e.symm.continuous.continuousAt id contDiffAt_id
    filter_upwards [(chartAt ℂ y).open_target.mem_nhds
      ((chartAt ℂ y).map_source (mem_chart_source ℂ y))] with z hz
    change (chartAt ℂ (e (e.symm y))) (e (e.symm ((chartAt ℂ y).symm z))) = z
    rw [e.apply_symm_apply, e.apply_symm_apply, (chartAt ℂ y).right_inv hz]

/-- Freeness over the punctured sphere gives faithfulness and the unramified stabilizers.
Source: `IsQuotientCoveringMap.disjoint`; `b64c_filling_stabilizers` on `origin/main`. -/
theorem rf8_filling_stabilizers (t : Fin 10 → ℂ) (U C : Type)
    [TopologicalSpace U] [MulAction b4b_Group U] [TopologicalSpace C]
    [MulAction b4b_Group C] (π : U → b6t_punctured t)
    (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : U)
    (f : C → OnePoint ℂ) (ι : U → C) (hi : Function.Injective ι)
    (hr : Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ)
    (he : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u) :
    FaithfulSMul b4b_Group C ∧
      ∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer b4b_Group x = ⊥ := by
  have hfree : ∀ (g : b4b_Group) (u : U), g • u = u → g = 1 := by
    intro g u hgu
    obtain ⟨V, hV, hV'⟩ := hπ.disjoint u
    exact hV' g ⟨u, ⟨u, mem_of_mem_nhds hV, hgu⟩, mem_of_mem_nhds hV⟩
  refine ⟨⟨fun {g k} h ↦ ?_⟩, ?_⟩
  · have h1 : (k⁻¹ * g) • ι u₀ = ι u₀ := by rw [mul_smul, h, inv_smul_smul]
    rw [← he] at h1
    have := hfree _ u₀ (hi h1)
    rwa [inv_mul_eq_one, eq_comm] at this
  · intro x hx
    have : x ∈ Set.range ι := by rw [hr]; exact hx
    obtain ⟨u, rfl⟩ := this
    rw [eq_bot_iff]
    intro g hg
    rw [MulAction.mem_stabilizer_iff, ← he] at hg
    exact hfree g u (hi hg)

/-- The peripheral monodromy identifies the root rotations on any holomorphic filling.
Source: `mr_loops_positive`, covering path lifting; `b64c_cover_roots` on `origin/main`. -/
theorem rf8_cover_roots (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ : b6t_punctured t)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀)
    (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π b4b_Group)
    (u₀ : π ⁻¹' {y₀})
    (hmon : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (f : C → OnePoint ℂ) (ι : U → C)
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hgal : b4_IsGaloisCover b4b_Group f)
    (hιc : Continuous ι)
    (hfι : ∀ u, f (ι u) = π u)
    (hιeq : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hstab : ∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer b4b_Group x = ⊥) :
    ∀ j, ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x (b4b_root j) := by
  intro j
  obtain ⟨c, -, hc⟩ := hγ j
  have hcov := hπ.isCoveringMap
  let L := hcov.liftPath c.toContinuousMap u₀.val (c.source.trans u₀.property.symm)
  have hL1 : L 1 = b4b_root j • u₀.val := by
    have h1 := hcov.monodromy_eq_apply_one (γ := c) (e := u₀) (Γ := L)
      (hcov.liftPath_lifts _ _ _) (hcov.liftPath_zero _ _ _)
    have h2 := hπ.unop_fundamentalGroupToMulOpposite_smul (e := u₀) (γ := γ j)
    rw [hmon, MulOpposite.unop_op] at h2
    change L 1 = _
    rw [← h1, h2, ← hc]
    rfl
  exact mr_loops_positive t ht y₀ γ hγ C b4b_Group hG f hf hgal hstab j c hc
    ⟨ι ∘ L, hιc.comp L.continuous⟩ (b4b_root j) (fun s ↦ by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hfι]
      exact congrArg Subtype.val (congrFun (hcov.liftPath_lifts _ _ _) s))
    (by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hιeq]
      exact congrArg (b4b_root j • ·) (congrArg ι (hcov.liftPath_zero _ _ _).symm))

/-- Root rotations and freeness away from the marked points identify the branch set.
Source: `b4_ramIndex_galois`, `b63_root_order`; `b64c_root_branchSet` on `origin/main`. -/
theorem rf8_root_branchSet (t : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover b4b_Group f)
    (hstab : ∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot : ∀ j, ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x (b4b_root j)) :
    b4_branchSet ℂ ℂ f = Set.range (b6_branch t) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_contra h
    change 2 ≤ b4_ramIndex ℂ ℂ f x at hx
    rw [b4_ramIndex_galois (by simp) (by simp) hG f hf hgal, hstab x h] at hx
    simp at hx
  · rintro ⟨j, rfl⟩
    obtain ⟨x, hx, hr⟩ := hrot j
    refine ⟨x, ?_, hx⟩
    change 2 ≤ b4_ramIndex ℂ ℂ f x
    rw [b4_ramIndex_galois (by simp) (by simp) hG f hf hgal, ← hr.2.1]
    have ho := b63_root_order j
    split_ifs at ho <;> omega

theorem rf8_shared_root_aux  :
    ∃ R : rf8_SharedFamily,
      ∃ (y₀ : b6t_punctured mr_base)
        (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
        (u₀ : R.atlas.π ⁻¹' {y₀}),
        (∀ i, mr_IsLoop mr_base y₀ i (γ i)) ∧
        ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (γ i) =
          MulOpposite.op (b4b_root i) := by
  classical
  have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    simp [mr_curve, mr_outer, mr_basePoint]
  have hmem : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    have h := (mr_curve_avoids mr_base
      (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).1 12 0).1
    rw [h0] at h
    exact h
  let y₀ : b6t_punctured mr_base := ⟨_, hmem⟩
  have hl := fun i ↦ (mr_loop_existsUnique mr_base
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).1 y₀ rfl i).exists
  let γ := fun i ↦ (hl i).choose
  have hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i) := fun i ↦ (hl i).choose_spec
  obtain ⟨U, _, _, _, π, hπ, u₀, hmon, -⟩ := mr_rootCover y₀ γ hγ
  obtain ⟨S, hκ⟩ := rf8_standard_setup U π u₀.val
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : TopologicalSpace C := rf8_fillTop U π S hπ
  let : ChartedSpace ℂ C := rf8_fillChart U π S hπ
  let : MulAction b4b_Group C := rf8_fillAction U π S hπ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let : Nonempty U := ⟨S.u₀⟩
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  let n := rf8_fillOrder U π S hπ
  have hn : ∀ x, 0 < n x := by
    rintro (u | c)
    · exact Nat.zero_lt_one
    · exact (S.D hπ c.1).e_pos
  have hunram : ∀ x, f x ∉ Set.range (b6_branch mr_base) → n x = 1 := by
    rintro (u | c) hx
    · rfl
    · exact False.elim (hx c.1.property)
  have hlocal := rf8_fill_local U π S hκ hπ
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
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hG g).continuous
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
  let : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc mr_base × C) := hm
  have hform := b6a_isolatedFamilyChart_formulas mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hAt : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) :=
    fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩
  let Pa : rf7_HurwitzAtlas mr_base b4b_Group C :=
    { hb := mr_base_mem_chart, U := U, π := π, hπ := hπ, f := f, ι := ι, hf := hf,
      hgal := hgal, hsurj := hs, hact := hG, hι := hι, hrange := hrange, hproj := hproj,
      hequiv := hequiv, total_isManifold := hm, A := A, n := n, hn := hn, hA := hAt,
      hparam := hform.1, hfree := fun q hq ↦ ⟨hunram q.2 hq, hform.2.1 q hq⟩,
      hmark := hform.2.2 }
  have slices := b6a_fibre_geometry mr_base b4b_Group U C π f ι mr_base_mem_chart hπ hf hgal
    hs hG hι hrange hproj hequiv n hn hunram hlocal A hAt hform.1
    (fun q hq ↦ hform.2.1 q hq) hform.2.2
  choose sliceChart sliceMan hk hiSlice hg hsSlice ha _hr _hp using slices
  let e (t : b6t_polydisc mr_base) : rf8_fibre C t ≃ₜ C := b6m_coordinate mr_base C t
  have pulls (t : b6t_polydisc mr_base) :=
    @rf8_pullback_charts (rf8_fibre C t) C _ _ (sliceChart t) (sliceMan t) (e t)
  choose fibreChart fibreMan he heinv using pulls
  let : ∀ t, ChartedSpace ℂ (rf8_fibre C t) := fibreChart
  let : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (rf8_fibre C t) := fibreMan
  let : ∀ t, T2Space (rf8_fibre C t) := fun t ↦ (e t).symm.t2Space
  let : ∀ t, CompactSpace (rf8_fibre C t) := fun t ↦ (e t).symm.compactSpace
  let : ∀ t, ConnectedSpace (rf8_fibre C t) := fun t ↦
    (e t).symm.surjective.connectedSpace (e t).symm.continuous
  have hprojection (t : b6t_polydisc mr_base) :
      b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t =
        (fun x : C ↦ b6a_map mr_base f (t, x)) ∘ e t := by
    funext x
    change b6a_map mr_base f x.val = b6a_map mr_base f (t, x.val.2)
    exact congrArg (b6a_map mr_base f) (Prod.ext x.property rfl)
  have hkF (t : b6t_polydisc mr_base) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t) := by
    let : ChartedSpace ℂ C := sliceChart t
    rw [hprojection]
    exact (hk t).comp (he t)
  have hiF (t : b6t_polydisc mr_base) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : rf8_fibre C t ↦ x.val) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (hiSlice t).comp (he t) using 1
    funext x
    exact Prod.ext x.property rfl
  have hGF (t : b6t_polydisc mr_base) (g : b4b_Group) :
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : rf8_fibre C t ↦ g • x) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (heinv t).comp ((ha t g).comp (he t)) using 1
    funext x
    rfl
  have hsF (t : b6t_polydisc mr_base) : Function.Surjective
      (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t) := by
    rw [hprojection]
    exact (hsSlice t).comp (e t).surjective
  have heact (t : b6t_polydisc mr_base) (g : b4b_Group) (x : rf8_fibre C t) :
      e t (g • x) = g • e t x := rfl
  have hgF (t : b6t_polydisc mr_base) : b4_IsGaloisCover b4b_Group
      (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t) := by
    refine ⟨fun g x ↦ ?_, fun x y h ↦ ?_⟩
    · rw [hprojection]
      change b6a_map mr_base f (t, e t (g • x)) = b6a_map mr_base f (t, e t x)
      rw [heact]
      exact (hg t).1 g (e t x)
    · rw [hprojection] at h
      obtain ⟨g, hg⟩ := (hg t).2 (e t x) (e t y) h
      exact ⟨g, (e t).injective ((heact t g x).trans hg)⟩
  let it (t : b6t_polydisc mr_base) : U → rf8_fibre C t := (e t).symm ∘ ι
  have hit (t : b6t_polydisc mr_base) : Topology.IsOpenEmbedding (it t) :=
    (e t).symm.isOpenEmbedding.comp hι
  have het (t : b6t_polydisc mr_base) (g : b4b_Group) (u : U) :
      it t (g • u) = g • it t u := rfl
  have hrt (t : b6t_polydisc mr_base) : Set.range (it t) =
      (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t) ⁻¹'
        (Set.range (b6_branch t.val))ᶜ := by
    ext x
    have hb := b6a_fibre_branch_preimage mr_base mr_base_mem_chart C f t
    change (∃ u, (e t).symm (ι u) = x) ↔ _
    rw [hprojection]
    change (∃ u, (e t).symm (ι u) = x) ↔
      (e t x) ∉ (fun x : C ↦ b6a_map mr_base f (t, x)) ⁻¹' Set.range (b6_branch t.val)
    rw [hb]
    change (∃ u, (e t).symm (ι u) = x) ↔ e t x ∈ f ⁻¹' (Set.range (b6_branch mr_base))ᶜ
    rw [← hrange]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, ((e t).apply_symm_apply _).symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, (e t).injective (by simpa using hu)⟩
  have stabilizers (t : b6t_polydisc mr_base) :
      FaithfulSMul b4b_Group (rf8_fibre C t) ∧
      ∀ x, b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t x ∉
        Set.range (b6_branch t.val) → MulAction.stabilizer b4b_Group x = ⊥ := by
    obtain ⟨et, -, -, -⟩ := mr_rootCover_family t.val t.property U π hπ y₀ u₀ γ hγ hmon
    exact rf8_filling_stabilizers t.val U (rf8_fibre C t) (et ∘ π)
      (hπ.homeomorph_comp et) u₀.val _ (it t) (hit t).injective (hrt t) (het t)
  let : ∀ t, FaithfulSMul b4b_Group (rf8_fibre C t) := fun t ↦ (stabilizers t).1
  have hrotF (t : b6t_polydisc mr_base) : ∀ j, ∃ x : rf8_fibre C t,
      b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t x =
        b6_branch t.val j ∧ b4_IsRotGen ℂ x (b4b_root j) := by
    obtain ⟨et, hetp, -, hetloops⟩ := mr_rootCover_family t.val t.property U π hπ y₀ u₀ γ hγ hmon
    let πt := et ∘ π
    have hπt := hπ.homeomorph_comp et
    have hstab := (rf8_filling_stabilizers t.val U (rf8_fibre C t) πt hπt u₀.val
      _ (it t) (hit t).injective (hrt t) (het t)).2
    apply rf8_cover_roots t.val t.property (et y₀)
      (fun j ↦ FundamentalGroup.map ⟨et, et.continuous⟩ y₀ (γ j))
      (fun j ↦ (hetloops j).1) U πt hπt ⟨u₀.val, congrArg et u₀.property⟩
      (fun j ↦ (hetloops j).2) (rf8_fibre C t) _ (it t) (hGF t) (hkF t) (hgF t)
      (hit t).continuous _ (het t) hstab
    intro u
    change b6t_sphere mr_base t.val (f (ι u)) = et (π u)
    rw [hproj, hetp]
  have hbranchF (t : b6t_polydisc mr_base) := rf8_root_branchSet t.val (rf8_fibre C t)
    (hGF t) _ (hkF t) (hgF t) (stabilizers t).2 (hrotF t)
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (by simp)
  have hq (t : b6t_polydisc mr_base) :=
    b3_exists_intersectionForm (C := rf8_fibre C t) (E := ℂ) (by simp)
  choose Q hQ using hq
  choose P hP using fun t : b6t_polydisc mr_base ↦ b6m_period_comparison (rf8_fibre C t)
  choose Aop hAop _hsq using fun t : b6t_polydisc mr_base ↦
    b63d_prymOperator_sq mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t (hGF t)
  let R : rf8_SharedFamily :=
    { C := C
      hC := hC
      atlas := Pa
      hincl := hiF
      hG := hGF
      hk := hkF
      hsurj := hsF
      hgal := hgF
      hbranch := hbranchF
      hrot := hrotF
      Q₀ := Q₀
      hQ₀ := hQ₀
      Q := Q
      hQ := hQ
      P := fun t ↦ (P t).toLinearMap
      hP := hP
      A := Aop
      hA := hAop }
  exact ⟨R, y₀, γ, u₀, hγ, hmon⟩

end SharedConstruction

theorem rf8_root_alignment_aux {Y : Type} [TopologicalSpace Y] [ConnectedSpace Y]
    (n : ℕ) (hn : 0 < n) (u v : Y → ℂ) (hu : Continuous u) (hv : Continuous v)
    (hzero : ∀ y, v y ≠ 0) (hpow : ∀ y, u y ^ n = v y ^ n) :
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ ∀ y, u y = ζ * v y := by
  have hroot : ∀ y, (u y / v y) ^ n = 1 := fun y ↦ by
    rw [div_pow, hpow y, div_self (pow_ne_zero n (hzero y))]
  let S := {z : ℂ | z ^ n = 1}
  have hS : S.Finite := by
    have h := (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet
    refine h.subset fun z (hz : z ^ n = 1) ↦ ?_
    simp [Polynomial.mem_nthRoots hn, hz]
  have : Finite S := hS.to_subtype
  let g : Y → S := fun y ↦ ⟨u y / v y, hroot y⟩
  have hg : Continuous g := (hu.div hv hzero).subtype_mk _
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  refine ⟨u y₀ / v y₀, hroot y₀, fun y ↦ ?_⟩
  have h := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hg (x := y) (y := y₀))
  change u y / v y = u y₀ / v y₀ at h
  rw [← h, div_mul_cancel₀ _ (hzero y)]

theorem rf8_principal_equivariance_aux (n : ℕ) (hn : 0 < n) (ζ ε u : ℂ)
    (hζ : ζ ^ n = 1) :
    rf4_rootMap n ε (ζ * u) = ζ * rf4_rootMap n ε u := by
  have h : (ζ * u) ^ (-(n : ℤ)) = u ^ (-(n : ℤ)) := by
    rw [mul_zpow, zpow_neg, zpow_neg, zpow_natCast, hζ, inv_one, one_mul]
  simp only [rf4_rootMap, h, mul_assoc]

/-- An injective analytic function of one variable has nonzero derivative.
Source: local form `(z - z₀)ⁿ g` (Mathlib `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`)
and the inverse function theorem. -/
theorem rf8_deriv_ne_zero_of_injOn {f : ℂ → ℂ} {z₀ : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z₀)
    (hf : AnalyticAt ℂ f z₀) (hinj : InjOn f U) : deriv f z₀ ≠ 0 := by
  intro hd
  have hF : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
  have hnc : ¬ ∀ᶠ z in 𝓝 z₀, f z - f z₀ = 0 := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU h)
    have h1 : z₀ + (ε / 2 : ℝ) ∈ Metric.ball z₀ ε := by
      rw [Metric.mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have h2 := hball h1
    have h3 := hball (Metric.mem_ball_self hε)
    have := hinj h2.1 h3.1 (by rw [sub_eq_zero.mp h2.2, sub_eq_zero.mp h3.2])
    have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    have : (ε / 2 : ℝ) = 0 := by exact_mod_cast this
    linarith
  obtain ⟨n, g, hg, hg0, hfg⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnc
  simp only [smul_eq_mul] at hfg
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have := hfg.self_of_nhds
      simp at this
      exact hg0 this.symm
    · have hD : HasDerivAt (fun z ↦ f z₀ + (z - z₀) ^ 1 * g z) (g z₀) z₀ := by
        have := ((hasDerivAt_id z₀).sub_const z₀).pow 1 |>.mul hg.differentiableAt.hasDerivAt
        have := this.const_add (f z₀)
        simpa using this
      have hfe : f =ᶠ[𝓝 z₀] fun z ↦ f z₀ + (z - z₀) ^ 1 * g z := by
        filter_upwards [hfg] with z hz
        rw [← hz]; ring
      exact hg0 ((hD.congr_of_eventuallyEq hfe).deriv ▸ hd)
  · have hn0 : n ≠ 0 := by omega
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (g z₀) (n := n) (by omega)
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow hn0] at hc; exact hg0 hc.symm
    let r : ℂ → ℂ := fun z ↦ c * (g z / g z₀) ^ ((n : ℂ)⁻¹)
    have hr : AnalyticAt ℂ r z₀ := by
      refine analyticAt_const.mul ((hg.div analyticAt_const hg0).cpow analyticAt_const ?_)
      simp [hg0]
    have hr0 : r z₀ = c := by simp [r, hg0]
    have hrn : ∀ z, r z ^ n = g z := by
      intro z
      simp only [r, mul_pow, Complex.cpow_nat_inv_pow _ hn0]
      rw [hc]
      field_simp
    let φ : ℂ → ℂ := fun z ↦ (z - z₀) * r z
    have hφd : HasStrictDerivAt φ c z₀ := by
      have hφa : AnalyticAt ℂ φ z₀ := (analyticAt_id.sub analyticAt_const).mul hr
      have h1 : HasDerivAt (fun z : ℂ ↦ z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
      have h2 : HasDerivAt φ c z₀ := by
        have := h1.fun_mul hr.differentiableAt.hasDerivAt
        simpa [hr0] using this
      exact h2.deriv ▸ hφa.hasStrictDerivAt
    have hmap := hφd.map_nhds_eq hc0
    have hφ0 : φ z₀ = 0 := by simp [φ]
    rw [hφ0] at hmap
    have hW : U ∩ {z | f z - f z₀ = (z - z₀) ^ n * g z} ∈ 𝓝 z₀ := inter_mem hU hfg
    have himg := Filter.image_mem_map (m := φ) hW
    rw [hmap] at himg
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
    let a : ℂ := ((ε / 2 : ℝ) : ℂ)
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hζ := Complex.isPrimitiveRoot_exp n hn0
    have ha : ‖a‖ = ε / 2 := by
      simp only [a, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ε / 2)]
    have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hn0
    obtain ⟨z1, hz1, hφ1⟩ := hball (show a ∈ Metric.ball 0 ε by
      rw [mem_ball_zero_iff, ha]; linarith)
    obtain ⟨z2, hz2, hφ2⟩ := hball (show ζ * a ∈ Metric.ball 0 ε by
      rw [mem_ball_zero_iff, norm_mul, hζn, one_mul, ha]; linarith)
    have hpow : ∀ z, φ z ^ n = (z - z₀) ^ n * g z := fun z ↦ by
      simp only [φ, mul_pow, hrn]
    have e1 : f z1 - f z₀ = a ^ n := by rw [hz1.2, ← hpow, hφ1]
    have e2 : f z2 - f z₀ = a ^ n := by rw [hz2.2, ← hpow, hφ2, mul_pow, hζ.pow_eq_one, one_mul]
    have hz : z1 = z2 := hinj hz1.1 hz2.1 (by linear_combination e1 - e2)
    have : a = ζ * a := calc
      a = φ z1 := hφ1.symm
      _ = φ z2 := by rw [hz]
      _ = ζ * a := hφ2
    have ha0 : a ≠ 0 := by
      intro h; rw [h, norm_zero] at ha; linarith
    have : ζ = 1 := by
      have := mul_right_cancel₀ ha0 (this.symm.trans (one_mul a).symm)
      exact this
    exact hζ.ne_one (by omega) this

/-- An injective analytic function on an open set of a Riemann surface is one of its charts.
Source: `rf8_deriv_ne_zero_of_injOn`, Mathlib `HasStrictDerivAt.of_local_left_inverse`. -/
theorem rf8_chart_of_injOn {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [Nonempty X] (S : Set X) (hS : IsOpen S) (g : X → ℂ)
    (hg : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g S) (hinj : InjOn g S) :
    ∃ φ : OpenPartialHomeomorph X ℂ, φ.source = S ∧ φ.target = g '' S ∧
      (∀ x ∈ S, φ x = g x) ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X := by
  -- the coordinate expression in any chart
  have hloc : ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X, ∀ y ∈ e.target, e.symm y ∈ S →
      AnalyticAt ℂ (g ∘ e.symm) y ∧ deriv (g ∘ e.symm) y ≠ 0 := by
    intro e he y₀ hy₀ hy₀S
    let D := e.target ∩ e.symm ⁻¹' S
    have hDo : IsOpen D := e.isOpen_inter_preimage_symm hS
    have hana : ∀ y ∈ D, AnalyticAt ℂ (g ∘ e.symm) y := by
      intro y hy
      have h1 := contMDiffAt_symm_of_mem_maximalAtlas he hy.1
      have h2 := (hg (e.symm y) hy.2).contMDiffAt (hS.mem_nhds hy.2)
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp y h1)).analyticAt
    have hyD : y₀ ∈ D := ⟨hy₀, hy₀S⟩
    refine ⟨hana _ hyD, rf8_deriv_ne_zero_of_injOn (hDo.mem_nhds hyD) (hana _ hyD) ?_⟩
    intro y hy y' hy' h
    exact e.symm.injOn hy.1 hy'.1 (hinj hy.2 hy'.2 h)
  have hchart : ∀ x : X, chartAt ℂ x ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X :=
    fun x ↦ IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)
  -- `g` is open on `S`
  have hopen : ∀ V ⊆ S, IsOpen V → IsOpen (g '' V) := by
    intro V hVS hV
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hxV, rfl⟩
    let e := chartAt ℂ x
    have hxe : x ∈ e.source := mem_chart_source ℂ x
    have hx' : e.symm (e x) = x := e.left_inv hxe
    obtain ⟨hA, hd⟩ := hloc e (hchart x) (e x) (e.map_source hxe) (hx'.symm ▸ hVS hxV)
    have hmap := (hA.hasStrictDerivAt).map_nhds_eq hd
    have hmem : e '' (V ∩ e.source) ∈ 𝓝 (e x) :=
      e.image_mem_nhds hxe (inter_mem (hV.mem_nhds hxV) (e.open_source.mem_nhds hxe))
    have := Filter.image_mem_map (m := g ∘ e.symm) hmem
    rw [hmap, Function.comp_apply, hx'] at this
    refine mem_of_superset this ?_
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv.1, by simp [e.left_inv hv.2]⟩
  let pe := hinj.toPartialEquiv g S
  let φ : OpenPartialHomeomorph X ℂ := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    hg.continuousOn (by
      intro V hV
      obtain ⟨W, hW, rfl⟩ := hV
      have := hopen (S ∩ W) inter_subset_left (hS.inter hW)
      convert this using 1
      ext y
      simp [pe, Set.InjOn.toPartialEquiv, and_comm]) hS
  have hsrc : φ.source = S := rfl
  have htgt : φ.target = g '' S := rfl
  have happ : ∀ x ∈ S, φ x = g x := fun _ _ ↦ rfl
  refine ⟨φ, hsrc, htgt, happ, φ.mem_maximalAtlas_of_contMDiffOn
    (hg.congr fun x hx ↦ happ x hx) ?_⟩
  -- the inverse is analytic
  intro y hy
  obtain ⟨x, hxS, rfl⟩ := hy
  have hxφ : φ.symm (g x) = x := by
    rw [← happ x hxS]; exact φ.left_inv hxS
  let e := chartAt ℂ x
  let W := φ.target ∩ φ.symm ⁻¹' e.source
  have hWo : IsOpen W := φ.isOpen_inter_preimage_symm e.open_source
  have hyW : g x ∈ W := ⟨⟨x, hxS, rfl⟩, by
    simp only [mem_preimage, hxφ]; exact mem_chart_source ℂ x⟩
  have hinv : ∀ z ∈ W, g (φ.symm z) = z := by
    intro z hz
    rw [← happ _ (φ.map_target hz.1)]
    exact φ.right_inv hz.1
  have hdiff : DifferentiableOn ℂ (e ∘ φ.symm) W := by
    intro z hz
    have hz' : φ.symm z ∈ S := φ.map_target hz.1
    have hl := e.left_inv hz.2
    obtain ⟨hA, hd⟩ := hloc e (hchart x) (e (φ.symm z)) (e.map_source hz.2) (by rw [hl]; exact hz')
    have hcont : ContinuousAt (e ∘ φ.symm) z :=
      (e.continuousAt hz.2).comp (φ.continuousAt_symm hz.1)
    have := HasStrictDerivAt.of_local_left_inverse hcont hA.hasStrictDerivAt hd (by
      filter_upwards [hWo.mem_nhds hz] with z' hz'
      simp only [Function.comp_apply, e.left_inv hz'.2]
      exact hinv z' hz')
    exact this.hasDerivAt.differentiableAt.differentiableWithinAt
  have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (e ∘ φ.symm) (g x) :=
    contMDiffAt_iff_contDiffAt.mpr ((hdiff.analyticAt (hWo.mem_nhds hyW)).contDiffAt)
  have h2 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ((e ∘ φ.symm) (g x)) := by
    apply contMDiffAt_symm_of_mem_maximalAtlas (hchart x)
    simp only [Function.comp_apply, hxφ]
    exact e.map_source (mem_chart_source ℂ x)
  refine ((h2.comp (g x) h1).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hWo.mem_nhds hyW] with z hz
  simp only [Function.comp_apply, e.left_inv hz.2]

/-- The annulus `r < |u|ⁿ < 2r` is connected. -/
theorem rf8_annulus_isConnected {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    IsConnected (b63r_annulus n r) := by
  let T : Set ℝ := {s | 0 < s ∧ r < s ^ n ∧ s ^ n < 2 * r}
  have hT : IsPreconnected T := by
    refine Set.OrdConnected.isPreconnected ⟨fun s₁ hs₁ s₂ hs₂ s hs ↦ ?_⟩
    have h0 : 0 < s := lt_of_lt_of_le hs₁.1 hs.1
    exact ⟨h0, lt_of_lt_of_le hs₁.2.1 (pow_le_pow_left₀ hs₁.1.le hs.1 n),
      lt_of_le_of_lt (pow_le_pow_left₀ h0.le hs.2 n) hs₂.2.2⟩
  have heq : b63r_annulus n r =
      (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (T ×ˢ univ) := by
    ext u
    constructor
    · intro hu
      have hpos : 0 < ‖u‖ := by
        rcases (norm_nonneg u).lt_or_eq with h | h
        · exact h
        · have := hu.1
          rw [← h, zero_pow (by omega)] at this
          linarith
      exact ⟨(‖u‖, Complex.arg u), ⟨⟨hpos, hu.1, hu.2⟩, mem_univ _⟩,
        Complex.norm_mul_exp_arg_mul_I u⟩
    · rintro ⟨⟨s, θ⟩, ⟨hs, -⟩, rfl⟩
      have hn' : ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ = s := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hs.1.le]
      change r < _ ∧ _ < 2 * r
      rw [hn']
      exact ⟨hs.2.1, hs.2.2⟩
  have hne : (b63r_annulus n r).Nonempty := by
    refine ⟨(((3 * r / 2) ^ ((n : ℝ)⁻¹) : ℝ) : ℂ), ?_⟩
    have hp : 0 ≤ (3 * r / 2) ^ ((n : ℝ)⁻¹) := by positivity
    change r < _ ∧ _ < 2 * r
    rw [Complex.norm_real, Real.norm_of_nonneg hp,
      Real.rpow_inv_natCast_pow (by positivity) (by omega)]
    constructor <;> linarith
  refine ⟨hne, ?_⟩
  rw [heq]
  exact (hT.prod isPreconnected_univ).image _ (Continuous.continuousOn (by fun_prop))

/-- The moving disc is invariant under an `n`th root of unity. -/
theorem rf8_innerDisc_rot {n : ℕ} {r : ℝ} {ε ζ v : ℂ} (hζ : ζ ^ n = 1) :
    ζ * v ∈ rf4_innerDisc n r ε ↔ v ∈ rf4_innerDisc n r ε := by
  simp only [rf4_innerDisc, mem_ofPred_eq, mul_pow, hζ, one_mul]

/-- On a component with `n` points over every value of the collar, a root chart with
`f = c + uⁿ` covers the whole collar by the annulus. -/
theorem rf8_collar_image {C : Type} [TopologicalSpace C] (f : C → OnePoint ℂ) (K : Set C)
    (φ : OpenPartialHomeomorph C ℂ) {n : ℕ} (hn : 1 ≤ n) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hA : b63r_annulus n ρ ⊆ φ.target) (hsrc : φ.source ⊆ K)
    (hf : ∀ y ∈ φ.source, f y = ((c + φ y ^ n : ℂ) : OnePoint ℂ))
    (hcard : ∀ z : ℂ, ρ < dist z c → dist z c < 2 * ρ →
      Nat.card ↥(K ∩ f ⁻¹' {((z : ℂ) : OnePoint ℂ)}) = n) :
    K ∩ f ⁻¹' rf7_sphereAnnulus c ρ (2 * ρ) = φ.symm '' b63r_annulus n ρ := by
  have hval : ∀ u ∈ b63r_annulus n ρ, φ.symm u ∈ K ∧
      f (φ.symm u) = ((c + u ^ n : ℂ) : OnePoint ℂ) := by
    intro u hu
    have hs := φ.map_target (hA hu)
    refine ⟨hsrc hs, ?_⟩
    rw [hf _ hs, φ.right_inv (hA hu)]
  ext y
  constructor
  · rintro ⟨hyK, z, hz, hzy⟩
    have hz0 : z - c ≠ 0 := by
      intro h
      have := hz.1
      rw [dist_eq_norm, h, norm_zero] at this
      linarith
    obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq (z - c) (n := n) (by omega)
    have hu₀0 : u₀ ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hu₀; exact hz0 hu₀.symm
    have hζ := Complex.isPrimitiveRoot_exp n (by omega)
    set ζ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hpow : ∀ j : ℕ, (u₀ * ζ ^ j) ^ n = z - c := fun j ↦ by
      rw [mul_pow, ← pow_mul, mul_comm j, pow_mul, hζ.pow_eq_one, one_pow, mul_one, hu₀]
    have hmemA : ∀ j : ℕ, u₀ * ζ ^ j ∈ b63r_annulus n ρ := by
      intro j
      change ρ < _ ∧ _ < 2 * ρ
      rw [← norm_pow, hpow j, ← dist_eq_norm]
      exact hz
    let F := K ∩ f ⁻¹' {((z : ℂ) : OnePoint ℂ)}
    let m : Fin n → F := fun j ↦ ⟨φ.symm (u₀ * ζ ^ (j : ℕ)), (hval _ (hmemA j)).1, by
      change f _ = _
      rw [(hval _ (hmemA j)).2, hpow j]
      congr 1
      ring⟩
    have hm : Function.Injective m := by
      intro j j' h
      have h1 := congrArg Subtype.val h
      have h2 := φ.symm.injOn (hA (hmemA j)) (hA (hmemA j')) h1
      have h3 : ζ ^ (j : ℕ) = ζ ^ (j' : ℕ) := mul_left_cancel₀ hu₀0 h2
      exact Fin.ext (hζ.pow_inj j.2 j'.2 h3)
    have hF : Nat.card F = n := hcard z hz.1 hz.2
    have : Finite F := Nat.finite_of_card_ne_zero (by omega)
    have hbij := hm.bijective_of_nat_card_le (by rw [Nat.card_fin, hF])
    obtain ⟨j, hj⟩ := hbij.2 ⟨y, hyK, hzy.symm⟩
    exact ⟨_, hmemA j, congrArg Subtype.val hj⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hK, hfu⟩ := hval u hu
    refine ⟨hK, c + u ^ n, ?_, hfu.symm⟩
    change ρ < dist _ c ∧ dist _ c < 2 * ρ
    rw [dist_eq_norm, add_sub_cancel_left, norm_pow]
    exact hu

/-- The branch values of a normalized configuration are distinct. -/
theorem rf8_branch_inj {b : Fin 10 → ℂ} (hb : b ∈ b6_chart) : Function.Injective b := by
  intro i j h
  have h' : b6_branch b (Fin.castAdd 3 i) = b6_branch b (Fin.castAdd 3 j) := by
    simp [b6_branch, h]
  exact Fin.castAdd_injective _ _ (hb h')

/-- The aligned moving root of one disc. -/
theorem rf8_disc_root (R : rf8_SharedFamily) {O : Set R.C} (D : rf4_OuterData R.C O)
    (k : Fin D.m) (i : Fin 10) (x : R.C)
    (hx : R.atlas.f x = ((mr_base i : ℂ) : OnePoint ℂ)) (hc : D.c k = mr_base i)
    (hdeg : D.deg k = R.atlas.n x) (hDr : D.r = rf7_radius mr_base)
    (hsrc : (D.P.chart (D.ann k)).source ⊆
      rf7_component R.atlas.f (mr_base i) (3 * b6t_radius mr_base) x)
    (hform : ∀ y ∈ (D.P.chart (D.ann k)).source,
      R.atlas.f y = ((D.c k + D.P.chart (D.ann k) y ^ D.deg k : ℂ) : OnePoint ℂ)) :
    ∃ (ζ : ℂ) (w : b6t_polydisc mr_base × R.C → ℂ), ζ ^ D.deg k = 1 ∧
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω w
        (univ ×ˢ rf7_component R.atlas.f (mr_base i) (3 * b6t_radius mr_base) x) ∧
      ∀ t : b6t_polydisc mr_base,
        InjOn (fun y ↦ w (t, y)) (rf7_component R.atlas.f (mr_base i) (3 * b6t_radius mr_base) x) ∧
        (fun y ↦ w (t, y)) '' rf7_component R.atlas.f (mr_base i) (3 * b6t_radius mr_base) x =
          {v : ℂ | ‖v ^ D.deg k + (t.val i - mr_base i)‖ < 3 * b6t_radius mr_base} ∧
        (fun y ↦ w (t, y)) '' rf7_inner mr_base R.atlas.f i x =
          rf4_innerDisc (D.deg k) D.r (t.val i - mr_base i) ∧
        ∀ u ∈ b63r_annulus (D.deg k) D.r,
          ζ * w (t, (D.P.chart (D.ann k)).symm u) = rf4_rootMap (D.deg k) (t.val i - mr_base i) u := by
  obtain ⟨w, hw, hwt⟩ := rf7_moving_root R.atlas i x hx
  have hn := R.atlas.hn x
  have hA : b63r_annulus (D.deg k) D.r ⊆ (D.P.chart (D.ann k)).target := by
    rw [← D.hann k]
    exact subset_closure.trans (D.P.contained _)
  let t₀ : b6t_polydisc mr_base := ⟨mr_base, (b6t_polydisc_neighbourhood mr_base R.atlas.hb).1⟩
  let φ := D.P.chart (D.ann k)
  have hYc : ConnectedSpace (b63r_annulus (D.deg k) D.r) :=
    isConnected_iff_connectedSpace.mp (rf8_annulus_isConnected (D.hdeg k) D.hr)
  have hmemK : ∀ a ∈ b63r_annulus (D.deg k) D.r,
      φ.symm a ∈ rf7_component R.atlas.f (mr_base i) (3 * b6t_radius mr_base) x :=
    fun a ha ↦ hsrc (φ.map_target (hA ha))
  have hcont : Continuous (fun a : b63r_annulus (D.deg k) D.r ↦ w (t₀, φ.symm a)) := by
    refine hw.continuousOn.comp_continuous ?_ (fun a ↦ ⟨mem_univ _, hmemK a a.2⟩)
    exact continuous_const.prodMk
      (φ.continuousOn_symm.comp_continuous continuous_subtype_val (fun a ↦ hA a.2))
  have hpowA : ∀ a ∈ b63r_annulus (D.deg k) D.r, a ^ D.deg k = w (t₀, φ.symm a) ^ D.deg k := by
    intro a ha
    have h1 := hform (φ.symm a) (φ.map_target (hA ha))
    rw [φ.right_inv (hA ha), hc] at h1
    have h2 := ((hwt t₀).1 (φ.symm a) (hmemK a ha))
    have h3 : b6a_map mr_base R.atlas.f (t₀, φ.symm a) = R.atlas.f (φ.symm a) := by
      change b6t_sphere mr_base mr_base _ = _
      rw [b6t_identity]; rfl
    rw [h3, h1] at h2
    have h4 := OnePoint.coe_injective h2
    change mr_base i + a ^ D.deg k = mr_base i + w (t₀, φ.symm a) ^ R.atlas.n x at h4
    rw [← hdeg] at h4
    exact add_left_cancel h4
  have hane : ∀ a ∈ b63r_annulus (D.deg k) D.r, a ≠ 0 := by
    intro a ha h
    have := ha.1
    rw [h, norm_zero, zero_pow (by have := D.hdeg k; omega)] at this
    linarith [D.hr]
  obtain ⟨ζ, hζ, hal⟩ := rf8_root_alignment_aux (D.deg k) (by have := D.hdeg k; omega)
    (fun a : b63r_annulus (D.deg k) D.r ↦ (a : ℂ)) (fun a ↦ w (t₀, φ.symm a))
    continuous_subtype_val hcont
    (fun a h ↦ hane a a.2 (pow_eq_zero_iff (by have := D.hdeg k; omega) |>.mp
      ((hpowA a a.2).trans (by rw [h, zero_pow (by have := D.hdeg k; omega)]))))
    (fun a ↦ hpowA a a.2)
  refine ⟨ζ, w, hζ, hw, fun t ↦ ?_⟩
  obtain ⟨-, hinj, himg, hinner, -, hcol⟩ := hwt t
  rw [hdeg, hDr]
  refine ⟨hinj, himg, hinner, fun u hu ↦ ?_⟩
  rw [← hdeg, ← hDr] at hu
  have hy := hmemK u hu
  have h1 := hform (φ.symm u) (φ.map_target (hA hu))
  rw [φ.right_inv (hA hu), hc] at h1
  have hr0 : 0 < b6t_radius mr_base := (b6t_discs mr_base mr_base_mem_chart).1
  have hcl := hcol (φ.symm u) hy (mr_base i + u ^ D.deg k) h1 (by
    rw [dist_eq_norm, add_sub_cancel_left, norm_pow]
    have := hu.1
    rw [hDr] at this
    have := (rf7_radius_bounds mr_base mr_base_mem_chart).1
    linarith)
  have hal' := hal ⟨u, hu⟩
  change u = ζ * w (t₀, φ.symm u) at hal'
  change ζ * w (t, φ.symm u) = _
  rw [hcl, ← rf8_principal_equivariance_aux _ hn _ _ _ (hdeg ▸ hζ), ← hal']

theorem rf8_family_plumbing_aux (R : rf8_SharedFamily) :
    ∃ (D : rf4_OuterData R.C (rf7_outer mr_base R.atlas.f))
      (e : Fin D.m ≃ {x : R.C // ∃ i : Fin 10,
        R.atlas.f x = ((mr_base i : ℂ) : OnePoint ℂ)})
      (idx : Fin D.m → Fin 10)
      (F : rf5_FamilyPlumbing mr_base R.C D (b6t_polydisc mr_base) (Subset.refl _)),
      D.r = rf7_radius mr_base ∧
      (∀ k, R.atlas.f (e k).val = ((mr_base (idx k) : ℂ) : OnePoint ℂ) ∧
        D.c k = mr_base (idx k) ∧ D.deg k = R.atlas.n (e k).val) ∧
      (∀ t k, F.ε t k = t (idx k) - mr_base (idx k)) ∧
      (∀ k, F.wSrc k = univ ×ˢ
        rf7_component R.atlas.f (mr_base (idx k)) (3 * b6t_radius mr_base) (e k).val) ∧
      ∀ (t : b6t_polydisc mr_base) k,
        ((F.S t).w k).source = {y | y.val.2 ∈
          rf7_component R.atlas.f (mr_base (idx k)) (3 * b6t_radius mr_base) (e k).val} := by
  classical
  obtain ⟨D, e, idx, hDr, hk, hann, -, hout⟩ := rf7_outer_data R.atlas
  obtain ⟨-, h2ρ, -, -, -, hsmall⟩ := rf7_radius_bounds mr_base R.atlas.hb
  obtain ⟨-, -, hdisj, hcov, hOI⟩ := rf7_pieces R.atlas
  have hr0 : 0 < b6t_radius mr_base := (b6t_discs mr_base mr_base_mem_chart).1
  let K : Fin D.m → Set R.C := fun k ↦
    rf7_component R.atlas.f (mr_base (idx k)) (3 * b6t_radius mr_base) (e k).val
  have hKo : ∀ k, IsOpen (K k) := fun k ↦
    (rf7_component_props R.atlas (idx k) (e k).val (hk k).1).1
  have hdisc := fun k ↦ rf8_disc_root R D k (idx k) (e k).val (hk k).1 (hk k).2.1 (hk k).2.2 hDr
    (hann k).1 (hann k).2
  choose ζ w hζ hw hwt using hdisc
  have hζ0 : ∀ k, ζ k ≠ 0 := fun k h ↦ by
    have := hζ k
    rw [h, zero_pow (by have := D.hdeg k; omega)] at this
    exact zero_ne_one this
  let ε : (Fin 10 → ℂ) → Fin D.m → ℂ := fun t k ↦ t (idx k) - mr_base (idx k)
  -- the total moving roots
  let W : Fin D.m → b6t_polydisc mr_base × R.C → ℂ := fun k q ↦ ζ k * w k q
  have hW : ∀ k, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (W k) (univ ×ˢ K k) := fun k ↦
    ((contDiff_const.mul contDiff_id).contMDiff).comp_contMDiffOn (hw k)
  have hval : ∀ (t : b6t_polydisc mr_base) (p : rf8_fibre R.C t), p.val = (t, p.val.2) :=
    fun t p ↦ Prod.ext p.property rfl
  -- the fibre root charts
  have hch : ∀ (t : b6t_polydisc mr_base) (k : Fin D.m),
      ∃ φ : OpenPartialHomeomorph (rf8_fibre R.C t) ℂ,
        φ.source = {p | p.val.2 ∈ K k} ∧
        φ.target = (fun p : rf8_fibre R.C t ↦ W k p.val) '' {p | p.val.2 ∈ K k} ∧
        (∀ p ∈ {p : rf8_fibre R.C t | p.val.2 ∈ K k}, φ p = W k p.val) ∧
        φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (rf8_fibre R.C t) := by
    intro t k
    refine rf8_chart_of_injOn (X := rf8_fibre R.C t) {p | p.val.2 ∈ K k}
      ((hKo k).preimage (b6m_coordinate mr_base R.C t).continuous) _ ?_ ?_
    · exact (hW k).comp (R.hincl t).contMDiffOn (fun p hp ↦ ⟨mem_univ _, hp⟩)
    · intro p hp p' hp' h
      have h1 : w k (t, p.val.2) = w k (t, p'.val.2) := by
        have := mul_left_cancel₀ (hζ0 k) h
        rwa [hval t p, hval t p'] at this
      have h2 := ((hwt k t).1 hp hp' h1)
      exact (b6m_coordinate mr_base R.C t).injective h2
  choose φ hφs hφt hφe hφm using hch
  have hA : ∀ k, b63r_annulus (D.deg k) D.r ⊆ (D.P.chart (D.ann k)).target := fun k ↦ by
    rw [← D.hann k]
    exact subset_closure.trans (D.P.contained _)
  -- stationary charts
  have hstat : ∀ (t : b6t_polydisc mr_base) (j : Fin D.P.n),
      (b6m_coordinate mr_base R.C t).toOpenPartialHomeomorph ≫ₕ D.P.chart j ∈
        IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (rf8_fibre R.C t) := by
    intro t j
    obtain ⟨ψ, hψs, -, hψe, hψm⟩ := rf8_chart_of_injOn (X := rf8_fibre R.C t)
      {p | p.val.2 ∈ (D.P.chart j).source}
      ((D.P.chart j).open_source.preimage (b6m_coordinate mr_base R.C t).continuous)
      (fun p ↦ D.P.chart j p.val.2)
      ((hout j).comp (R.hincl t).contMDiffOn (fun p hp ↦ hp))
      (fun p hp p' hp' h ↦ (b6m_coordinate mr_base R.C t).injective
        ((D.P.chart j).injOn hp hp' h))
    refine StructureGroupoid.mem_maximalAtlas_of_eqOnSource
      (G := contDiffGroupoid ω 𝓘(ℂ, ℂ)) ⟨?_, ?_⟩ hψm
    · rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        univ_inter, hψs]
      rfl
    · intro p hp
      rw [hψe p (by
        rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
          univ_inter] at hp
        exact hp)]
      rfl
  -- inner pieces in the fibre
  have hInner : ∀ (t : b6t_polydisc mr_base) (k : Fin D.m),
      (φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k) =
        {p | p.val.2 ∈ rf7_inner mr_base R.atlas.f (idx k) (e k).val} := by
    intro t k
    obtain ⟨-, -, hinner, -⟩ := hwt k t
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (ζ k)⁻¹ * v ∈ rf4_innerDisc (D.deg k) D.r (ε t.val k) :=
        (rf8_innerDisc_rot (by rw [inv_pow, hζ k, inv_one])).mpr hv
      rw [← hinner] at hv'
      obtain ⟨y, hy, hyv⟩ := hv'
      change w k (t, y) = _ at hyv
      have hq : (b6m_coordinate mr_base R.C t).symm y ∈ (φ t k).source := by
        rw [hφs]; exact hy.1
      have hφq : φ t k ((b6m_coordinate mr_base R.C t).symm y) = v := by
        rw [hφe t k _ (hφs t k ▸ hq)]
        change ζ k * w k (t, y) = v
        rw [hyv, ← mul_assoc, mul_inv_cancel₀ (hζ0 k), one_mul]
      rw [← hφq, (φ t k).left_inv hq]
      exact hy
    · intro hp
      have hq : p ∈ (φ t k).source := by rw [hφs]; exact hp.1
      refine ⟨φ t k p, ?_, (φ t k).left_inv hq⟩
      rw [hφe t k p (hφs t k ▸ hq)]
      change ζ k * w k p.val ∈ _
      rw [hval t p, rf8_innerDisc_rot (hζ k), ← hinner]
      exact ⟨_, hp, rfl⟩
  have hcoord : ∀ (t : b6t_polydisc mr_base) (s : Set R.C),
      {p : rf8_fibre R.C t | p.val.2 ∈ s} = (b6m_coordinate mr_base R.C t).symm '' s :=
    fun t s ↦ (congrFun (b6m_coordinate mr_base R.C t).image_symm s).symm
  have hwtarget : ∀ (t : b6t_polydisc mr_base) (k : Fin D.m),
      closure (rf4_innerDisc (D.deg k) D.r (ε t.val k)) ⊆ (φ t k).target := by
    intro t k v hv
    have hle := closure_lt_subset_le (by fun_prop) continuous_const hv
    simp only [Set.mem_ofPred_eq] at hle
    rw [hφt]
    have h3 : (ζ k)⁻¹ * v ∈ {v : ℂ | ‖v ^ D.deg k + (t.val (idx k) - mr_base (idx k))‖ <
        3 * b6t_radius mr_base} := by
      change ‖((ζ k)⁻¹ * v) ^ D.deg k + _‖ < _
      rw [mul_pow, inv_pow, hζ k, inv_one, one_mul]
      change ‖v ^ D.deg k + ε t.val k‖ < _
      rw [hDr] at hle
      linarith
    rw [← (hwt k t).2.1] at h3
    obtain ⟨y, hy, hyv⟩ := h3
    change w k (t, y) = _ at hyv
    refine ⟨(b6m_coordinate mr_base R.C t).symm y, hy, ?_⟩
    change ζ k * w k (t, y) = v
    rw [hyv, ← mul_assoc, mul_inv_cancel₀ (hζ0 k), one_mul]
  have hcover : ∀ (t : b6t_polydisc mr_base) (p : rf8_fibre R.C t),
      (b6m_coordinate mr_base R.C t) p ∈ rf7_outer mr_base R.atlas.f ∨
        ∃ k, p ∈ (φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k) := by
    intro t p
    rcases hcov p.val.2 with hO | ⟨i, y, hy, hin⟩
    · exact Or.inl hO
    · obtain ⟨k, hky⟩ : ∃ k, (e k).val = y := ⟨e.symm ⟨y, i, hy⟩, by rw [e.apply_symm_apply]⟩
      have h2 : R.atlas.f y = ((mr_base (idx k) : ℂ) : OnePoint ℂ) := hky ▸ (hk k).1
      have hi : idx k = i :=
        (rf8_branch_inj R.atlas.hb (OnePoint.coe_injective (hy.symm.trans h2))).symm
      refine Or.inr ⟨k, ?_⟩
      rw [hInner]
      change p.val.2 ∈ rf7_inner mr_base R.atlas.f (idx k) (e k).val
      rw [hi, hky]
      exact hin
  have hdisjoint : ∀ (t : b6t_polydisc mr_base), Pairwise fun k k' : Fin D.m ↦
      Disjoint ((φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k))
        ((φ t k').symm '' rf4_innerDisc (D.deg k') D.r (ε t.val k')) := by
    intro t k k' hkk'
    rw [hInner, hInner]
    have hne : (e k).val ≠ (e k').val := fun h ↦ hkk' (e.injective (Subtype.ext h))
    exact ((hdisj _ _ _ _ (hk k).1 (hk k').1 hne).mono inter_subset_left
      inter_subset_left).preimage (b6m_coordinate mr_base R.C t)
  have hoverlap : ∀ (t : b6t_polydisc mr_base) (k : Fin D.m),
      (b6m_coordinate mr_base R.C t).symm '' rf7_outer mr_base R.atlas.f ∩
        (φ t k).symm '' rf4_innerDisc (D.deg k) D.r (ε t.val k) =
      (b6m_coordinate mr_base R.C t).symm ''
        ((D.P.chart (D.ann k)).symm '' b63r_annulus (D.deg k) D.r) := by
    intro t k
    rw [hInner, hcoord, ← image_inter (b6m_coordinate mr_base R.C t).symm.injective,
      hOI (idx k) (e k).val (hk k).1, ← hDr]
    congr 1
    refine rf8_collar_image R.atlas.f (K k) (D.P.chart (D.ann k)) (D.hdeg k) (mr_base (idx k))
      D.hr (hA k) (hann k).1 (fun y hy ↦ (hk k).2.1 ▸ (hann k).2 y hy) ?_
    intro z hz1 hz2
    rw [(hk k).2.2]
    refine (rf7_component_props R.atlas (idx k) (e k).val (hk k).1).2.2.2.2.2 z ?_ ?_
    · rw [Metric.mem_ball]
      rw [hDr] at hz2
      linarith
    · rintro rfl
      rw [dist_self] at hz1
      linarith [D.hr]
  have hglue : ∀ (t : b6t_polydisc mr_base) (k : Fin D.m), ∀ u ∈ b63r_annulus (D.deg k) D.r,
      (b6m_coordinate mr_base R.C t).symm ((D.P.chart (D.ann k)).symm u) ∈ (φ t k).source ∧
        φ t k ((b6m_coordinate mr_base R.C t).symm ((D.P.chart (D.ann k)).symm u)) =
          rf4_rootMap (D.deg k) (ε t.val k) u := by
    intro t k u hu
    have hs : (b6m_coordinate mr_base R.C t).symm ((D.P.chart (D.ann k)).symm u) ∈
        (φ t k).source := by
      rw [hφs]
      exact (hann k).1 ((D.P.chart (D.ann k)).map_target (hA k hu))
    refine ⟨hs, ?_⟩
    rw [hφe t k _ (hφs t k ▸ hs)]
    exact (hwt k t).2.2.2 u hu
  let S : ∀ t : b6t_polydisc mr_base, rf4_Plumbing D (ε t.val) (rf8_fibre R.C t) := fun t ↦
    { h := (b6m_coordinate mr_base R.C t).symm
      stationary := hstat t
      small := fun k ↦ hDr ▸ hsmall t.val t.property (idx k)
      w := φ t
      w_mem := hφm t
      w_target := hwtarget t
      cover := hcover t
      disjoint := hdisjoint t
      overlap := hoverlap t
      glue := hglue t }
  let F : rf5_FamilyPlumbing mr_base R.C D (b6t_polydisc mr_base) (Subset.refl _) :=
    { ε := ε
      ε_analytic := fun s _ ↦ AnalyticAt.pi fun k ↦ ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 10 ↦ ℂ) (idx k)).analyticAt s).sub analyticAt_const
      S := S
      h_eq := fun t ↦ rfl
      outer_analytic := hout
      wTot := W
      wSrc := fun k ↦ univ ×ˢ K k
      wSrc_open := fun k ↦ isOpen_univ.prod (hKo k)
      w_analytic := hW
      w_source := fun t k p ↦ by
        change p ∈ (φ t k).source ↔ _
        rw [hφs]
        simp
      w_eq := fun t k p hp ↦ hφe t k p (hφs t k ▸ hp) }
  exact ⟨D, e, idx, F, hDr, hk, fun t k ↦ rfl, fun k ↦ rfl, fun t k ↦ hφs t k⟩

theorem rf8_root_relForm_frame_aux (R : rf8_SharedFamily)
    (t₀ : b6t_polydisc mr_base) :
        ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc mr_base ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t₀))) →
          b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) W,
        ∀ t : b6t_polydisc mr_base, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) (θ i) t) = ⊤ := by
  obtain ⟨D, -, -, F, -⟩ := rf8_family_plumbing_aux R
  exact rf6_relForm_frame mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1
    (fun q ↦ ⟨R.atlas.A q, (R.atlas.hA q).2, (R.atlas.hA q).1, R.atlas.hparam q⟩) R.hincl F t₀

theorem rf8_root_filtration_frame_aux (R : rf8_SharedFamily)
    (s : b6t_polydisc mr_base)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s))
    (t₀ : b6t_polydisc mr_base) :
        ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc mr_base ∧
      ∃ c : Fin 6 →
          (Fin 10 → ℂ) → (Fin 12 → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : b6t_polydisc mr_base, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_coordVector B (c i t.val)) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) =
            b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t := by
  obtain ⟨D, -, -, F, -⟩ := rf8_family_plumbing_aux R
  obtain ⟨W, hWo, htW, hWV, c, hc, hfr⟩ := rf6_filtration_frame mr_base R.C R.hC
    (b6t_polydisc mr_base) (Subset.refl _)
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1
    (fun q ↦ ⟨R.atlas.A q, (R.atlas.hA q).2, (R.atlas.hA q).1, R.atlas.hparam q⟩) R.hincl R.hG R.Q R.hQ R.P R.hP F s B t₀
  have hrank : Module.finrank ℂ (b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.P s t₀) = 6 := by
    obtain ⟨E, -, hE⟩ := b63e_lattice_period_transport mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) R.hG R.P R.hP s t₀
    have hd := (b63d_dim_eq mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      t₀ (R.hG t₀) mr_base_mem_chart R.atlas.f (R.hk t₀) (R.hsurj t₀) (R.hgal t₀)
      (R.hbranch t₀) (R.hrot t₀)).2.2
    let eC := E.baseChange ℤ ℂ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)
      (b63l_periodLattice (rf8_fibre R.C t₀))
    rw [hE]
    change Module.finrank ℂ ↥((b63l_periodF _).comap eC.toLinearMap) = 6
    exact (Submodule.comap_equiv_self_of_inj_of_le (p := b63l_periodF _)
      eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq.trans hd
  let e : Fin 6 ≃ Fin (Module.finrank ℂ (b63e_transportedF mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) R.P s t₀)) := finCongr hrank.symm
  refine ⟨W, hWo, htW, hWV, fun i ↦ c (e i), fun i ↦ hc (e i), fun t ht ↦ ?_⟩
  obtain ⟨hli, hsp⟩ := hfr t ht
  refine ⟨hli.comp e e.injective, ?_⟩
  rw [← hsp]
  congr 1
  exact e.surjective.range_comp (fun i ↦ b63e_coordVector B (c i t.val))

theorem rf8_root_polarized_variation_aux (R : rf8_SharedFamily)
    (s : b6t_polydisc mr_base)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)) :
        b2_IsPolarizedTorusFamily (Fin 10 → ℂ) (b63e_localSystem mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1 s B)
      (fun t ↦ b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s ⟨t.val, t.property⟩)
      (fun _ ↦ b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s (R.P s) (R.Q s)) := by
  obtain ⟨D, -, -, F, -⟩ := rf8_family_plumbing_aux R
  exact rf6_polarized_variation mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
    (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1
    (fun q ↦ ⟨R.atlas.A q, (R.atlas.hA q).2, (R.atlas.hA q).1, R.atlas.hparam q⟩) R.hincl R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
    R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP F s B

end HodgeLean.Foundations.Program
