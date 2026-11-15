import HodgeLean.Foundations.Program.PathCoverFamilyRotation
import HodgeLean.Foundations.Program.RelativeFrameAssemblyProofs
import HodgeLean.Foundations.Program.PathCoverFamilyExistence

/-! # B6-5: the retained cover family at an admissible centre (construction)

The construction of `rf8_shared_root_aux` with the centre `mr_base` and the tuple `b4b_root`
replaced by an admissible configuration `c` and a tuple `g` in the G32 Nielsen class: the
entries of `g` are nontrivial, the constructive filling helpers at `c`, and the assembly of a
`b65z_SharedFamily c g`, with the rotation generators of `b65z_rot_transfer` at every
parameter. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- No class representative of the class datum is the identity. -/
theorem b65z_classRep_ne_one (k : Fin 13) : g32h_classRep g32h_omega k ≠ 1 := by
  have hw := g32h_omega_sq_add
  intro h
  unfold g32h_classRep at h
  split_ifs at h
  · have h1 := congrFun (congrFun h 3) 0
    simp [g32R1] at h1
    have : g32h_omega = -2 := by linear_combination h1
    rw [this] at hw; norm_num at hw
  · have h1 := congrFun (congrFun h 1) 0
    simp [g32R2] at h1
    have : g32h_omega = 1 := by linear_combination -h1
    rw [this] at hw; norm_num at hw
  · have h1 := congrFun (congrFun h 1) 1
    simp [g32X, Matrix.mul_apply, Fin.sum_univ_four] at h1
    have : (0 : ℂ) = 1 := by rw [← h1]; ring
    norm_num at this

/-- No entry of a tuple in the G32 Nielsen class is the identity. -/
theorem b65z_nielsen_ne_one (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (j : Fin 13) : g j ≠ 1 := by
  obtain ⟨σ, hσ⟩ := hg.1
  obtain ⟨h, -, h', -, hhh', hgj⟩ := hσ j
  intro h1
  have hgj : b4b_toMatrix (g j) = _ := hgj
  rw [h1, map_one] at hgj
  have hh'h : h' * h = 1 := mul_eq_one_comm.mp hhh'
  apply b65z_classRep_ne_one (σ j)
  calc g32h_classRep g32h_omega (σ j)
      = h' * (h * g32h_classRep g32h_omega (σ j) * h') * h := by
        rw [← mul_assoc, ← mul_assoc, hh'h, one_mul, mul_assoc, hh'h, mul_one]
    _ = 1 := by rw [← hgj, mul_one, hh'h]

/-- Rotation generators of nontrivial order and freeness away from the marks identify the
branch set.
Source: `b4_ramIndex_galois`; `rf8_root_branchSet` with `b4b_root` replaced by `g`. -/
theorem b65z_branchSet (t : Fin 10 → ℂ) (g : Fin 13 → b4b_Group) (hne : ∀ j, g j ≠ 1)
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover b4b_Group f)
    (hstab : ∀ x, f x ∉ Set.range (b6_branch t) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot : ∀ j, ∃ x, f x = b6_branch t j ∧ b4_IsRotGen ℂ x (g j)) :
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
    have h1 : orderOf (g j) ≠ 1 := fun h ↦ hne j (orderOf_eq_one_iff.mp h)
    have h0 : 0 < orderOf (g j) := orderOf_pos (g j)
    omega

section Filling
open HurwitzPrymRexPunct HurwitzPrymRexFill Metric
attribute [local instance] b4b_group

/-- The constructive filling at the centre `c` can use the standard complex coordinate.
Source: `HurwitzPrymRexFill.exists_setup`; `rf8_standard_setup` with `mr_base` replaced by
`c`. -/
theorem b65z_standard_setup (c : Fin 10 → ℂ) (U : Type) [TopologicalSpace U]
    [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch c)}) (u₀ : U) :
    ∃ S : Setup ℂ π, S.κ' = ContinuousLinearEquiv.refl ℂ ℂ := by
  classical
  let B := Set.range (b6_branch c)
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

/-- The centred sphere coordinate is the coordinate of the moving power model at `c`.
Source: `HurwitzPrymRexPunct.ξY`, `b6a_value`; `rf8_standard_value`. -/
theorem b65z_standard_value (c : Fin 10 → ℂ) (j : Fin 13) (w : ℂ) :
    ξY (ContinuousLinearEquiv.refl ℂ ℂ) (b6_branch c j) w = b6a_value c j w := by
  fin_cases j <;>
    simp [ξY, b6_branch, Fin.append, Fin.addCases, b6a_value,
      b4cov_chartAt_coe, b4cov_chartAt_infty, b4cov_chart0_coe, b4cov_chart0_symm,
      b4cov_chartInf_apply, b4cov_chartInf_symm, b4cov_sphInv_infty, add_comm]

/-- Ramification orders in the constructive filling at `c`.
Source: `HurwitzPrymRexPunct.Datum.e`. -/
def b65z_fillOrder (c : Fin 10 → ℂ) (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch c)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ) → ℕ :=
  Sum.elim (fun _ ↦ 1) (fun c ↦ (S.D hπ c.1).e)

local instance b65z_fillTop (c : Fin 10 → ℂ) (U : Type) [TopologicalSpace U]
    [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch c)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    TopologicalSpace (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instTopologicalSpaceCC hπ _

local instance b65z_fillChart (c : Fin 10 → ℂ) (U : Type) [TopologicalSpace U]
    [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch c)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ChartedSpace ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instChartedSpaceCC hπ _

local instance b65z_fillAction (c : Fin 10 → ℂ) (U : Type) [TopologicalSpace U]
    [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch c)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    MulAction b4b_Group (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instMulActionCC hπ _

/-- The filling charts at `c` give the branch power formulas and the stabilizer rotations.
Source: `Setup.f_eq_on_pChart`, `Setup.smul_pChart_symm`; `rf8_fill_local`. -/
theorem b65z_fill_local (c : Fin 10 → ℂ) (U : Type) [TopologicalSpace U]
    [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch c)}) (S : Setup ℂ π)
    (hκ : S.κ' = ContinuousLinearEquiv.refl ℂ ℂ)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ∀ x (j : Fin 13), S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) x = b6_branch c j →
      ∃ P : OpenPartialHomeomorph (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ∧ P x = 0 ∧
        (∀ y ∈ P.source, S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) y =
          b6a_value c j (P y ^ b65z_fillOrder c U π S hπ x)) ∧
        ∀ g : MulAction.stabilizer b4b_Group x, ∃ ζ : ℂ,
          ζ ^ b65z_fillOrder c U π S hπ x = 1 ∧
          Set.MapsTo (fun y ↦ (g : b4b_Group) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : b4b_Group) • y) = ζ * P y := by
  classical
  intro x j hx
  rcases x with u | d
  · exact False.elim ((π u).property ⟨j, hx.symm⟩)
  · let κ := ContinuousLinearEquiv.refl ℂ ℂ
    let P := chartAt ℂ (S.ofP hπ κ d)
    have hPs : P.source = (S.pChart hπ d).source := by
      change ((S.pChart hπ d).trans (κPE κ)).source = _
      simp [PartialEquiv.trans_source, κPE, κ]
    have hPt : P.target = (S.pChart hπ d).target := by
      change ((S.pChart hπ d).trans (κPE κ)).target = _
      simp [PartialEquiv.trans_target, κPE, κ]
    refine ⟨P, mem_chart_source _ _, chart_mem_atlas _ _, S.chartAt_ofP_self hπ κ d, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ (S.pChart hπ d).source := hPs ▸ hy
      have hf := S.f_eq_on_pChart hπ κ d hy'
      change d.1.val = b6_branch c j at hx
      rw [hκ, hx, b65z_standard_value] at hf
      exact hf
    · intro g
      have hgc : (g : b4b_Group) • d = d := by
        have hg := g.property
        change Sum.inr ((g : b4b_Group) • d) = Sum.inr d at hg
        exact Sum.inr.inj hg
      obtain ⟨k, hk⟩ := S.exists_rot hπ (g : b4b_Group) d
      let ζ := (S.D hπ d.1).ζ ^ k
      have hζ : ζ ^ (S.D hπ d.1).e = 1 := by
        dsimp [ζ, Datum.ζ]
        rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast,
          (Complex.isPrimitiveRoot_exp _ (S.D hπ d.1).e_pos.ne').pow_eq_one, one_zpow]
      have hrot (y) (hy : y ∈ P.source) :
          (g : b4b_Group) • y = P.symm (ζ * P y) := by
        have h := S.smul_pChart_symm hπ (g : b4b_Group) d hk
          (hPt ▸ P.map_source hy)
        rw [hgc] at h
        exact (congrArg (fun z ↦ (g : b4b_Group) • z) (P.left_inv hy)).symm.trans h
      have ht (y) (hy : y ∈ P.source) : ζ * P y ∈ P.target := by
        rw [hPt]
        change ‖ζ * P y‖ ^ (S.D hπ d.1).e < S.r d.1
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

attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- **The retained family at an admissible centre.** The construction of `rf8_shared_root_aux`
with the centre `mr_base` and the tuple `b4b_root` replaced by `c` and a Nielsen tuple `g`: the
marked cover of `b65z_marked_cover`, its constructive filling, the B6-2b atlas over the polydisc,
the pulled-back fibre structures, and the rotation generators of `b65z_rot_transfer`.
Source: `rf8_shared_root_aux`; `b65z_marked_cover`, `b65z_rot_transfer`; `b6a_fibre_geometry`,
`b6m_period_comparison`, `b63d_prymOperator_sq`. -/
theorem b65z_family_construction (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) :
    Nonempty (b65z_SharedFamily c g) := by
  classical
  have hne := b65z_nielsen_ne_one g hg
  obtain ⟨U, _, _, _, π, hπ, hpos⟩ := b65z_marked_cover c hc g (b65z_group_nielsen g hg)
  obtain ⟨u₀⟩ : Nonempty U := inferInstance
  obtain ⟨S, hκ⟩ := b65z_standard_setup c U π u₀
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : TopologicalSpace C := b65z_fillTop c U π S hπ
  let : ChartedSpace ℂ C := b65z_fillChart c U π S hπ
  let : MulAction b4b_Group C := b65z_fillAction c U π S hπ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  let n := b65z_fillOrder c U π S hπ
  have hn : ∀ x, 0 < n x := by
    rintro (u | d)
    · exact Nat.zero_lt_one
    · exact (S.D hπ d.1).e_pos
  have hunram : ∀ x, f x ∉ Set.range (b6_branch c) → n x = 1 := by
    rintro (u | d) hx
    · rfl
    · exact False.elim (hx d.1.property)
  have hlocal := b65z_fill_local c U π S hκ hπ
  have hf := S.contMDiff_f hπ κ
  have hgal : b4_IsGaloisCover b4b_Group f :=
    ⟨S.f_smul hπ κ, fun _ _ h ↦ S.exists_smul_of_f_eq hπ κ h⟩
  have hs : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ Set.range (b6_branch c)
    · exact ⟨S.ofP hπ κ ⟨⟨y, hy⟩, QuotientGroup.mk (1 : b4b_Group)⟩, rfl⟩
    · obtain ⟨u, hu⟩ := hπ.surjective ⟨y, hy⟩
      exact ⟨ι u, congrArg Subtype.val hu⟩
  have hG := S.contMDiff_smul hπ κ
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hG g).continuous
  have hι := S.isOpenEmbedding_ι hπ κ
  have hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch c))ᶜ := by
    ext x
    rcases x with u | d
    · exact ⟨fun _ ↦ (π u).property, fun _ ↦ ⟨u, rfl⟩⟩
    · exact ⟨fun ⟨u, hu⟩ ↦ False.elim (Sum.inl_ne_inr hu),
        fun h ↦ False.elim (h d.1.property)⟩
  have hproj : ∀ u, f (ι u) = π u := fun _ ↦ rfl
  have hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u := fun _ _ ↦ rfl
  have stab₀ := rf8_filling_stabilizers c U C π hπ u₀ f ι hι.injective hrange hequiv
  let : FaithfulSMul b4b_Group C := stab₀.1
  have hrot₀ := hpos C hG f hf hgal stab₀.2 ι hι.continuous hproj hequiv
  let A := b6a_isolatedFamilyChart c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  have hA := b6a_mem_isolatedFamilyChart_source c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  let cs := b6a_familyChartedSpace c C A hA
  let : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc c × C) := cs
  have hm := b6a_isolatedFamilyChart_isManifold c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  let : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc c × C) := hm
  have hform := b6a_isolatedFamilyChart_formulas c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hAt : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc c × C) :=
    fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩
  let Pa : rf7_HurwitzAtlas c b4b_Group C :=
    { hb := hc, U := U, π := π, hπ := hπ, f := f, ι := ι, hf := hf,
      hgal := hgal, hsurj := hs, hact := hG, hι := hι, hrange := hrange, hproj := hproj,
      hequiv := hequiv, total_isManifold := hm, A := A, n := n, hn := hn, hA := hAt,
      hparam := hform.1, hfree := fun q hq ↦ ⟨hunram q.2 hq, hform.2.1 q hq⟩,
      hmark := hform.2.2 }
  have slices := b6a_fibre_geometry c b4b_Group U C π f ι hc hπ hf hgal
    hs hG hι hrange hproj hequiv n hn hunram hlocal A hAt hform.1
    (fun q hq ↦ hform.2.1 q hq) hform.2.2
  choose sliceChart sliceMan hk hiSlice hg hsSlice ha _hr _hp using slices
  let e (t : b6t_polydisc c) : b65z_fibre c C t ≃ₜ C := b6m_coordinate c C t
  have pulls (t : b6t_polydisc c) :=
    @rf8_pullback_charts (b65z_fibre c C t) C _ _ (sliceChart t) (sliceMan t) (e t)
  choose fibreChart fibreMan he heinv using pulls
  let : ∀ t, ChartedSpace ℂ (b65z_fibre c C t) := fibreChart
  let : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (b65z_fibre c C t) := fibreMan
  let : ∀ t, T2Space (b65z_fibre c C t) := fun t ↦ (e t).symm.t2Space
  let : ∀ t, CompactSpace (b65z_fibre c C t) := fun t ↦ (e t).symm.compactSpace
  let : ∀ t, ConnectedSpace (b65z_fibre c C t) := fun t ↦
    (e t).symm.surjective.connectedSpace (e t).symm.continuous
  have hprojection (t : b6t_polydisc c) :
      b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t =
        (fun x : C ↦ b6a_map c f (t, x)) ∘ e t := by
    funext x
    change b6a_map c f x.val = b6a_map c f (t, x.val.2)
    exact congrArg (b6a_map c f) (Prod.ext x.property rfl)
  have hkF (t : b6t_polydisc c) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) := by
    let : ChartedSpace ℂ C := sliceChart t
    rw [hprojection]
    exact (hk t).comp (he t)
  have hiF (t : b6t_polydisc c) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b65z_fibre c C t ↦ x.val) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (hiSlice t).comp (he t) using 1
    funext x
    exact Prod.ext x.property rfl
  have hGF (t : b6t_polydisc c) (g : b4b_Group) :
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b65z_fibre c C t ↦ g • x) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (heinv t).comp ((ha t g).comp (he t)) using 1
    funext x
    rfl
  have hsF (t : b6t_polydisc c) : Function.Surjective
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) := by
    rw [hprojection]
    exact (hsSlice t).comp (e t).surjective
  have heact (t : b6t_polydisc c) (g : b4b_Group) (x : b65z_fibre c C t) :
      e t (g • x) = g • e t x := rfl
  have hgF (t : b6t_polydisc c) : b4_IsGaloisCover b4b_Group
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) := by
    refine ⟨fun g x ↦ ?_, fun x y h ↦ ?_⟩
    · rw [hprojection]
      change b6a_map c f (t, e t (g • x)) = b6a_map c f (t, e t x)
      rw [heact]
      exact (hg t).1 g (e t x)
    · rw [hprojection] at h
      obtain ⟨g, hg⟩ := (hg t).2 (e t x) (e t y) h
      exact ⟨g, (e t).injective ((heact t g x).trans hg)⟩
  let it (t : b6t_polydisc c) : U → b65z_fibre c C t := (e t).symm ∘ ι
  have hit (t : b6t_polydisc c) : Topology.IsOpenEmbedding (it t) :=
    (e t).symm.isOpenEmbedding.comp hι
  have het (t : b6t_polydisc c) (g : b4b_Group) (u : U) :
      it t (g • u) = g • it t u := rfl
  have hrt (t : b6t_polydisc c) : Set.range (it t) =
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) ⁻¹'
        (Set.range (b6_branch t.val))ᶜ := by
    ext x
    have hb := b6a_fibre_branch_preimage c hc C f t
    change (∃ u, (e t).symm (ι u) = x) ↔ _
    rw [hprojection]
    change (∃ u, (e t).symm (ι u) = x) ↔
      (e t x) ∉ (fun x : C ↦ b6a_map c f (t, x)) ⁻¹' Set.range (b6_branch t.val)
    rw [hb]
    change (∃ u, (e t).symm (ι u) = x) ↔ e t x ∈ f ⁻¹' (Set.range (b6_branch c))ᶜ
    rw [← hrange]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, ((e t).apply_symm_apply _).symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, (e t).injective (by simpa using hu)⟩
  have stabilizers (t : b6t_polydisc c) :
      FaithfulSMul b4b_Group (b65z_fibre c C t) ∧
      ∀ x, b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t x ∉
        Set.range (b6_branch t.val) → MulAction.stabilizer b4b_Group x = ⊥ := by
    obtain ⟨et, -⟩ := b6t_punctured_homeomorph c hc t.val t.property
    exact rf8_filling_stabilizers t.val U (b65z_fibre c C t) (et ∘ π)
      (hπ.homeomorph_comp et) u₀ _ (it t) (hit t).injective (hrt t) (het t)
  let : ∀ t, FaithfulSMul b4b_Group (b65z_fibre c C t) := fun t ↦ (stabilizers t).1
  have hrotF (t : b6t_polydisc c) : ∀ j, ∃ x : b65z_fibre c C t,
      b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t x =
        b6_branch t.val j ∧ b4_IsRotGen ℂ x (g j) :=
    b65z_rot_transfer c hc g t.val t.property π hπ hG f hf hgal stab₀.2 ι hι.continuous
      hproj hequiv hrot₀ (hGF t) _ (hkF t) (hgF t) (stabilizers t).2 (it t)
      (hit t).continuous (fun u ↦ by
        change b6t_sphere c t.val (f (ι u)) = _
        rw [hproj]) (het t)
  have hbranchF (t : b6t_polydisc c) := b65z_branchSet t.val g hne
    (b65z_fibre c C t) (hGF t) _ (hkF t) (hgF t) (stabilizers t).2 (hrotF t)
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (by simp)
  have hq (t : b6t_polydisc c) :=
    b3_exists_intersectionForm (C := b65z_fibre c C t) (E := ℂ) (by simp)
  choose Q hQ using hq
  choose P hP using fun t : b6t_polydisc c ↦ b6m_period_comparison (b65z_fibre c C t)
  choose Aop hAop _hsq using fun t : b6t_polydisc c ↦
    b63d_prymOperator_sq c C hC (b6t_polydisc c) (Set.Subset.refl _) t (hGF t)
  exact ⟨{ C := C
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
           hA := hAop }⟩

end Filling

end HodgeLean.Foundations.Program
