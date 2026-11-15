import HodgeLean.Foundations.Program.PeriodFunction
import HodgeLean.Foundations.Program.MarkedRootCover
import HodgeLean.Foundations.Program.HurwitzFamilyAnalytic

/-! # B6-4c: marked root cover input checks -/

noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The parameter domain contains the marked base and is open and nonempty.
Source: `b6t_polydisc_neighbourhood`, `mr_base_mem_chart`. -/
theorem b64c_root_domain :
    mr_base ∈ b6t_polydisc mr_base ∧ (b6t_polydisc mr_base).Nonempty ∧
      IsOpen (b6t_polydisc mr_base) ∧ b6t_polydisc mr_base ⊆ b6_chart :=
  b6t_polydisc_neighbourhood mr_base mr_base_mem_chart

/-- The marked root base has its intersection form and integral period comparison.
Source: `mr_rootCover`, `b3_exists_intersectionForm`, `b6m_period_comparison`. -/
theorem b64c_root_base_inputs (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
      (f : C → OnePoint ℂ),
      (∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ Function.Surjective f ∧
      b4_IsGaloisCover b4b_Group f ∧
      (∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j)) ∧
      (∃ Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C), b3_IsIntersectionForm ℂ Q) ∧
      ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
        ∀ δ : b3_SmoothLoop ℂ C, P (b6m_loopClass C δ) = b3_latticePeriod ℂ C δ := by
  obtain ⟨U, _, _, _, π, hπ, u₀, _, C, _, _, _, _, _, _, _, _, f, ι,
    hf, hgal, hs, hG, _, _, _, _, _, hrot⟩ := mr_rootCover y₀ γ hγ
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, f, hG, hf, hs, hgal, hrot,
    b3_exists_intersectionForm (by simp), b6m_period_comparison C⟩

/-- Period comparisons, intersection forms and restricted operators are available
on every supplied compact analytic fibre, with no rational marking chosen.
Source: `b3_exists_intersectionForm`, `b6m_period_comparison`, `b63d_prymOperator_sq`. -/
theorem b64c_fibre_linear_inputs (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ (Q : (t : V) → LinearMap.BilinForm ℤ
        (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
      (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
        b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
      (A : (t : V) → b63l_parameterLattice b C hC V hV t →ₗ[ℤ]
        b63l_parameterLattice b C hC V hV t),
      (∀ t, b3_IsIntersectionForm ℂ (Q t)) ∧
      (∀ (t : V) (δ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
        P t (b6m_loopClass _ δ) = b3_latticePeriod ℂ _ δ) ∧
      (∀ t x, (A t x).val = b63d_operator b C hC V hV t x.val) ∧
      ∀ t x, A t (A t x) = (-3 : ℤ) • x := by
  classical
  have hq (t : V) := b3_exists_intersectionForm (C := b63l_parameterFibre b C V hV t)
    (E := ℂ) (by simp)
  choose Q hQ using hq
  choose P hP using fun t : V ↦ b6m_period_comparison (b63l_parameterFibre b C V hV t)
  choose A hA hsq using fun t : V ↦ b63d_prymOperator_sq b C hC V hV t (hG t)
  exact ⟨Q, fun t ↦ (P t).toLinearMap, A, hQ, hP, hA, hsq⟩

open Set Metric Manifold Topology HurwitzPrymRexPunct HurwitzPrymRexFill

attribute [local instance] b4b_group

/-- The constructive filling can use the standard complex coordinate on the sphere.
Source: `HurwitzPrymRexFill.exists_setup`, with the identity coordinate identification. -/
theorem b64c_standard_setup (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
theorem b64c_standard_value (j : Fin 13) (w : ℂ) :
    ξY (ContinuousLinearEquiv.refl ℂ ℂ) (b6_branch mr_base j) w =
      b6a_value mr_base j w := by
  fin_cases j <;>
    simp [ξY, b6_branch, Fin.append, Fin.addCases, b6a_value,
      b4cov_chartAt_coe, b4cov_chartAt_infty, b4cov_chart0_coe, b4cov_chart0_symm,
      b4cov_chartInf_apply, b4cov_chartInf_symm, b4cov_sphInv_infty]

/-- Ramification orders in the constructive filling.
Source: `HurwitzPrymRexPunct.Datum.e`. -/
def b64c_fillOrder (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ) → ℕ :=
  Sum.elim (fun _ ↦ 1) (fun c ↦ (S.D hπ c.1).e)

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) (u : U) :
    b64c_fillOrder U π S hπ (S.ι hπ (ContinuousLinearEquiv.refl ℂ ℂ) u) = 1 := rfl

local instance b64c_fillTop (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    TopologicalSpace (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instTopologicalSpaceCC hπ _

local instance b64c_fillChart (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ChartedSpace ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instChartedSpaceCC hπ _

local instance b64c_fillAction (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    MulAction b4b_Group (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) :=
  S.instMulActionCC hπ _

/-- The filling charts give the branch power formulas and the stabilizer rotations.
Source: `Setup.f_eq_on_pChart`, `Setup.smul_pChart_symm`. -/
theorem b64c_fill_local (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)}) (S : Setup ℂ π)
    (hκ : S.κ' = ContinuousLinearEquiv.refl ℂ ℂ)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    ∀ x (j : Fin 13), S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) x = b6_branch mr_base j →
      ∃ P : OpenPartialHomeomorph (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ (S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)) ∧ P x = 0 ∧
        (∀ y ∈ P.source, S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ) y =
          b6a_value mr_base j (P y ^ b64c_fillOrder U π S hπ x)) ∧
        ∀ g : MulAction.stabilizer b4b_Group x, ∃ ζ : ℂ,
          ζ ^ b64c_fillOrder U π S hπ x = 1 ∧
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
      rw [hκ, hx, b64c_standard_value] at hf
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

/-- The constructive filling supplies the total atlas and the analytic slice geometry.
Source: `b6a_analytic_atlas`, `b6a_fibre_geometry` and their atlas constructions. -/
theorem b64c_fill_totalSpace (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    [ConnectedSpace U]
    (π : U → {y : OnePoint ℂ // y ∉ Set.range (b6_branch mr_base)})
    (S : Setup ℂ π) (hκ : S.κ' = ContinuousLinearEquiv.refl ℂ ℂ)
    (hπ : IsQuotientCoveringMap π b4b_Group) :
    let C := S.CC hπ (ContinuousLinearEquiv.refl ℂ ℂ)
    ∃ (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C))
      (_ : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc mr_base × C)),
      (∀ q : b6t_polydisc mr_base × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ)
        (b6t_polydisc mr_base × C), q ∈ φ.source ∧
          ∀ y ∈ φ.source, (φ y).1 = y.1.val) ∧
      ∀ t : b6t_polydisc mr_base,
        ∃ (_ : ChartedSpace ℂ C) (_ : IsManifold 𝓘(ℂ, ℂ) ω C),
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
            (fun x : C ↦ b6a_map mr_base (S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ)) (t, x)) ∧
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (fun x : C ↦ (t, x)) ∧
          b4_IsGaloisCover b4b_Group
            (fun x : C ↦ b6a_map mr_base (S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ)) (t, x)) ∧
          Function.Surjective
            (fun x : C ↦ b6a_map mr_base (S.f hπ (ContinuousLinearEquiv.refl ℂ ℂ)) (t, x)) ∧
          ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x) := by
  classical
  dsimp only
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let : Nonempty U := ⟨S.u₀⟩
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  let n := b64c_fillOrder U π S hπ
  have hn : ∀ x, 0 < n x := by
    rintro (u | c)
    · exact Nat.zero_lt_one
    · exact (S.D hπ c.1).e_pos
  have hunram : ∀ x, f x ∉ Set.range (b6_branch mr_base) → n x = 1 := by
    rintro (u | c) hx
    · rfl
    · exact False.elim (hx c.1.property)
  have hlocal := b64c_fill_local U π S hκ hπ
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
  let : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc mr_base × C) := hm
  have hform := b6a_isolatedFamilyChart_formulas mr_base mr_base_mem_chart b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hAt : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) :=
    fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩
  have hfree : ∀ q, f q.2 ∉ Set.range (b6_branch mr_base) → n q.2 = 1 ∧
      ∀ y ∈ (A q).source, b6a_map mr_base f y = ((A q y).2 : OnePoint ℂ) :=
    fun q hq ↦ ⟨hunram q.2 hq, hform.2.1 q hq⟩
  refine ⟨cs, hm, (fun q ↦ ⟨A q, (hAt q).2, (hAt q).1, hform.1 q⟩), ?_⟩
  intro t
  obtain ⟨cs', hm', hk, hi, hg, hsurj, ha, -⟩ := b6a_fibre_geometry mr_base b4b_Group U C
    π f ι mr_base_mem_chart hπ hf hgal hs hG hι hrange hproj hequiv n hn hunram hlocal
    A hAt hform.1 (fun q hq ↦ (hfree q hq).2) hform.2.2 t
  exact ⟨cs', hm', hk, hi, hg, hsurj, ha⟩

/-- The peripheral monodromy identifies the root rotations on any holomorphic filling.
Source: `mr_loops_positive`, covering path lifting. -/
theorem b64c_cover_roots (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
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

/-- A homeomorphism transports analytic charts to the fixed topological fibre.
Source: Mathlib `Homeomorph.transOpenPartialHomeomorph`, `isManifold_of_contDiffOn`. -/
theorem b64c_pullback_charts (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
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
Source: `IsQuotientCoveringMap.disjoint`, equivariance of the filling inclusion. -/
theorem b64c_filling_stabilizers (t : Fin 10 → ℂ) (U C : Type)
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

/-- Root rotations and freeness away from the marked points identify the branch set.
Source: `b4_ramIndex_galois`, `b63_root_order`. -/
theorem b64c_root_branchSet (t : Fin 10 → ℂ) (C : Type)
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

/-- The actual fibre over the full marked-root polydisc.
Source: `b63l_parameterFibre`. -/
abbrev b64c_rootFibre (C : Type) [TopologicalSpace C] (t : b6t_polydisc mr_base) :=
  b63l_parameterFibre mr_base C (b6t_polydisc mr_base) (Set.Subset.refl _) t

example (C : Type) [TopologicalSpace C] (t : b6t_polydisc mr_base) :
    b64c_rootFibre C t ≃ₜ C := b6m_coordinate mr_base C t

/-- Geometric and integral input data on the marked-root polydisc.
Source: `mr_rootCover`, B6-2, `b3_exists_intersectionForm`, `b6m_period_comparison`.
The rational marking and its two identities are supplied separately. -/
structure b64c_RootFamily where
  C : Type
  [topC : TopologicalSpace C]
  [chartC : ChartedSpace ℂ C]
  [manC : IsManifold 𝓘(ℂ, ℂ) ω C]
  [t2C : T2Space C]
  [compactC : CompactSpace C]
  [connectedC : ConnectedSpace C]
  [actionC : MulAction b4b_Group C]
  hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)
  f : C → OnePoint ℂ
  hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f
  hs : Function.Surjective f
  [totalChart : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C)]
  [totalMan : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc mr_base × C)]
  hAt : ∀ q : b6t_polydisc mr_base × C,
    ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C), q ∈ φ.source ∧
      ∀ y ∈ φ.source, (φ y).1 = y.1.val
  [fibreChart : ∀ t, ChartedSpace ℂ (b64c_rootFibre C t)]
  [fibreMan : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (b64c_rootFibre C t)]
  [fibreT2 : ∀ t, T2Space (b64c_rootFibre C t)]
  [fibreCompact : ∀ t, CompactSpace (b64c_rootFibre C t)]
  [fibreConnected : ∀ t, ConnectedSpace (b64c_rootFibre C t)]
  [fibreFaithful : ∀ t, FaithfulSMul b4b_Group (b64c_rootFibre C t)]
  hincl : ∀ t, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
    (fun x : b64c_rootFibre C t ↦ x.val)
  hG : ∀ t (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (fun x : b64c_rootFibre C t ↦ g • x)
  hk : ∀ t, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t)
  hsurj : ∀ t, Function.Surjective
    (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t)
  hgal : ∀ t, b4_IsGaloisCover b4b_Group
    (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t)
  hbranch : ∀ t, b4_branchSet ℂ ℂ
    (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t) =
      Set.range (b6_branch t.val)
  hrot : ∀ t (j : Fin 13), ∃ x : b64c_rootFibre C t,
    b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t x =
      b6_branch t.val j ∧ b4_IsRotGen ℂ x (b4b_root j)
  Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)
  hQ₀ : b3_IsIntersectionForm ℂ Q₀
  Q : (t : b6t_polydisc mr_base) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b64c_rootFibre C t))
  hQ : ∀ t, b3_IsIntersectionForm ℂ (Q t)
  P : (t : b6t_polydisc mr_base) → b6m_H1 (b64c_rootFibre C t) →ₗ[ℤ]
    b3_periodLattice ℂ (b64c_rootFibre C t)
  hP : ∀ t (δ : b3_SmoothLoop ℂ (b64c_rootFibre C t)),
    P t (b6m_loopClass _ δ) = b3_latticePeriod ℂ _ δ
  A : (t : b6t_polydisc mr_base) →
    b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t →ₗ[ℤ]
      b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t
  hA : ∀ t x, (A t x).val =
    b63d_operator mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t x.val

/-- The marked root covering supplies every geometric and integral family input.
Source: `mr_rootCover`, `b64c_fill_totalSpace`, `b64c_fibre_linear_inputs`.
The constructive filling is compared with the base filling retained by `mr_rootCover`. -/
theorem b64c_root_family (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) : Nonempty b64c_RootFamily := by
  classical
  obtain ⟨U, _, _, _, π, hπ, u₀, hmon, C₀, _, _, _, _, _, _, _, _, f₀, ι₀,
    hf₀, hgal₀, hs₀, hG₀, hi₀, hr₀, hp₀, he₀, -, -⟩ := mr_rootCover y₀ γ hγ
  obtain ⟨S, hκ⟩ := b64c_standard_setup U π u₀.val
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : TopologicalSpace C := b64c_fillTop U π S hπ
  let : ChartedSpace ℂ C := b64c_fillChart U π S hπ
  let : MulAction b4b_Group C := b64c_fillAction U π S hπ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  have hf := S.contMDiff_f hπ κ
  have hG₀' := S.contMDiff_smul hπ κ
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hG₀' g).continuous
  have hi := S.isOpenEmbedding_ι hπ κ
  have hr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ := by
    ext x
    rcases x with u | c
    · exact ⟨fun _ ↦ (π u).property, fun _ ↦ ⟨u, rfl⟩⟩
    · exact ⟨fun ⟨u, hu⟩ ↦ False.elim (Sum.inl_ne_inr hu),
        fun h ↦ False.elim (h c.1.property)⟩
  have hp : ∀ u, f (ι u) = π u := fun _ ↦ rfl
  have heq : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u := fun _ _ ↦ rfl
  have hgal₀' : b4_IsGaloisCover b4b_Group f :=
    ⟨S.f_smul hπ κ, fun _ _ h ↦ S.exists_smul_of_f_eq hπ κ h⟩
  have hs : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ Set.range (b6_branch mr_base)
    · exact ⟨S.ofP hπ κ ⟨⟨y, hy⟩, QuotientGroup.mk (1 : b4b_Group)⟩, rfl⟩
    · obtain ⟨u, hu⟩ := hπ.surjective ⟨y, hy⟩
      exact ⟨ι u, congrArg Subtype.val hu⟩
  obtain ⟨baseComparison, -, -, -, -, -, -⟩ := b6m_filling_unique mr_base mr_base_mem_chart
    b4b_Group U π hπ C C₀ f f₀ ι ι₀ hf hf₀ hi hi₀ hr hr₀ hp hp₀ heq he₀
    hC (fun g ↦ (hG₀ g).continuous)
  obtain ⟨totalChart, totalMan, hAt, slices⟩ := b64c_fill_totalSpace U π S hκ hπ
  let : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C) := totalChart
  let : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc mr_base × C) := totalMan
  choose sliceChart sliceMan hk hiSlice hg hsSlice ha using slices
  let e (t : b6t_polydisc mr_base) : b64c_rootFibre C t ≃ₜ C := b6m_coordinate mr_base C t
  have pulls (t : b6t_polydisc mr_base) :=
    @b64c_pullback_charts (b64c_rootFibre C t) C _ _ (sliceChart t) (sliceMan t) (e t)
  choose fibreChart fibreMan he heinv using pulls
  let : ∀ t, ChartedSpace ℂ (b64c_rootFibre C t) := fibreChart
  let : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (b64c_rootFibre C t) := fibreMan
  let : ∀ t, T2Space (b64c_rootFibre C t) := fun t ↦ (e t).symm.t2Space
  let : ∀ t, CompactSpace (b64c_rootFibre C t) := fun t ↦ (e t).symm.compactSpace
  let : ∀ t, ConnectedSpace (b64c_rootFibre C t) := fun t ↦
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
      (fun x : b64c_rootFibre C t ↦ x.val) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (hiSlice t).comp (he t) using 1
    funext x
    exact Prod.ext x.property rfl
  have hGF (t : b6t_polydisc mr_base) (g : b4b_Group) :
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b64c_rootFibre C t ↦ g • x) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (heinv t).comp ((ha t g).comp (he t)) using 1
    funext x
    rfl
  have hsF (t : b6t_polydisc mr_base) : Function.Surjective
      (b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t) := by
    rw [hprojection]
    exact (hsSlice t).comp (e t).surjective
  have heact (t : b6t_polydisc mr_base) (g : b4b_Group) (x : b64c_rootFibre C t) :
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
  let it (t : b6t_polydisc mr_base) : U → b64c_rootFibre C t := (e t).symm ∘ ι
  have hit (t : b6t_polydisc mr_base) : Topology.IsOpenEmbedding (it t) :=
    (e t).symm.isOpenEmbedding.comp hi
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
    rw [← hr]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, ((e t).apply_symm_apply _).symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, (e t).injective (by simpa using hu)⟩
  have stabilizers (t : b6t_polydisc mr_base) :
      FaithfulSMul b4b_Group (b64c_rootFibre C t) ∧
      ∀ x, b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t x ∉
        Set.range (b6_branch t.val) → MulAction.stabilizer b4b_Group x = ⊥ := by
    obtain ⟨et, -, -, -⟩ := mr_rootCover_family t.val t.property U π hπ y₀ u₀ γ hγ hmon
    exact b64c_filling_stabilizers t.val U (b64c_rootFibre C t) (et ∘ π)
      (hπ.homeomorph_comp et) u₀.val _ (it t) (hit t).injective (hrt t) (het t)
  have faithful (t : b6t_polydisc mr_base) := (stabilizers t).1
  let : ∀ t, FaithfulSMul b4b_Group (b64c_rootFibre C t) := faithful
  have hrotF (t : b6t_polydisc mr_base) : ∀ j, ∃ x : b64c_rootFibre C t,
      b63d_projection mr_base C f (b6t_polydisc mr_base) (Set.Subset.refl _) t x =
        b6_branch t.val j ∧ b4_IsRotGen ℂ x (b4b_root j) := by
    obtain ⟨et, hetp, -, hetloops⟩ := mr_rootCover_family t.val t.property U π hπ y₀ u₀ γ hγ hmon
    let πt := et ∘ π
    have hπt := hπ.homeomorph_comp et
    have hstab := (b64c_filling_stabilizers t.val U (b64c_rootFibre C t) πt hπt u₀.val
      _ (it t) (hit t).injective (hrt t) (het t)).2
    apply b64c_cover_roots t.val t.property (et y₀)
      (fun j ↦ FundamentalGroup.map ⟨et, et.continuous⟩ y₀ (γ j))
      (fun j ↦ (hetloops j).1) U πt hπt ⟨u₀.val, congrArg et u₀.property⟩
      (fun j ↦ (hetloops j).2) (b64c_rootFibre C t) _ (it t) (hGF t) (hkF t) (hgF t)
      (hit t).continuous _ (het t) hstab
    intro u
    change b6t_sphere mr_base t.val (f (ι u)) = et (π u)
    rw [hp, hetp]
  have hbranchF (t : b6t_polydisc mr_base) := b64c_root_branchSet t.val (b64c_rootFibre C t)
    (hGF t) _ (hkF t) (hgF t)
    (stabilizers t).2 (hrotF t)
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (by simp)
  obtain ⟨Q, P, A, hQ, hP, hA, -⟩ := b64c_fibre_linear_inputs mr_base C hC
    (b6t_polydisc mr_base) (Set.Subset.refl _) hGF
  exact ⟨{
    C := C
    hC := hC
    f := f
    hf := hf
    hs := hs
    hAt := hAt
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
    P := P
    hP := hP
    A := A
    hA := hA }⟩

/-- The explicit peripheral loops give a family without any loop-existence assumption.
Source: `mr_curve_avoids`, `mr_loop_existsUnique`, `b64c_root_family`. -/
theorem b64c_root_family_nonempty : Nonempty b64c_RootFamily := by
  classical
  have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    simp [mr_curve, mr_outer, mr_basePoint]
  have hmem : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    have h := (mr_curve_avoids mr_base b64c_root_domain.1 12 0).1
    rw [h0] at h
    exact h
  let y₀ : b6t_punctured mr_base := ⟨_, hmem⟩
  let γ := fun i ↦ (mr_loop_existsUnique mr_base b64c_root_domain.1 y₀ rfl i).exists.choose
  exact b64c_root_family y₀ γ
    (fun i ↦ (mr_loop_existsUnique mr_base b64c_root_domain.1 y₀ rfl i).exists.choose_spec)

attribute [local instance] b64c_RootFamily.topC b64c_RootFamily.chartC b64c_RootFamily.manC
  b64c_RootFamily.t2C b64c_RootFamily.compactC b64c_RootFamily.connectedC
  b64c_RootFamily.actionC b64c_RootFamily.totalChart b64c_RootFamily.totalMan
  b64c_RootFamily.fibreChart b64c_RootFamily.fibreMan b64c_RootFamily.fibreT2
  b64c_RootFamily.fibreCompact b64c_RootFamily.fibreConnected b64c_RootFamily.fibreFaithful

/-- Every input of statement 5 is supplied by the marked root family. -/
example (D : b64c_RootFamily) (s t : b6t_polydisc mr_base) :
    Module.finrank ℂ (b63e_transportedF mr_base D.C D.hC (b6t_polydisc mr_base)
      (Set.Subset.refl _) D.P s t) = 6 :=
  b64c_transported_finrank mr_base D.C D.hC (b6t_polydisc mr_base) (Set.Subset.refl _)
    D.hG mr_base_mem_chart D.f D.hk D.hsurj D.hgal D.hbranch D.hrot D.P D.hP s t

/-- Every input of statement 6, including the operator identity, is supplied. -/
example (D : b64c_RootFamily) (s t : b6t_polydisc mr_base) :
    Module.finrank ℂ ↥(b63e_transportedF mr_base D.C D.hC (b6t_polydisc mr_base)
        (Set.Subset.refl _) D.P s t ⊓ Module.End.eigenspace ((D.A s).baseChange ℂ)
          (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF mr_base D.C D.hC (b6t_polydisc mr_base)
        (Set.Subset.refl _) D.P s t ⊓ Module.End.eigenspace ((D.A s).baseChange ℂ)
          (Complex.I * (Real.sqrt 3 : ℂ))) = 3 :=
  b64c_transported_eigen_ranks mr_base D.C D.hC (b6t_polydisc mr_base) (Set.Subset.refl _)
    D.hG mr_base_mem_chart D.f D.hk D.hsurj D.hgal D.hbranch D.hrot D.P D.hP s (D.A s) (D.hA s) t

/-- Statement 7 and the frame-premise form of statement 8 take only the polarized rational
marking, an integral basis `B` and the local analytic frames `hframe` (the shape of the set-aside
`b63e_filtration_frame`) in addition to the constructed geometric inputs. -/
example (D : b64c_RootFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Set.Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Set.Subset.refl _)
        s (D.P s) (D.Q s)).baseChange ℚ x y)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Set.Subset.refl _) s))
    (hframe : ∀ t₀ ∈ b6t_polydisc mr_base, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      W ⊆ b6t_polydisc mr_base ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → Fin 12 → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) =
          b64c_transportedFamily mr_base D.C D.hC (b6t_polydisc mr_base) (Set.Subset.refl _)
            D.P s t) :
    AnalyticOnNhd ℂ (b64c_geomPeriod mr_base D.C D.hC (b6t_polydisc mr_base)
      (Set.Subset.refl _) D.P s m) (b6t_polydisc mr_base) ∧
      ∀ t ∈ b6t_polydisc mr_base,
        b64c_geomPeriod mr_base D.C D.hC (b6t_polydisc mr_base) (Set.Subset.refl _) D.P s m t ∈
          HodgeLean.Papers.g32m_Domain ∧
        b60_F (b64c_geomPeriod mr_base D.C D.hC (b6t_polydisc mr_base)
          (Set.Subset.refl _) D.P s m t) =
          b64c_markedF _ m (b64c_transportedFamily mr_base D.C D.hC (b6t_polydisc mr_base)
            (Set.Subset.refl _) D.P s) t := by
  constructor
  · exact b64c_geomPeriod_analytic_of_frames mr_base D.C D.hC (b6t_polydisc mr_base)
      (Set.Subset.refl _) b64c_root_domain.2.2.1 D.hG mr_base_mem_chart D.f D.hf D.hs
      D.hk D.hsurj D.hgal D.hbranch D.hrot D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP s
      (D.A s) (D.hA s) m hJ hpol B hframe
  · exact b64c_geomPeriod_chart mr_base D.C D.hC (b6t_polydisc mr_base) (Set.Subset.refl _)
      D.hG mr_base_mem_chart D.f D.hf D.hs D.hk D.hsurj D.hgal D.hbranch D.hrot
      D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP s (D.A s) (D.hA s) m hJ hpol

#print axioms b64c_root_family
#print axioms b64c_root_family_nonempty

end HodgeLean.Foundations.Program
