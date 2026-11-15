import HodgeLean.Foundations.Program.RelativeFrameAssemblyProofs

/-! # Assembly of the marked-root relative frame datum
Implications from the retained geometric construction to plumbing, D2, D3 and D4.
The rational marking H7 and the rational variation packaging are separate inputs downstream.
HC no distance; AV milestone no distance.
-/
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

/-- One construction retains the filling, atlas and transported fibre structures together.
Source: `PeriodFunctionChecks.lean` on `origin/main`, lines 508–685, with the retained atlas
of `b6a_isolatedFamilyChart`; `docs/specs/RelativeFrameFamily.md`, review item 10a. -/
theorem rf8_shared_root  :
    ∃ R : rf8_SharedFamily,
      ∃ (y₀ : b6t_punctured mr_base)
        (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
        (u₀ : R.atlas.π ⁻¹' {y₀}),
        (∀ i, mr_IsLoop mr_base y₀ i (γ i)) ∧
        ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (γ i) =
          MulOpposite.op (b4b_root i) :=
  rf8_shared_root_aux 

example := @rf8_shared_root

/-- On a connected annulus two nonvanishing roots differ by one constant root of unity.
The formulation applies to its subtype, with `u` the annulus chart and `v` the base moving root.
Source: Forster, *Lectures on Riemann Surfaces*, §4 (uniqueness of lifts);
`docs/specs/RelativeFrameFamily.md`, review item 10b. -/
theorem rf8_root_alignment {Y : Type} [TopologicalSpace Y] [ConnectedSpace Y]
    (n : ℕ) (hn : 0 < n) (u v : Y → ℂ) (hu : Continuous u) (hv : Continuous v)
    (hzero : ∀ y, v y ≠ 0) (hpow : ∀ y, u y ^ n = v y ^ n) :
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ ∀ y, u y = ζ * v y :=
  rf8_root_alignment_aux n hn u v hu hv hzero hpow

example := @rf8_root_alignment

/-- Rotation by an nth root of unity commutes with the principal-root formula.
Source: `rf4_rootMap`; `docs/specs/RelativeFrameFamily.md`, review item 10b. -/
theorem rf8_principal_equivariance (n : ℕ) (hn : 0 < n) (ζ ε u : ℂ)
    (hζ : ζ ^ n = 1) :
    rf4_rootMap n ε (ζ * u) = ζ * rf4_rootMap n ε u :=
  rf8_principal_equivariance_aux n hn ζ ε u hζ

example := @rf8_principal_equivariance

/-- The aligned moving roots yield the fibre and total plumbing data on the retained structures.
The coordinate inverse is the `h_eq` field of `F`; its chart restrictions are `w_source`, `w_eq`.
Source: `rf7_moving_root`, `rf7_pieces`, `rf7_outer_data`;
`docs/specs/RelativeFrameFamily.md`, review items 10b–10c. -/
theorem rf8_family_plumbing (R : rf8_SharedFamily) :
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
          rf7_component R.atlas.f (mr_base (idx k)) (3 * b6t_radius mr_base) (e k).val} :=
  rf8_family_plumbing_aux R

example := @rf8_family_plumbing

/-- D2 for the retained marked-root family.
Source: `rf6_relForm_frame`; `docs/specs/RelativeFrameFamily.md`, review item 10d. -/
theorem rf8_root_relForm_frame (R : rf8_SharedFamily)
    (t₀ : b6t_polydisc mr_base) :
        ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc mr_base ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t₀))) →
          b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) W,
        ∀ t : b6t_polydisc mr_base, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) (θ i) t) = ⊤ :=
  rf8_root_relForm_frame_aux R t₀

example := @rf8_root_relForm_frame

/-- D3 for the retained marked-root family, in a rank-twelve integral basis.
Source: `rf6_filtration_frame`; `docs/specs/RelativeFrameFamily.md`, review item 10d. -/
theorem rf8_root_filtration_frame (R : rf8_SharedFamily)
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
            b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t :=
  rf8_root_filtration_frame_aux R s B t₀

example := @rf8_root_filtration_frame

/-- D4 for the retained marked-root family and the same intersection pairing.
Source: `rf6_polarized_variation`; `docs/specs/RelativeFrameFamily.md`, review item 10d. -/
theorem rf8_root_polarized_variation (R : rf8_SharedFamily)
    (s : b6t_polydisc mr_base)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)) :
        b2_IsPolarizedTorusFamily (Fin 10 → ℂ) (b63e_localSystem mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1 s B)
      (fun t ↦ b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s ⟨t.val, t.property⟩)
      (fun _ ↦ b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s (R.P s) (R.Q s)) :=
  rf8_root_polarized_variation_aux R s B

example := @rf8_root_polarized_variation

/-! ## Checks on geometric inputs and positive ranks -/

/-- A degree-two pair of nonzero roots with nontrivial discrepancy and a nonconstant root.
No statement of this file is used for this check. -/
example : Continuous (fun z : ℂ ↦ -Complex.exp z) ∧ Continuous Complex.exp ∧
    (∀ z : ℂ, Complex.exp z ≠ 0) ∧
    (∀ z : ℂ, (-Complex.exp z) ^ 2 = (Complex.exp z) ^ 2) ∧
    (-Complex.exp 0 ≠ Complex.exp 0) ∧ (-1 : ℂ) ^ 2 = 1 ∧ (2 : ℕ) > 1 := by
  refine ⟨Complex.continuous_exp.neg, Complex.continuous_exp,
    Complex.exp_ne_zero, fun z ↦ by ring, ?_, by norm_num, by norm_num⟩
  simp only [Complex.exp_zero]
  norm_num

/-- Checked marked-cover inputs with a faithful action and a nonidentity rotation.
The loops and compact filling come from the existing marked-cover construction. -/
example : ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
      (f : C → OnePoint ℂ),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ Function.Surjective f ∧
      b4_IsGaloisCover b4b_Group f ∧
      (∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j)) ∧
      b4b_root 0 ≠ 1 := by
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
  obtain ⟨U, _, _, _, π, hπ, u₀, hmon, C, _, _, _, _, _, _, _, _, f, ι,
    hf, hgal, hs, hG, hi, hr, hp, he, hstab, hrot⟩ :=
    mr_rootCover y₀ (fun i ↦ (hl i).choose) (fun i ↦ (hl i).choose_spec)
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, f, hf, hs, hgal, hrot, ?_⟩
  intro h
  have ho := b63_root_order (0 : Fin 13)
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- The marked polydisc contains a genuinely displaced moving branch value. -/
example : ∃ t ∈ b6t_polydisc mr_base, t 0 - mr_base 0 ≠ 0 ∧
    ‖t 0 - mr_base 0‖ < rf7_radius mr_base := by
  have hr : 0 < b6t_radius mr_base := (b6t_discs mr_base mr_base_mem_chart).1
  refine ⟨Function.update mr_base 0 (mr_base 0 + (b6t_radius mr_base / 2 : ℝ)), ?_, ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    by_cases h : i = 0
    · subst h
      simp only [Function.update_self, dist_self_add_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2)]
      linarith
    · simp [Function.update_of_ne h, hr]
  · simp only [Function.update_self, add_sub_cancel_left]
    exact_mod_cast (by positivity : (b6t_radius mr_base / 2 : ℝ) ≠ 0)
  · simp only [Function.update_self, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2), rf7_radius]
    linarith

/-- Every retained fibre has a rank-twelve lattice; no open statement is used here. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    Nonempty (Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)) :=
  (b63d_lattice_rank mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s
    (R.hG s) mr_base_mem_chart R.atlas.f (R.hk s) (R.hsurj s) (R.hgal s)
    (R.hbranch s) (R.hrot s)).1

/-- Filtration rank six on the retained structures, using the checked period transport.
This specializes the proof of `b64c_transported_finrank` on `origin/main` to this datum. -/
example (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) :
    Module.finrank ℂ (b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.P s t) = 6 := by
  obtain ⟨E, -, hE⟩ := b63e_lattice_period_transport mr_base R.C R.hC
    (b6t_polydisc mr_base) (Subset.refl _) R.hG R.P R.hP s t
  have hd := (b63d_dim_eq mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
    t (R.hG t) mr_base_mem_chart R.atlas.f (R.hk t) (R.hsurj t) (R.hgal t)
    (R.hbranch t) (R.hrot t)).2.2
  let eC := E.baseChange ℤ ℂ
    (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)
    (b63l_periodLattice (rf8_fibre R.C t))
  rw [hE]
  change Module.finrank ℂ ↥((b63l_periodF _).comap eC.toLinearMap) = 6
  exact (Submodule.comap_equiv_self_of_inj_of_le (p := b63l_periodF _)
    eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq.trans hd

/-- Chain to the exact local-frame premise used by `b64c_geomPeriod_analytic_of_frames`.
Only this chain check uses a statement of this draft. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)) :
    ∀ t₀ ∈ b6t_polydisc mr_base,
      ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ b6t_polydisc mr_base ∧
        ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → Fin 12 → ℂ,
          (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
          ∀ t ∈ W, Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t)) =
            rf8_transportedFamily R s t := by
  intro t₀ ht₀
  obtain ⟨W, hWo, htW, hWV, c, hc, hspan⟩ :=
    rf8_root_filtration_frame R s B ⟨t₀, ht₀⟩
  refine ⟨W, hWo, htW, hWV, _, c, hc, ?_⟩
  intro t ht
  simpa only [rf8_transportedFamily, dite_eq_left (hWV ht)] using (hspan ⟨t, hWV ht⟩ ht).2

end HodgeLean.Foundations.Program
