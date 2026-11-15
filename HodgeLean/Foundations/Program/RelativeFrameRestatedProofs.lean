import HodgeLean.Foundations.Program.RelativeFrameRestatedDefs
import HodgeLean.Foundations.Program.PrymVariationFrames
import HodgeLean.Foundations.Program.RelativeFrameCharts

noncomputable section
open Set Manifold
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option maxHeartbeats 400000 in
theorem rf6_relForm_frame_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (t₀ : V) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))) →
          b63e_relForm b C V hV W,
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt b C V hV (θ i) t) = ⊤ := by
  classical
  let _ : ∀ t : V, FiniteDimensional ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t)) :=
    fun t ↦ b3_holForm_finiteDimensional (show Module.finrank ℂ ℂ = 1 by simp)
  let β := Module.finBasis ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))
  choose U hU htU hUV θ hθ using fun i ↦ rf5_relForm_extend hVo hincl F t₀ (β i)
  let W := V ∩ ⋂ i, U i
  have hW : IsOpen W := hVo.inter (isOpen_iInter_of_finite hU)
  have htW : t₀.val ∈ W := ⟨t₀.property, Set.mem_iInter.mpr htU⟩
  have hWi i : W ⊆ U i := fun u hu ↦ Set.mem_iInter.mp hu.2 i
  let θW i : b63e_relForm b C V hV W :=
    ⟨(θ i).val, b63e_relForm_mono b C V hV (hWi i) (θ i).property⟩
  have hβ : (fun i ↦ b63e_relFormAt b C V hV (θW i) t₀) = β := funext hθ
  have hli : LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θW i) t₀) := by
    rw [hβ]
    exact β.linearIndependent
  obtain ⟨W', hW', ht', hsub, hind⟩ :=
    b63e_relForm_independent_near b C V hV hVo hA hincl t₀ W hW htW θW hli
  let θ' i : b63e_relForm b C V hV W' :=
    ⟨(θW i).val, b63e_relForm_mono b C V hV (fun u hu ↦ (hsub hu).2) (θW i).property⟩
  refine ⟨W', hW', ht', fun u hu ↦ (hsub hu).1, θ', ?_⟩
  intro t ht
  have hi := hind t ht
  refine ⟨hi, hi.span_eq_top_of_card_eq_finrank' ?_⟩
  rw [Fintype.card_fin]
  exact b63e_holForm_finrank_homeomorph _ _
    (b6m_transport b C ⟨t₀.val, hV t₀.property⟩ ⟨t.val, hV t.property⟩)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem rf6_filtration_frame_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    (t₀ : V) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ c : Fin (Module.finrank ℂ (b63e_transportedF b C hC V hV P s t₀)) →
          (Fin 10 → ℂ) → (ι → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_coordVector B (c i t.val)) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) =
            b63e_transportedF b C hC V hV P s t := by
  classical
  let L := b63l_parameterLattice b C hC V hV s
  have key : ∀ {n : ℕ} (B' : Module.Basis (Fin n) ℤ L),
      ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
        ∃ c : Fin (Module.finrank ℂ (b63e_transportedF b C hC V hV P s t₀)) →
            (Fin 10 → ℂ) → (Fin n → ℂ),
          (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
          ∀ t : V, t.val ∈ W →
            LinearIndependent ℂ (fun i ↦ b63e_coordVector B' (c i t.val)) ∧
            Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B' (c i t.val)) =
              b63e_transportedF b C hC V hV P s t := by
    intro n B'
    let _ : Module.Free ℤ L := Module.Free.of_basis B'
    let _ : Module.Finite ℤ L := Module.Finite.of_basis B'
    let Fs := b63e_transportedF b C hC V hV P s
    let e : (Fin n → ℂ) ≃ₗ[ℂ] (ℂ ⊗[ℤ] L) := (B'.baseChange ℂ).equivFun.symm
    have hw (t : V) : b2_IsWeightOne L (Fs t) := by
      obtain ⟨E, _, hF⟩ := b63e_lattice_period_transport b C hC V hV hG P hP s t
      rw [show Fs t = _ from hF]
      exact b63e_weightOne_comap E _
        (b63l_image_riemann (b63l_parameterFibre b C V hV t) (hG t) (Q t) (hQ t)).2.1
    have hd (t : V) : Module.finrank ℂ (Fs t) = Module.finrank ℂ (Fs t₀) := by
      have h := Submodule.finrank_add_eq_of_isCompl (hw t)
      have h₀ := Submodule.finrank_add_eq_of_isCompl (hw t₀)
      rw [b2a_finrank_conjSubmodule] at h h₀
      omega
    obtain ⟨W, hW, ht₀, hWV, θ, hθ⟩ := rf6_relForm_frame_aux b C V hV hVo hA hincl F t₀
    let N : (Fin 10 → ℂ) → Matrix
        (Fin (Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))))
        (Fin n) ℂ := fun u i j ↦ b63e_periodFunction b C V hV P (θ i) s (B' j).val u
    have hN i j : AnalyticOnNhd ℂ (fun u ↦ N u i j) W :=
      (b63e_period_analytic b C V hV hVo hA hincl P hP W hW (θ i) s (B' j).val).mono
        (fun _ hu ↦ ⟨hWV hu, hu⟩)
    have hk (t : V) (ht : t.val ∈ W) :
        (Fs t).comap e.toLinearMap = LinearMap.ker (N t.val).mulVecLin := by
      have hNt : N t.val = fun i j ↦
          (b63e_transportMap b C hC V hV P s t (B' j)).val
            (b63e_relFormAt b C V hV (θ i) t) := by
        funext i j
        dsimp [N, b63e_periodFunction]
        rw [dite_eq_left t.property]
        rfl
      rw [hNt]
      ext c
      change (B'.baseChange ℂ).equivFun.symm c ∈ Fs t ↔ _
      rw [← b63e_coordVector_equiv]
      exact b63e_period_matrix_kernel (b63l_parameterFibre b C V hV t) B'
        (b63e_transportMap b C hC V hV P s t)
        (fun i ↦ b63e_relFormAt b C V hV (θ i) t) (hθ t ht).2 c
    have hn u (hu : u ∈ W) :
        Module.finrank ℂ (LinearMap.ker (N u).mulVecLin) = Module.finrank ℂ (Fs t₀) := by
      rw [← hk ⟨u, hWV hu⟩ hu]
      rw [← Submodule.map_equiv_eq_comap_symm]
      rw [LinearEquiv.finrank_map_eq]
      exact hd ⟨u, hWV hu⟩
    obtain ⟨W', hW', ht', hsub, c, hc, hspan⟩ :=
      b63e_kernel_frame_of_nullity W hW N hN hn t₀.val ht₀
    refine ⟨W', hW', ht', hsub.trans hWV, c, hc, ?_⟩
    intro t ht
    obtain ⟨hli, hsp⟩ := hspan t.val ht
    simp_rw [b63e_coordVector_equiv]
    refine ⟨hli.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective), ?_⟩
    change Submodule.span ℂ (Set.range (e.toLinearMap ∘ (fun i ↦ c i t.val))) = Fs t
    rw [Set.range_comp, ← Submodule.map_span, hsp, ← hk t (hsub ht)]
    exact Submodule.map_comap_eq_of_surjective e.surjective _
  let e := Fintype.equivFin ι
  obtain ⟨W, hW, ht, hWV, c, hc, hspan⟩ := key (B.reindex e)
  refine ⟨W, hW, ht, hWV, (fun i u j ↦ c i u (e j)), ?_, ?_⟩
  · intro i u hu
    exact AnalyticAt.pi fun j ↦ (analyticAt_pi_iff.mp (hc i u hu)) (e j)
  · intro t ht
    have heq (i) : b63e_coordVector B (fun j ↦ c i t.val (e j)) =
        b63e_coordVector (B.reindex e) (c i t.val) :=
      (b63e_coordVector_reindex B e (c i t.val)).symm
    simp_rw [heq]
    exact hspan t ht

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem rf6_polarized_variation_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s)) :
    b2_IsPolarizedTorusFamily (Fin 10 → ℂ) (b63e_localSystem b C hC V hV hVo s B)
      (fun t ↦ b63e_transportedF b C hC V hV P s ⟨t.val, t.property⟩)
      (fun _ ↦ b63e_singularQ b C hC V hV s (P s) (Q s)) := by
  let _ : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
  let _ : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
  refine ⟨?_, fun _ _ _ _ _ ↦ rfl, ?_, ?_⟩
  · apply b63e_const_subbundle_of_frames (⟨V, hVo⟩ : TopologicalSpace.Opens (Fin 10 → ℂ)) B
    intro t₀
    obtain ⟨W, hW, ht, _, c, hc, hspan⟩ :=
      rf6_filtration_frame_aux b C hC V hV hVo hA hincl hG Q hQ P hP F s B t₀
    exact ⟨W, hW, ht, _, c, hc, fun t ht ↦ (hspan t ht).2⟩
  · intro t
    exact (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).1
  · intro t
    exact (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).2

end HodgeLean.Foundations.Program
