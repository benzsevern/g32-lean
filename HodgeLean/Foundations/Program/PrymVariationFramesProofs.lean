import HodgeLean.Foundations.Program.PrymVariationFramesDefs
import HodgeLean.Foundations.Program.PrymVariationFramesKernel
import HodgeLean.Foundations.Program.PrymVariationFramesTransport
import HodgeLean.Foundations.Program.PrymVariationFramesHolomorphic
import HodgeLean.Foundations.Program.PrymVariationFramesPeriodMatrix
import HodgeLean.Foundations.Program.PrymVariationFramesRelative

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63e_analytic_kernel_frame_aux {k m n r : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin m) (Fin n) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun u ↦ M u i j) W)
    (hr : ∀ u ∈ W, (M u).rank = r) (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ u₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ c : Fin (n - r) → (Fin k → ℂ) → (Fin n → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W') ∧
        ∀ u ∈ W', LinearIndependent ℂ (fun i ↦ c i u) ∧
          Submodule.span ℂ (Set.range fun i ↦ c i u) = LinearMap.ker (M u).mulVecLin := by
  exact b63e_kernel_frame W hW M hM hr u₀ hu₀

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem b63e_period_analytic_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (θ : b63e_relForm b C V hV U) (s : V)
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ s x) (V ∩ U) := by
  exact b63e_period_analytic_of_loops b C V hV P θ s
    (fun γ ↦ b63e_loop_period_analytic b C V hV hVo hA hincl P hP U hU θ s γ) x

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b63e_lattice_period_transport_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    ∃ E : b63l_parameterLattice b C hC V hV s ≃ₗ[ℤ]
        b63l_periodLattice (b63l_parameterFibre b C V hV t),
      (∀ x, (E x).val = b63e_transportMap b C hC V hV P s t x) ∧
      b63e_transportedF b C hC V hV P s t =
        (b63l_periodF (b63l_parameterFibre b C V hV t)).comap
          ((E : b63l_parameterLattice b C hC V hV s →ₗ[ℤ]
            b63l_periodLattice (b63l_parameterFibre b C V hV t)).baseChange ℂ) := by
  obtain ⟨T, hT, _⟩ := (b63l_fibre_image_transport b C hC
    ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩).2
  obtain ⟨P', hP', _, E, hE⟩ :=
    b63l_period_image_comparison (b63l_parameterFibre b C V hV t) (hG t)
  have hPeq : P'.toLinearMap = P t :=
    b6m_homology_linearMap_ext _ _ _ _ (fun γ ↦ (hP' γ).trans (hP t γ).symm)
  let E' : b63l_parameterLattice b C hC V hV s ≃ₗ[ℤ]
      b63l_periodLattice (b63l_parameterFibre b C V hV t) := T.trans E
  have hval : ∀ x, (E' x).val = b63e_transportMap b C hC V hV P s t x := by
    intro x
    change (E (T x)).val = _
    rw [hE]
    change P'.toLinearMap (T x).val = _
    rw [hPeq, hT]
    rfl
  refine ⟨E', hval, ?_⟩
  have hm : (b63l_periodLattice (b63l_parameterFibre b C V hV t)).subtype.comp
      E'.toLinearMap = b63e_transportMap b C hC V hV P s t := by
    apply LinearMap.ext
    intro x
    exact hval x
  unfold b63e_transportedF b63l_periodF
  rw [← Submodule.comap_comp, ← LinearMap.baseChange_comp, hm]


set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b63e_pairing_constant_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
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
    (s t : V) (x y : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    Q t (P t (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x))
        (P t (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) y)) =
      Q s (P s x) (P s y) := by
  obtain ⟨P₀, hP₀⟩ := b6m_period_comparison C
  have hbase (u : V) (a d : b6m_H1 C) :
      Q u (P u ((b6m_H1Equiv (b6m_coordinate b C ⟨u.val, hV u.property⟩)).symm a))
        (P u ((b6m_H1Equiv (b6m_coordinate b C ⟨u.val, hV u.property⟩)).symm d)) =
        Q₀ (P₀ a) (P₀ d) := by
    obtain ⟨R, S, hR, hS, hRS⟩ := b6m_intersection_transport b hb u.val (hV u.property)
      C (b63l_parameterFibre b C V hV u) f (b63d_projection b C f V hV u)
      hf (hk u) hs (b6m_coordinate b C ⟨u.val, hV u.property⟩).symm
      (fun _ ↦ rfl) Q₀ hQ₀ (Q u) (hQ u)
    have heR : R.toLinearMap = P₀.toLinearMap :=
      b6m_homology_linearMap_ext _ _ _ _ (fun γ ↦ (hR γ).trans (hP₀ γ).symm)
    have heS : S.toLinearMap = P u :=
      b6m_homology_linearMap_ext _ _ _ _ (fun γ ↦ (hS γ).trans (hP u γ).symm)
    have h := hRS a d
    change Q u (S.toLinearMap _) (S.toLinearMap _) = Q₀ (R.toLinearMap a) (R.toLinearMap d) at h
    rw [heR, heS, ← b6m_H1Equiv_symm_aux] at h
    exact h
  rw [b6m_transport, ← b6m_H1Equiv_trans_aux, ← b6m_H1Equiv_symm_aux]
  change Q t (P t ((b6m_H1Equiv (b6m_coordinate b C ⟨t.val, hV t.property⟩)).symm
      (b6m_H1Equiv (b6m_coordinate b C ⟨s.val, hV s.property⟩) x)))
    (P t ((b6m_H1Equiv (b6m_coordinate b C ⟨t.val, hV t.property⟩)).symm
      (b6m_H1Equiv (b6m_coordinate b C ⟨s.val, hV s.property⟩) y))) = _
  rw [hbase]
  symm
  simpa only [LinearEquiv.symm_apply_apply] using hbase s
    (b6m_H1Equiv (b6m_coordinate b C ⟨s.val, hV s.property⟩) x)
    (b6m_H1Equiv (b6m_coordinate b C ⟨s.val, hV s.property⟩) y)


set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b63e_weight_one_riemann_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
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
    (s t : V) :
    b2_IsWeightOne (b63l_parameterLattice b C hC V hV s)
        (b63e_transportedF b C hC V hV P s t) ∧
      b2_IsRiemannForm (b63l_parameterLattice b C hC V hV s)
        (b63e_transportedF b C hC V hV P s t) (b63e_singularQ b C hC V hV s (P s) (Q s)) := by
  obtain ⟨E, hE, hF⟩ := b63e_lattice_period_transport_aux b C hC V hV hG P hP s t
  obtain ⟨_, hw, hR⟩ := b63l_image_riemann
    (b63l_parameterFibre b C V hV t) (hG t) (Q t) (hQ t)
  have hform : b63e_singularQ b C hC V hV s (P s) (Q s) =
      (b63l_periodQ (b63l_parameterFibre b C V hV t) (Q t)).compl₁₂
        E.toLinearMap E.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q s (P s x.val) (P s y.val) = Q t (E x).val (E y).val
    rw [hE x, hE y]
    exact (b63e_pairing_constant_aux b C V hV hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t
      x.val y.val).symm
  rw [hF, hform]
  exact ⟨b63e_weightOne_comap E _ hw, b63e_riemann_comap E _ _ hR⟩


end HodgeLean.Foundations.Program
