import HodgeLean.Foundations.Program.PrymVariationFramesDefs
import HodgeLean.Foundations.Program.PrymVariationFramesPeriods

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b63e_holForm_finrank_homeomorph (C D : Type)
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] (e : C ≃ₜ D) :
    Module.finrank ℂ (b3_HolForm ℂ C) = Module.finrank ℂ (b3_HolForm ℂ D) := by
  obtain ⟨P, _⟩ := b6m_period_comparison C
  obtain ⟨Q, _⟩ := b6m_period_comparison D
  have h := (P.symm.trans ((b6m_H1Equiv e).trans Q)).finrank_eq
  rw [b3_finrank_periodLattice (show Module.finrank ℂ ℂ = 1 by simp),
    b3_finrank_periodLattice (show Module.finrank ℂ ℂ = 1 by simp)] at h
  omega

set_option backward.isDefEq.respectTransparency false in
theorem b63e_relForm_mono (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    {U W : Set (Fin 10 → ℂ)} (hWU : W ⊆ U) :
    b63e_relForm b C V hV U ≤ b63e_relForm b C V hV W := by
  rintro θ ⟨hf, hc⟩
  refine ⟨hf, ?_⟩
  intro φ hφ hp
  obtain ⟨a, ha, hθ⟩ := hc φ hφ hp
  refine ⟨a, ha.mono (fun p hp ↦ ⟨hp.1, hp.2.1, hWU hp.2.2⟩), ?_⟩
  exact fun t x ht hx v ↦ hθ t x (hWU ht) hx v

set_option backward.isDefEq.respectTransparency false in
def b63e_periodBasisEval (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {ι : Type} (B : Module.Basis ι ℤ (b3_periodLattice ℂ C)) :
    b3_HolForm ℂ C →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun i ↦ b3A_toDual ⟨(B i).val, b3A_lattice_mem_linearDual (B i)⟩

set_option backward.isDefEq.respectTransparency false in
theorem b63e_periodBasisEval_injective (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [CompactSpace C] [ConnectedSpace C]
    {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b3_periodLattice ℂ C)) :
    Function.Injective (b63e_periodBasisEval C B) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro η hη
  change η = 0
  apply b3A_eq_zero_of_periods (show Module.finrank ℂ ℂ = 1 by simp) η
  intro γ
  have hi (i) : (B i).val η = 0 := congrFun hη i
  let ev : b3_periodLattice ℂ C →ₗ[ℤ] ℂ :=
    { toFun := fun l ↦ l.val η
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have h := congrArg ev (B.sum_repr (b3_latticePeriod ℂ C γ))
  have hB i : ev (B i) = 0 := hi i
  simp only [map_sum, map_smul, hB, smul_zero, Finset.sum_const_zero] at h
  exact h.symm

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b63e_relForm_independent_near (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
    (t₀ : V) (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (ht₀ : t₀.val ∈ U)
    {r : ℕ} (θ : Fin r → b63e_relForm b C V hV U)
    (hθ : LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θ i) t₀)) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∩ U ∧
      ∀ t : V, t.val ∈ W → LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θ i) t) := by
  classical
  choose P hP using fun t : V ↦ b6m_period_comparison (b63l_parameterFibre b C V hV t)
  let L := b3_periodLattice ℂ (b63l_parameterFibre b C V hV t₀)
  letI : Module.Finite ℤ L := b3_periodLattice_finite (show Module.finrank ℂ ℂ = 1 by simp)
  letI : Module.Free ℤ L := b3_periodLattice_free
  let B := Module.Free.chooseBasis ℤ L
  let T (t : V) := (P t₀).symm.trans
    ((b6m_H1Equiv (b6m_transport b C ⟨t₀.val, hV t₀.property⟩ ⟨t.val, hV t.property⟩)).trans (P t))
  let Ψ (t : V) := b63e_periodBasisEval (b63l_parameterFibre b C V hV t) (B.map (T t))
  let v (i : Fin r) (u : Fin 10 → ℂ) (j : Module.Free.ChooseBasisIndex ℤ L) :=
    b63e_periodFunction b C V hV (fun t ↦ (P t).toLinearMap) (θ i) t₀ ((P t₀).symm (B j)) u
  have hv (t : V) (i : Fin r) : v i t.val = Ψ t (b63e_relFormAt b C V hV (θ i) t) := by
    funext j
    dsimp [v, b63e_periodFunction]
    rw [dite_eq_left t.property]
    rfl
  have hperiod i x : AnalyticOnNhd ℂ
      (b63e_periodFunction b C V hV (fun t ↦ (P t).toLinearMap) (θ i) t₀ x) (V ∩ U) :=
    b63e_period_analytic_of_loops b C V hV (fun t ↦ (P t).toLinearMap) (θ i) t₀
      (fun γ ↦ b63e_loop_period_analytic b C V hV hVo hA hincl
        (fun t ↦ (P t).toLinearMap) hP U hU (θ i) t₀ γ) x
  have hvcont : ContinuousAt (fun u i j ↦ v i u j) t₀.val :=
    continuousAt_pi.mpr fun i ↦ continuousAt_pi.mpr fun j ↦
      (hperiod i ((P t₀).symm (B j)) t₀.val ⟨t₀.property, ht₀⟩).continuousAt
  have hli : LinearIndependent ℂ (fun i ↦ v i t₀.val) := by
    simp_rw [hv]
    exact hθ.map' (Ψ t₀) (LinearMap.ker_eq_bot.mpr (b63e_periodBasisEval_injective _ _))
  have hn : {u | u ∈ V ∩ U ∧ LinearIndependent ℂ (fun i ↦ v i u)} ∈ nhds t₀.val :=
    Filter.inter_mem ((hVo.inter hU).mem_nhds ⟨t₀.property, ht₀⟩) (hvcont hli.eventually)
  obtain ⟨W, hsub, hW, htW⟩ := mem_nhds_iff.mp hn
  refine ⟨W, hW, htW, fun u hu ↦ (hsub hu).1, ?_⟩
  intro t ht
  have hi := (hsub ht).2
  simp_rw [hv] at hi
  exact LinearIndependent.of_comp (Ψ t) hi

end HodgeLean.Foundations.Program
