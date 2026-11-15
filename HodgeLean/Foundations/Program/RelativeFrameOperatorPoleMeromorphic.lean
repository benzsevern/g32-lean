import HodgeLean.Foundations.Program.RelativeFrameOperatorPoleField
import HodgeLean.Foundations.Program.RelativeFrameOperatorPoleResidue

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_pole_meromorphic_exists {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x₀ : Fin D.m) (k : rf4_Src D)
    (hk : rf4_delta D ε k = rf4_poleDatum D ε S.small x₀) :
    ∃ θ : b4c_MeroForm ℂ X (Module.finrank_self ℂ),
      (∀ i p, p ∈ (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i).source →
        D.P.chart i (S.h.symm p) ∈ D.P.piece i → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ ⟨p, v⟩ = rf4_extendBdd (k.1.val i) (D.P.chart i (S.h.symm p)) *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) p v)) ∧
      ∀ x p, p ∈ (S.w x).source → S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x) →
        ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ ⟨p, v⟩ = rf4_poleInnerCoeff D ε k x₀ x (S.w x p) *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) p v) := by
  classical
  obtain ⟨θ, hlin, hO, hI⟩ := rf4_pole_field_exists S x₀ k hk
  have hU (x : Fin D.m) : IsOpen (rf4_innerDisc (D.deg x) D.r (ε x)) :=
    isOpen_lt (by fun_prop : Continuous (fun w : ℂ ↦ ‖w ^ D.deg x + ε x‖)) continuous_const
  have hβ (x : Fin D.m) (z : ℂ) (hz : z ∈ rf4_innerDisc (D.deg x) D.r (ε x)) :=
    (rf4_sectorCoeff_differentiableOn (D.deg x) D.r (D.c x) (ε x) (k.2 x)).analyticOnNhd
      (hU x) z hz
  have hmero (p : X) : MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 := by
    rcases rf4_plumbing_cover_coordinates S p with ⟨i, hi, hui⟩ | ⟨x, hx, hux⟩
    · let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
      have hp : p ∈ e.source := by
        change p ∈ Set.univ ∩ _
        exact ⟨Set.mem_univ p, hi⟩
      have hα := ((b63r_mem_bddHol_iff (D.P.isOpen i) _).mp (k.1.val i).property).analyticOnNhd
        (D.P.isOpen i) (D.P.chart i (S.h.symm p)) hui
      exact rf4_chartField_meromorphic θ e (S.stationary i) (D.P.piece i) (D.P.isOpen i)
        (rf4_extendBdd (k.1.val i)) p hp hui (hO i) hα.meromorphicAt
    · apply rf4_chartField_meromorphic θ (S.w x) (S.w_mem x)
        (rf4_innerDisc (D.deg x) D.r (ε x)) (hU x) (rf4_poleInnerCoeff D ε k x₀ x)
        p hx hux (hI x)
      change MeromorphicAt (fun z ↦
        rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.2 x j)) (D.c x + ε x) z +
          if x = x₀ then z⁻¹ else 0) (S.w x p)
      by_cases h : x = x₀
      · simp only [if_pos h]
        have hinv : MeromorphicAt (fun z : ℂ ↦ z⁻¹) (S.w x p) :=
          (analyticAt_id : AnalyticAt ℂ (fun z : ℂ ↦ z) (S.w x p)).meromorphicAt.inv
        exact (hβ x _ hux).meromorphicAt.fun_add hinv
      · simpa only [if_neg h, add_zero] using (hβ x _ hux).meromorphicAt
  exact ⟨⟨θ, hlin, hmero⟩, hO, hI⟩

end HodgeLean.Foundations.Program
