import HodgeLean.Foundations.Program.RelativeFrameOperatorPoleMeromorphic

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_pole_residue_witness {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x₀ : Fin D.m) (k : rf4_Src D)
    (hk : rf4_delta D ε k = rf4_poleDatum D ε S.small x₀) :
    ∃ w : b4c_MeroForm ℂ X (Module.finrank_self ℂ),
      b4c_res (hE := Module.finrank_self ℂ) w ((S.w x₀).symm 0) = 1 ∧
      ∀ p, p ≠ (S.w x₀).symm 0 → b4c_res (hE := Module.finrank_self ℂ) w p = 0 := by
  classical
  obtain ⟨w, hO, hI⟩ := rf4_pole_meromorphic_exists S x₀ k hk
  let p₀ := (S.w x₀).symm 0
  have hU (x : Fin D.m) : IsOpen (rf4_innerDisc (D.deg x) D.r (ε x)) :=
    isOpen_lt (by fun_prop : Continuous (fun z : ℂ ↦ ‖z ^ D.deg x + ε x‖)) continuous_const
  have hβ (x : Fin D.m) (z : ℂ) (hz : z ∈ rf4_innerDisc (D.deg x) D.r (ε x)) :=
    (rf4_sectorCoeff_differentiableOn (D.deg x) D.r (D.c x) (ε x) (k.2 x)).analyticOnNhd
      (hU x) z hz
  have hn : D.deg x₀ ≠ 0 := by have := D.hdeg x₀; omega
  have h0 : (0 : ℂ) ∈ rf4_innerDisc (D.deg x₀) D.r (ε x₀) := by
    change ‖(0 : ℂ) ^ D.deg x₀ + ε x₀‖ < 2 * D.r
    rw [zero_pow hn, zero_add]
    linarith [S.small x₀, D.hr]
  have h0t := S.w_target x₀ (subset_closure h0)
  have hp₀ : p₀ ∈ (S.w x₀).source := (S.w x₀).map_target h0t
  have hcoord : S.w x₀ p₀ = 0 := (S.w x₀).right_inv h0t
  refine ⟨w, ?_, ?_⟩
  · change TauCeti.Contour.residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) w.val p₀) 0 = 1
    apply rf4_chartField_residue_simple w.val (S.w x₀) (S.w_mem x₀)
      (rf4_innerDisc (D.deg x₀) D.r (ε x₀)) (hU x₀)
      (rf4_sectorCoeff (D.deg x₀) (fun j ↦ rf4_extendBdd (k.2 x₀ j)) (D.c x₀ + ε x₀))
      p₀ hp₀ (by rwa [hcoord]) hcoord (hβ x₀ 0 h0)
    intro q hq hqU v
    simpa [rf4_poleInnerCoeff] using hI x₀ q hq hqU v
  · intro p hpp₀
    change TauCeti.Contour.residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) w.val p) 0 = 0
    rcases rf4_plumbing_cover_coordinates S p with ⟨i, hi, hui⟩ | ⟨x, hx, hux⟩
    · let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
      have hp : p ∈ e.source := by
        change p ∈ Set.univ ∩ _
        exact ⟨Set.mem_univ p, hi⟩
      have hα := ((b63r_mem_bddHol_iff (D.P.isOpen i) _).mp (k.1.val i).property).analyticOnNhd
        (D.P.isOpen i) (D.P.chart i (S.h.symm p)) hui
      exact rf4_chartField_residue_hol w.val e (S.stationary i) (D.P.piece i) (D.P.isOpen i)
        (rf4_extendBdd (k.1.val i)) p hp hui (hO i) hα
    · have han : AnalyticAt ℂ (rf4_poleInnerCoeff D ε k x₀ x) (S.w x p) := by
        change AnalyticAt ℂ (fun z ↦
          rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.2 x j)) (D.c x + ε x) z +
            if x = x₀ then z⁻¹ else 0) (S.w x p)
        by_cases h : x = x₀
        · have hwp : S.w x p ≠ 0 := by
            intro hw0
            apply hpp₀
            have hp : p = (S.w x).symm 0 := by rw [← hw0, (S.w x).left_inv hx]
            simpa only [h] using hp
          simp only [if_pos h]
          have hinv : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) (S.w x p) :=
            (analyticAt_id : AnalyticAt ℂ (fun z : ℂ ↦ z) (S.w x p)).inv hwp
          exact (hβ x _ hux).add hinv
        · simpa only [if_neg h, add_zero] using hβ x _ hux
      exact rf4_chartField_residue_hol w.val (S.w x) (S.w_mem x)
        (rf4_innerDisc (D.deg x) D.r (ε x)) (hU x) (rf4_poleInnerCoeff D ε k x₀ x)
        p hx hux (hI x) han

end HodgeLean.Foundations.Program
