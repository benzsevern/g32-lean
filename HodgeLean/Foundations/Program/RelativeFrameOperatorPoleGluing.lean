import HodgeLean.Foundations.Program.RelativeFrameOperatorPoleData
import HodgeLean.Foundations.Program.RelativeFrameOperatorCentered

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_poleInnerCoeff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) (ε : Fin D.m → ℂ)
    (k : rf4_Src D) (x₀ x : Fin D.m) (w : ℂ) : ℂ := by
  classical
  exact rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.2 x j)) (D.c x + ε x) w +
    if x = x₀ then w⁻¹ else 0

theorem rf4_pole_overlap_coeff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x₀ : Fin D.m) (k : rf4_Src D)
    (hk : rf4_delta D ε k = rf4_poleDatum D ε S.small x₀)
    (x : Fin D.m) (u : b63r_annulus (D.deg x) D.r) :
    rf4_extendBdd (k.1.val (D.ann x)) u =
      rf4_poleInnerCoeff D ε k x₀ x (rf4_rootMap (D.deg x) (ε x) u) *
        deriv (rf4_rootMap (D.deg x) (ε x)) u := by
  classical
  have hval := congrArg (fun F : rf4_Tgt D ↦
    (F x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u) hk
  change (k.1.val (D.ann x) : D.P.piece (D.ann x) →ᵇ ℂ) ⟨u, (D.hann x).ge u.property⟩ -
    ((rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) (k.2 x) :
      b63r_bddHol (b63r_annulus (D.deg x) D.r)) :
        b63r_annulus (D.deg x) D.r →ᵇ ℂ) u = _ at hval
  rw [rf4_poleDatum_apply] at hval
  have hη : (if x = x₀ then (rf4_rootMap (D.deg x) (ε x) u)⁻¹ else 0) *
      deriv (rf4_rootMap (D.deg x) (ε x)) u =
      if x = x₀ then rf4_poleMultiplierFun (D.deg x) (ε x) u else 0 := by
    by_cases h : x = x₀
    · rw [if_pos h, if_pos h]
      exact rf4_poleMultiplier_pullback (D.deg x) (D.hdeg x) D.r D.hr (ε x) (S.small x) u
    · rw [if_neg h, if_neg h, zero_mul]
  unfold rf4_poleInnerCoeff
  rw [add_mul, rf4_sectorOp_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
    (S.small x) (k.2 x) u, hη]
  rw [rf4_extendBdd, dif_pos ((D.hann x).ge u.property)]
  rw [← hval]
  ring

theorem rf4_pole_overlap_form {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x₀ : Fin D.m) (k : rf4_Src D)
    (hk : rf4_delta D ε k = rf4_poleDatum D ε S.small x₀)
    (x : Fin D.m) (u : b63r_annulus (D.deg x) D.r)
    (v : TangentSpace 𝓘(ℂ, ℂ) (S.h ((D.P.chart (D.ann x)).symm u))) :
    rf4_extendBdd (k.1.val (D.ann x)) u *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x))
        (S.h ((D.P.chart (D.ann x)).symm u)) v) =
    rf4_poleInnerCoeff D ε k x₀ x (S.w x (S.h ((D.P.chart (D.ann x)).symm u))) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x)
        (S.h ((D.P.chart (D.ann x)).symm u)) v) := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  let p := S.h ((D.P.chart (D.ann x)).symm u)
  have hut : (u : ℂ) ∈ e.target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact D.P.contained (D.ann x) (subset_closure ((D.hann x).ge u.property))
  have hps : p ∈ e.source := e.map_target hut
  have heval : e p = u := e.right_inv hut
  have hglue := S.glue x u u.property
  apply rf4_chartForm_transition e (S.w x) (S.stationary (D.ann x)) (S.w_mem x)
    p hps hglue.1 v
  rw [heval, rf4_plumbing_transition_deriv S x u]
  change rf4_extendBdd (k.1.val (D.ann x)) u =
    rf4_poleInnerCoeff D ε k x₀ x (S.w x (S.h ((D.P.chart (D.ann x)).symm u))) * _
  rw [hglue.2]
  exact rf4_pole_overlap_coeff S x₀ k hk x u

theorem rf4_pole_outer_inner_agree {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x₀ : Fin D.m) (k : rf4_Src D)
    (hk : rf4_delta D ε k = rf4_poleDatum D ε S.small x₀)
    (p : X) (i : Fin D.P.n) (x : Fin D.m)
    (hi : S.h.symm p ∈ (D.P.chart i).source ∧ D.P.chart i (S.h.symm p) ∈ D.P.piece i)
    (hx : p ∈ (S.w x).source ∧ S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x))
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_extendBdd (k.1.val i) (D.P.chart i (S.h.symm p)) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) p v) =
    rf4_poleInnerCoeff D ε k x₀ x (S.w x p) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) p v) := by
  have hO : p ∈ S.h '' O := by
    refine ⟨S.h.symm p, ?_, S.h.apply_symm_apply p⟩
    exact (Set.ext_iff.mp D.P.covers _).mpr (mem_iUnion.mpr
      ⟨i, D.P.chart i (S.h.symm p), hi.2, (D.P.chart i).left_inv hi.1⟩)
  have hI : p ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) :=
    ⟨S.w x p, hx.2, (S.w x).left_inv hx.1⟩
  have hann := (Set.ext_iff.mp (S.overlap x) p).mp ⟨hO, hI⟩
  obtain ⟨t, ⟨u, hu, hut⟩, htp⟩ := hann
  subst t
  subst p
  have hutarget := D.P.contained (D.ann x) (subset_closure ((D.hann x).ge hu))
  have hAnn : S.h.symm (S.h ((D.P.chart (D.ann x)).symm u)) ∈
      (D.P.chart (D.ann x)).source ∧
      D.P.chart (D.ann x) (S.h.symm (S.h ((D.P.chart (D.ann x)).symm u))) ∈
        D.P.piece (D.ann x) := by
    rw [S.h.symm_apply_apply]
    exact ⟨(D.P.chart (D.ann x)).map_target hutarget,
      by rw [(D.P.chart (D.ann x)).right_inv hutarget]; exact (D.hann x).ge hu⟩
  have hag := rf4_outerForm_agree S k.1 _ i (D.ann x) hi hAnn v
  simp only [S.h.symm_apply_apply, (D.P.chart (D.ann x)).right_inv hutarget] at hag
  have hfun : ((S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) : X → ℂ) =
      (fun q : X ↦ D.P.chart i (S.h.symm q)) := rfl
  rw [hfun]
  simpa only [S.h.symm_apply_apply] using
    hag.trans (rf4_pole_overlap_form S x₀ k hk x ⟨u, hu⟩ v)

end HodgeLean.Foundations.Program
