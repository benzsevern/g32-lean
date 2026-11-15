import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusLocalLift
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ChartTangentCurve
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.AbelDifferentialSpan
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option backward.isDefEq.respectTransparency false
noncomputable section
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.AbelAdapter.StageTwo Filter
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

theorem abel_local_curve (h : Module.finrank ℂ E = 1) (p q : C) (v : E) :
    ∃ g : ℂ → b3Rest2_VJ E C, g 0 = 0 ∧
      HasStrictDerivAt g
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) (analyticAbel (E := E) (C := C) h p) q v) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), b3Rest2_covHom (E := E) (C := C) (g z) ∈
        (weightedSum (analyticAbel (E := E) (C := C) h p)).range := by
  let a := analyticAbel (E := E) (C := C) h p
  let cov := b3Rest2_covHom (E := E) (C := C)
  have ha := b3_abelJacobi_holomorphic (E := E) (C := C) h p a
    (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec
  have hLift := torus_localLift (E := E) (C := C) (L := b3_periodLattice E C)
    (b3_periodF E C) a q (ha q)
  let G := hLift.choose
  have hG : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) ω G q := hLift.choose_spec.1
  have he : a =ᶠ[𝓝 q] b2_torusCover (b3_periodLattice E C) (b3_periodF E C) ∘ G :=
    hLift.choose_spec.2
  have hCurve := exists_holomorphic_curve_tangent (E := E) (C := C) q v
  let r := hCurve.choose
  have hr0 : r 0 = q := hCurve.choose_spec.1
  have hr : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω r 0 := hCurve.choose_spec.2.1
  have hdr : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) r 0
      ((ContinuousLinearMap.id ℂ ℂ).smulRight v) := hCurve.choose_spec.2.2
  let g : ℂ → b3Rest2_VJ E C := fun z ↦ G (r z) - G q
  have hGr : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) ω G (r 0) := by
    simpa only [hr0] using hG
  have hghol : ContDiffAt ℂ ω g 0 := ((hGr.comp 0 hr).sub contMDiffAt_const).contDiffAt
  have hgd : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) G (r 0)
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) G q) := by
    rw [hr0]
    exact (hG.mdifferentiableAt (by simp)).hasMFDerivAt
  have hsub := (hgd.comp 0 hdr).sub
    (hasMFDerivAt_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, b3Rest2_VJ E C)) (G q) 0)
  have hprojected := torusCover_lift_mfderiv (U := E) (M := C) (Λ := b3_periodLattice E C) (b3_periodF E C) a G q
    (hG.mdifferentiableAt (by simp)) he
  have hderiv : HasDerivAt g
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) a q v) 0 := by
    apply hsub.hasFDerivAt.hasDerivAt.congr_deriv
    change (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) G q) ((1 : ℂ) • v) - 0 = _
    exact (sub_zero _).trans
      ((congrArg (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) G q) (one_smul ℂ v)).trans
        (congrArg (fun L : E →L[ℂ] b3Rest2_VJ E C ↦ L v) hprojected).symm)
  refine ⟨g, ?_, hghol.hasStrictDerivAt' hderiv (by simp), ?_⟩
  · change G (r 0) - G q = 0
    exact (congrArg (fun x : C ↦ G x - G q) hr0).trans (sub_self _)
  · have hrt0 : Tendsto r (𝓝 (0 : ℂ)) (𝓝 (r 0)) := hr.continuousAt
    have hrt : Tendsto r (𝓝 (0 : ℂ)) (𝓝 q) := hr0 ▸ hrt0
    have hpoint := he.self_of_nhds
    filter_upwards [he.comp_tendsto hrt] with z hz
    refine ⟨Finsupp.single (r z) 1 - Finsupp.single q 1, ?_⟩
    calc
      weightedSum a (Finsupp.single (r z) 1 - Finsupp.single q 1) = a (r z) - a q := by
        simp only [map_sub, weightedSum, LinearMap.toAddMonoidHom_coe,
          Finsupp.linearCombination_single, one_smul]
      _ = cov (G (r z)) - cov (G q) := congrArg₂ (fun x y : b3_Jacobian E C ↦ x - y) hz hpoint
      _ = cov (g z) := (map_sub cov _ _).symm

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
