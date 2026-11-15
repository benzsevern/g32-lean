import HodgeLean.Foundations.Program.G32Native.CompactNearestChartRegularity

/-! # Nearest-point chart regularity through an equivalent Hilbert model

The original chart and its original normed model are retained in the result.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function Set Topology
namespace HodgeLean.Foundations.TubularEuler

/-- A continuous linear change to Hilbert coordinates transfers the nearest-point
argument to the original normed coordinate model.
Source: `compactNearest_chart_analytic` and the chain rule through a continuous
linear equivalence.
HC no distance; AV milestone no distance. -/
theorem compactNearest_chart_analytic_of_model_equiv
    {M E B F : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : B ≃L[ℝ] E) (C : Set M) [CompactSpace C] [Nonempty C]
    (e : M → F) (he : Continuous e)
    (hemb : Topology.IsEmbedding (fun z : C => e z))
    (a : OpenPartialHomeomorph M E) (c : C)
    (hc : (c : M) ∈ a.source) (hcC : (c : M) ∈ interior C)
    (hσ : ContDiffAt ℝ ⊤ (fun b => e (a.symm b)) (a c))
    (hinj : Injective (fderiv ℝ (fun b => e (a.symm b)) (a c))) :
    ContDiffAt ℝ ⊤
      (fun y => a ((CompactNearest.nearest (fun z : C => e z)
        (he.comp continuous_subtype_val) y : C) : M)) (e c) := by
  let aB := a.trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  let σ : E → F := fun b => e (a.symm b)
  let b := L.symm (a c)
  have hLb : L b = a c := L.apply_symm_apply _
  have hs : ContDiffAt ℝ ⊤ σ (L b) := by simpa only [hLb] using hσ
  have hSB : ContDiffAt ℝ ⊤ (fun t : B => σ (L t)) b :=
    hs.comp b L.contDiff.contDiffAt
  have hd : HasFDerivAt σ (fderiv ℝ σ (a c)) (L b) := by
    simpa only [hLb] using (hσ.differentiableAt (by simp)).hasFDerivAt
  have hdB := hd.comp b L.hasFDerivAt
  have hiB : Injective (fderiv ℝ (fun t : B => σ (L t)) b) := by
    change Injective (fderiv ℝ (σ ∘ L) b)
    rw [hdB.fderiv]
    exact hinj.comp L.injective
  have hcB : (c : M) ∈ aB.source := ⟨hc, mem_univ _⟩
  have hσB : ContDiffAt ℝ ⊤ (fun t => e (aB.symm t)) (aB c) := hSB
  have hinjB : Injective (fderiv ℝ (fun t => e (aB.symm t)) (aB c)) := hiB
  have hreg := compactNearest_chart_analytic C e he hemb aB c hcB hcC hσB hinjB
  have hcomp := L.contDiff.contDiffAt.comp (e c) hreg
  convert hcomp using 1
  funext y
  exact (L.apply_symm_apply _).symm

#print axioms compactNearest_chart_analytic_of_model_equiv

end HodgeLean.Foundations.TubularEuler
