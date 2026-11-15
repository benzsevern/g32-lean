import HodgeLean.Foundations.Program.G32Native.NormalFrameModelProjection
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions

/-! # Analytic addition in the original normal frame coordinates

Base projection is replaced by the actual base chart inverse only on the
open target of the retained bundle chart.
-/

noncomputable section
open Bundle Filter Topology
namespace HodgeLean.Foundations.TubularEuler

theorem normal_frame_addition_analyticAt
    {B A F Y : Type*} [TopologicalSpace B]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
    (e : Trivialization F (π F E)) (b : OpenPartialHomeomorph B A)
    (u : B → Y) (δ : TotalSpace F E → Y) (q : A × F)
    (hq : q ∈ (e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).target)
    (hu : AnalyticAt ℝ (fun c => u (b.symm c)) q.1)
    (hδ : AnalyticAt ℝ (fun t => δ ((e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).symm t)) q) :
    let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl F))
    AnalyticAt ℝ (fun t => u (P.symm t).proj + δ (P.symm t)) q := by
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl F))
  have heq : (fun t => u (P.symm t).proj) =ᶠ[𝓝 q] (fun t : A × F => u (b.symm t.1)) := by
    filter_upwards [P.open_target.mem_nhds hq] with t ht
    exact congrArg u (normal_frame_model_inverse_proj E e b t ht)
  have hb : AnalyticAt ℝ (fun t : A × F => u (b.symm t.1)) q :=
    hu.comp (f := (Prod.fst : A × F → A)) (x := q) analyticAt_fst
  exact (hb.congr heq.symm).add hδ

#print axioms normal_frame_addition_analyticAt

theorem normal_frame_retracted_coordinates_analyticAt
    {B A F Y Z : Type*} [TopologicalSpace B]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
    (e : Trivialization F (π F E)) (b : OpenPartialHomeomorph B A)
    (u : B → Y) (δ : TotalSpace F E → Y) (R : Y → Z) (q : A × F)
    (hq : q ∈ (e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).target)
    (hu : AnalyticAt ℝ (fun c => u (b.symm c)) q.1)
    (hδ : AnalyticAt ℝ (fun t => δ ((e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl F))).symm t)) q)
    (hR : AnalyticAt ℝ R
      (u (((e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl F))).symm q).proj) +
          δ ((e.toOpenPartialHomeomorph.trans
            (b.prod (OpenPartialHomeomorph.refl F))).symm q))) :
    let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl F))
    AnalyticAt ℝ (fun t => R (u (P.symm t).proj + δ (P.symm t))) q := by
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl F))
  exact hR.comp (f := fun t : A × F => u (P.symm t).proj + δ (P.symm t)) (x := q)
    (normal_frame_addition_analyticAt E e b u δ q hq hu hδ)

#print axioms normal_frame_retracted_coordinates_analyticAt
end HodgeLean.Foundations.TubularEuler
