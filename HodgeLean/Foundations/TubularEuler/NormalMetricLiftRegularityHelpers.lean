import HodgeLean.Foundations.TubularEuler.NormalMetricLiftHelpers
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Real analytic dependence of the canonical normal lift

The adjoint is real linear, and inversion is analytic on invertible Gram operators.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [CompleteSpace N]
variable [NormedSpace ℝ E] [NormedSpace ℝ N]

theorem normalAdjoint_contDiff :
    ContDiff ℝ ⊤ (fun D : E →L[𝕜] N => D.adjoint) := by
  let A : (E →L[𝕜] N) →+ (N →L[𝕜] E) := {
    toFun := fun D => D.adjoint
    map_zero' := map_zero ContinuousLinearMap.adjoint
    map_add' := map_add ContinuousLinearMap.adjoint }
  let AR := A.toRealLinearMap ContinuousLinearMap.adjoint.continuous
  exact AR.contDiff

theorem normalGram_contDiffOn
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (D : B → E →L[𝕜] N) (S : Set B) (hD : ContDiffOn ℝ ⊤ D S) :
    ContDiffOn ℝ ⊤ (fun b => (D b).comp (D b).adjoint) S := by
  let C := (ContinuousLinearMap.compL 𝕜 N E N).bilinearRestrictScalars ℝ
  exact (C.contDiff.comp_contDiffOn hD).clm_apply
    (normalAdjoint_contDiff.comp_contDiffOn hD)

theorem normalGramInverse_contDiffOn
    [FiniteDimensional 𝕜 N]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (D : B → E →L[𝕜] N) (S : Set B) (hD : ContDiffOn ℝ ⊤ D S)
    (hsurj : ∀ b ∈ S, Function.Surjective (D b)) :
    ContDiffOn ℝ ⊤ (fun b => ContinuousLinearMap.inverse ((D b).comp (D b).adjoint)) S := by
  intro b hb
  let G := ContinuousLinearEquiv.ofBijective ((D b).comp (D b).adjoint)
    (LinearMap.ker_eq_bot.mpr (normalGram_bijective (D b) (hsurj b hb)).1)
    (LinearMap.range_eq_top.mpr (normalGram_bijective (D b) (hsurj b hb)).2)
  have hc : ContDiffAt 𝕜 ⊤ ContinuousLinearMap.inverse ((D b).comp (D b).adjoint) :=
    contDiffAt_map_inverse G
  have ha : AnalyticAt ℝ ContinuousLinearMap.inverse ((D b).comp (D b).adjoint) :=
    hc.analyticAt.restrictScalars
  exact ha.contDiffAt.comp_contDiffWithinAt b (normalGram_contDiffOn D S hD b hb)

theorem normalMetricLift_contDiffOn
    [FiniteDimensional 𝕜 N]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (D : B → E →L[𝕜] N) (S : Set B) (hD : ContDiffOn ℝ ⊤ D S)
    (hsurj : ∀ b ∈ S, Function.Surjective (D b)) :
    ContDiffOn ℝ ⊤ (fun b => normalMetricLift (D b)) S := by
  let C := (ContinuousLinearMap.compL 𝕜 N N E).bilinearRestrictScalars ℝ
  exact (C.contDiff.comp_contDiffOn (normalAdjoint_contDiff.comp_contDiffOn hD)).clm_apply
    (normalGramInverse_contDiffOn D S hD hsurj)

theorem normalMetricLift_continuousAt
    [FiniteDimensional 𝕜 N] (D : E →L[𝕜] N) (hD : Function.Surjective D) :
    ContinuousAt (normalMetricLift : (E →L[𝕜] N) → (N →L[𝕜] E)) D := by
  let G := ContinuousLinearEquiv.ofBijective (D.comp D.adjoint)
    (LinearMap.ker_eq_bot.mpr (normalGram_bijective D hD).1)
    (LinearMap.range_eq_top.mpr (normalGram_bijective D hD).2)
  have hi : ContinuousAt ContinuousLinearMap.inverse (D.comp D.adjoint) :=
    (contDiffAt_map_inverse (n := ⊤) G).continuousAt
  have hAdj : Continuous (fun T : E →L[𝕜] N => T.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  have hGram : Continuous (fun T : E →L[𝕜] N => T.comp T.adjoint) :=
    continuous_id.clm_comp hAdj
  have hInv : ContinuousAt (fun T : E →L[𝕜] N =>
      ContinuousLinearMap.inverse (T.comp T.adjoint)) D :=
    hi.comp (f := fun T : E →L[𝕜] N => T.comp T.adjoint) (x := D) hGram.continuousAt
  exact hAdj.continuousAt.clm_comp hInv

#print axioms normalMetricLift_continuousAt

#print axioms normalMetricLift_contDiffOn

#print axioms normalGramInverse_contDiffOn

#print axioms normalGram_contDiffOn

#print axioms normalAdjoint_contDiff

end HodgeLean.Foundations.TubularEuler
