import HodgeLean.Foundations.Program.G32Native.RetractedManifoldDifferential
import HodgeLean.Foundations.Program.G32Native.ComplexRealManifoldRegularity
import HodgeLean.Foundations.Program.G32Native.NormalQuotientTransverseEquiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Transverse quotient coordinates through an actual manifold retraction

The retraction identity cancels the embedding tangent map before the
original complex quotient section is evaluated in the flattening derivative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold
namespace HodgeLean.Foundations.TubularEuler

theorem retracted_manifold_quotient_coordinates
    {E F B N M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedSpace ℝ B] [IsScalarTower ℝ ℂ B]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [NormedSpace ℝ N] [IsScalarTower ℝ ℂ N]
    [FiniteDimensional ℂ N]
    [TopologicalSpace M] [ChartedSpace E M]
    (emb : M → F) (r : F → M) (a : M → B × N) (C : Set M) (p : M)
    (hp : p ∈ interior C) (hfix : ∀ c ∈ C, r (emb c) = c)
    (hemb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) emb p)
    (hr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (emb p))
    (A : E →L[ℂ] B × N) (ha : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, B × N) a p A)
    (T : E →ₗ[ℂ] N) (L : N →L[ℂ] E)
    (hL : ∀ u, T (L u) = u)
    (hker : ((ContinuousLinearMap.snd ℂ B N).comp A).toLinearMap.ker = T.ker)
    (hsurj : Function.Surjective ((ContinuousLinearMap.snd ℂ B N).comp A)) :
    let S : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) emb p
    ∃ R : N ≃L[ℂ] N,
      HasFDerivAt (fun w : N => (a (r (emb p +
        S (L w)))).2) R.toContinuousLinearMap 0 := by
  dsimp only
  let P := ((ContinuousLinearMap.snd ℂ B N).comp A).toLinearMap
  obtain ⟨R, hR⟩ := quotient_section_transverse_equiv T L.toLinearMap P hL hker hsurj
  refine ⟨R, ?_⟩
  let S : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) emb p
  let Q : F →L[ℝ] E := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (emb p)
  have hfixp := hfix p (interior_subset hp)
  have hcancel := retraction_mfderiv_comp_of_interior emb r C p hp hfix hemb hr
  have haR := hasMFDerivAt_real_of_complex ha
  have haR' : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, B × N) a (r (emb p))
      (A.restrictScalars ℝ) := by
    convert haR using 1 <;> exact hfixp
  have houterM := haR'.comp (emb p) hr.hasMFDerivAt
  have houter : HasFDerivAt (a ∘ r) ((A.restrictScalars ℝ).comp Q) (emb p) := by
    convert (hasMFDerivAt_self_iff_original_charts.mp houterM).2 using 1 <;> rfl
  have hcurve : HasFDerivAt (fun w : N => emb p + S (L w))
      (S.comp (L.restrictScalars ℝ)) 0 :=
    (S.comp (L.restrictScalars ℝ)).hasFDerivAt.const_add (emb p)
  have houter' : HasFDerivAt (a ∘ r) ((A.restrictScalars ℝ).comp Q)
      (emb p + S (L 0)) := by simpa only [map_zero, add_zero] using houter
  have hd := (houter'.comp 0 hcurve).snd
  have heq : (ContinuousLinearMap.snd ℝ B N).comp
      (((A.restrictScalars ℝ).comp Q).comp (S.comp (L.restrictScalars ℝ))) =
      R.toContinuousLinearMap.restrictScalars ℝ := by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc Q,
      hcancel, ContinuousLinearMap.id_comp]
    apply ContinuousLinearMap.ext
    intro u
    exact (hR u).symm
  rw [heq] at hd
  exact hasFDerivAt_of_restrictScalars ℝ hd rfl

#print axioms retracted_manifold_quotient_coordinates
end HodgeLean.Foundations.TubularEuler
