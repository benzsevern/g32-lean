import HodgeLean.Foundations.Program.SchoenCycleProjectiveSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleHomogeneousNormalization

/-! # Normalizing actual regular linear sections against analytic homogeneous lifts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An arbitrary analytic homogeneous lift normalizes the actual chart linear section by an analytic reciprocal coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15. -/
theorem s2e_standardProjectiveLinearSection_analytic_lift
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k d : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ)
    (r : (Fin d → ℂ) → ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (a : (Fin d → ℂ) → (Fin (k + 1) → ℂ)) (ha : AnalyticAt ℂ a 0)
    (hlift : ∀ᶠ z in 𝓝 0, ∃ hz : (∑ j, a z j • Module.finBasisOfFinrankEq ℂ V hd j) ≠ 0,
      (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm (r z) =
        Projectivization.mk ℂ (∑ j, a z j • Module.finBasisOfFinrankEq ℂ V hd j) hz) :
    ∃ (i : Fin (k + 1)) (η : (Fin d → ℂ) → ℂ),
      (r 0).underlying ∈ (s2e_standardProjectiveAffineOpen i).1 ∧
      AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0,
        Point.evaluate (s2e_standardProjectiveAffineOpen i).1
          (s2e_standardProjectiveLinearSection V k hd L i) (r z) =
          η z * L (∑ j, a z j • Module.finBasisOfFinrankEq ℂ V hd j)) := by
  classical
  let b := Module.finBasisOfFinrankEq ℂ V hd
  have hn (z) (hz : (∑ j, a z j • b j) ≠ 0) : a z ≠ 0 := by
    intro h
    apply hz
    simp [h]
  have hr (z) (hz : (∑ j, a z j • b j) ≠ 0) (hh :
      (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm (r z) =
        Projectivization.mk ℂ (∑ j, a z j • b j) hz) :
      r z = vectorToComplexPoint (a z) (hn z hz) := by
    apply (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm.injective
    rw [hh, s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
    simp only [Module.Basis.equivFun_symm_apply, b]
  obtain ⟨hz0, hh0⟩ := hlift.self_of_nhds
  obtain ⟨i, hi⟩ : ∃ i, a 0 i ≠ 0 := by
    by_contra! h
    exact hn 0 hz0 (funext h)
  have hai : AnalyticAt ℂ (fun z => a z i) 0 :=
    ((ContinuousLinearMap.proj i : (Fin (k + 1) → ℂ) →L[ℂ] ℂ).analyticAt (a 0)).comp ha
  refine ⟨i, (fun z => (a z i)⁻¹), ?_, hai.inv hi, inv_ne_zero hi, ?_⟩
  · rw [hr 0 hz0 hh0]
    exact s2e_standardProjectiveAffineOpen_mem (a 0) i hi
  · filter_upwards [hlift, hai.continuousAt.eventually_ne hi] with z hz hzi
    obtain ⟨hz, hh⟩ := hz
    rw [hr z hz hh]
    exact s2e_standardProjectiveLinearSection_evaluate V k hd L (a z) i hzi

end HodgeLean.Foundations.Program
