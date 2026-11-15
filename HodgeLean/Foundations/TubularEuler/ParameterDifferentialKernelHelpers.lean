import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Detecting the square of an ideal with differential coordinates

A generating parameter system with coordinate covectors detects the
first-order coefficient of each generator. HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

theorem differential_zero_mem_square_of_parameters
    {A K : Type*} [CommRing A] [NontriviallyNormedField K] (d : ℕ)
    (ε : A →+* K) (D : A →+ ((Fin d → K) →L[K] K))
    (hleibniz : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (t : Fin d → A) (hspan : Ideal.span (Set.range t) = RingHom.ker ε)
    (hD : ∀ i, D (t i) = ContinuousLinearMap.proj i)
    (a : A) (ha : a ∈ RingHom.ker ε) (hzero : D a = 0) :
    a ∈ (RingHom.ker ε) ^ 2 := by
  classical
  have ht : ∀ i, t i ∈ RingHom.ker ε := fun i =>
    hspan ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan.symm ▸ ha)
  have hd : (∑ i, ε (c i) • (ContinuousLinearMap.proj i : (Fin d → K) →L[K] K)) = 0 := by
    rw [← hc, map_sum] at hzero
    simpa only [hleibniz, RingHom.mem_ker.mp (ht _), zero_smul, add_zero, hD] using hzero
  have hcz : ∀ i, c i ∈ RingHom.ker ε := by
    intro i
    have h := congrArg (fun f : (Fin d → K) →L[K] K => f (Pi.single i 1)) hd
    simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul] using h
  rw [← hc, pow_two]
  exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_mul (hcz i) (ht i)

#print axioms differential_zero_mem_square_of_parameters

end HodgeLean.Foundations.TubularEuler
