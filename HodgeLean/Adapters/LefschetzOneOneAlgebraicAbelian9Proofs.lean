import HodgeLean.Foundations.AnalyticDivisorAlgebraic18
import HodgeLean.Foundations.AnalyticDivisorAlgebraic20

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Adapters

/-- An irreducible analytic equation has a directional derivative outside its principal ideal.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter II.B,
convergent power series and order of vanishing in characteristic zero. -/
theorem bh9_irreducible_derivative_aux (n : ℕ) (p : Fin n → ℂ)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
    (hirr : IsIrreducibleAt f p) :
    ∃ v : Fin n → ℂ, ¬ ∃ g : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ g p ∧
      (fun z ↦ fderiv ℂ f z v) =ᶠ[𝓝 p] (fun z ↦ f z * g z) := by
  classical
  by_contra h
  push_neg at h
  choose g hg heq using fun i ↦ h (Pi.single i 1)
  have hall : ∀ᶠ z in 𝓝 p, ∀ i, fderiv ℂ f z (Pi.single i 1) = f z * g i z := by
    filter_upwards [(Filter.eventually_all_finite Set.finite_univ).2
      fun i _ ↦ heq i] with z hz
    exact fun i ↦ hz i (Set.mem_univ i)
  obtain ⟨W, hW, hWo, hpW, hdense, -⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic20.gaga20_regular_locus
      p f hf hirr.1 hirr
  have hpcl : p ∈ closure
      (HodgeLean.Foundations.AnalyticDivisorAlgebraic20.gaga20_regularZero f ∩ W) := by
    rw [hdense]
    exact ⟨hirr.1, subset_closure hpW⟩
  have hfreq := mem_closure_iff_frequently.mp hpcl
  obtain ⟨q, hqreg, hqall⟩ := (hfreq.and_eventually hall).exists
  have hzero : fderiv ℂ f q = 0 := by
    ext v
    simp only [ContinuousLinearMap.zero_apply]
    have hv : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
      ext j
      simp [Pi.single_apply]
    calc
      fderiv ℂ f q v = fderiv ℂ f q (∑ i, v i • Pi.single i (1 : ℂ)) :=
        congrArg (fderiv ℂ f q) hv
      _ = ∑ i, v i • fderiv ℂ f q (Pi.single i 1) := by
        simp only [map_sum, map_smul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hqall i, hqreg.1.1, zero_mul, smul_zero]
  exact hqreg.1.2 hzero

end HodgeLean.Adapters
