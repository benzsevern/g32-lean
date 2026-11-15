import HodgeLean.Foundations.AnalyticDivisorAlgebraic16Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic16

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

theorem spec_local_factor_component_aux {n k : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i)
    {u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j)
    (hfac : f i =ᶠ[nhds p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) (j : Fin k) :
    (∀ᶠ y in nhds p, y ∈ gaga16_localComponent V f i (P j) ↔ y ∈ V i ∧ P j y = 0) ∧
      ∀ᶠ y in nhds p,
        y ∈ V i → (y ∈ localDivisorSupport V f ↔ ∃ l : Fin k, P l y = 0) := by
  have hu_ne : ∀ᶠ y in nhds p, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hVi : V i ∈ nhds p := (hD.1 i).mem_nhds hi
  have hfac' : ∀ᶠ y in nhds p, f i y = u y * ∏ l, P l y ^ m l := hfac
  constructor
  · filter_upwards [hVi, hfac', hu_ne] with y hyV hyfac hyu
    simp only [gaga16_localComponent, mem_inter_iff, mem_ofPred_eq]
    rw [spec_mem_localDivisorSupport_iff_aux hD i y hyV, hyfac]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · rintro ⟨-, hj⟩
      have hjpow : P j y ^ m j = 0 := by
        rw [hj, zero_pow (Nat.ne_of_gt (hP j).2.2)]
      have hprod : ∏ l, P l y ^ m l = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hjpow
      exact ⟨⟨hyV, mul_eq_zero.mpr (Or.inr hprod)⟩, hj⟩
  · filter_upwards [hfac', hu_ne] with y hyfac hyu hyV
    rw [spec_mem_localDivisorSupport_iff_aux hD i y hyV, hyfac, mul_eq_zero]
    simp only [hyu, false_or, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, ?_⟩
      by_contra hPl
      exact (pow_ne_zero (m l) hPl) hl
    · rintro ⟨l, hl⟩
      exact ⟨l, by rw [hl, zero_pow (Nat.ne_of_gt (hP l).2.2)]⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic16
