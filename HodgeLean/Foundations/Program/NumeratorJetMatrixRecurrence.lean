import HodgeLean.Foundations.Program.NumeratorJetConvolution
import HodgeLean.Foundations.Program.NumeratorJetDenominator

/-! # Matrix Taylor convolutions for the Schlesinger field -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Matrix multiplication gives a finite convolution of entry coefficients. -/
theorem b65e_matrix_mul_coeff {A B : ℂ → Matrix (Fin 4) (Fin 4) ℂ}
    {P Q : Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ i j, HasFPowerSeriesAt (fun θ ↦ A θ i j) (P i j) 0)
    (hQ : ∀ i j, HasFPowerSeriesAt (fun θ ↦ B θ i j) (Q i j) 0)
    (i j : Fin 4) {S : FormalMultilinearSeries ℂ ℂ ℂ}
    (hS : HasFPowerSeriesAt (fun θ ↦ (A θ * B θ) i j) S 0) (n : ℕ) :
    S.coeff n = ∑ k : Fin 4, ∑ a ∈ Finset.range (n + 1),
      (P i k).coeff a * (Q k j).coeff (n - a) := by
  have han (k : Fin 4) := (hP i k).analyticAt.mul (hQ k j).analyticAt
  choose T hT using han
  rw [b65e_sum_coeff Finset.univ (fun k _ ↦ hT k) hS]
  exact Finset.sum_congr rfl fun k _ ↦ b65e_mul_coeff (hP i k) (hQ k j) (hT k) n

/-- Matrix commutators give differences of entry convolutions. -/
theorem b65e_matrix_commutator_coeff {A B : ℂ → Matrix (Fin 4) (Fin 4) ℂ}
    {P Q : Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ i j, HasFPowerSeriesAt (fun θ ↦ A θ i j) (P i j) 0)
    (hQ : ∀ i j, HasFPowerSeriesAt (fun θ ↦ B θ i j) (Q i j) 0)
    (i j : Fin 4) {S : FormalMultilinearSeries ℂ ℂ ℂ}
    (hS : HasFPowerSeriesAt (fun θ ↦ (A θ * B θ - B θ * A θ) i j) S 0)
    (n : ℕ) :
    S.coeff n =
      (∑ k : Fin 4, ∑ a ∈ Finset.range (n + 1),
        (P i k).coeff a * (Q k j).coeff (n - a)) -
      (∑ k : Fin 4, ∑ a ∈ Finset.range (n + 1),
        (Q i k).coeff a * (P k j).coeff (n - a)) := by
  have hab : AnalyticAt ℂ (fun θ ↦ (A θ * B θ) i j) 0 := by
    convert Finset.analyticAt_sum Finset.univ
      (fun k _ ↦ (hP i k).analyticAt.mul (hQ k j).analyticAt) using 1
    ext θ
    simp [Matrix.mul_apply]
  have hba : AnalyticAt ℂ (fun θ ↦ (B θ * A θ) i j) 0 := by
    convert Finset.analyticAt_sum Finset.univ
      (fun k _ ↦ (hQ i k).analyticAt.mul (hP k j).analyticAt) using 1
    ext θ
    simp [Matrix.mul_apply]
  obtain ⟨T, hT⟩ := hab
  obtain ⟨U, hU⟩ := hba
  rw [b65e_sub_coeff hT hU hS,
    b65e_matrix_mul_coeff hP hQ i j hT, b65e_matrix_mul_coeff hQ hP i j hU]

end HodgeLean.Foundations.Program
