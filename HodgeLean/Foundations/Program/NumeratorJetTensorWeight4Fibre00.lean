import HodgeLean.Foundations.Program.NumeratorJetTensorWeightData

/-! # Finite rational tensor-weight certificates -/

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_4_0_0_0 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 0 0 (b65e_tensorWeightCoeffQ 3 0 0)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 0 0 a b) 0 h = b65e_tensorWeightCoeffQ 4 0 0 0 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_4_0_0_1 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 0 0 (b65e_tensorWeightCoeffQ 3 0 0)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 0 0 a b) 1 h = b65e_tensorWeightCoeffQ 4 0 0 1 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_4_0_0_2 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 0 0 (b65e_tensorWeightCoeffQ 3 0 0)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 0 0 a b) 2 h = b65e_tensorWeightCoeffQ 4 0 0 2 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_4_0_0_3 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 0 0 (b65e_tensorWeightCoeffQ 3 0 0)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 0 0 a b) 3 h = b65e_tensorWeightCoeffQ 4 0 0 3 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_4_0_0_4 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 0 0 (b65e_tensorWeightCoeffQ 3 0 0)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 0 0 a b) 4 h = b65e_tensorWeightCoeffQ 4 0 0 4 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_4_0_0_5 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 0 0 (b65e_tensorWeightCoeffQ 3 0 0)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 0 0 a b) 5 h = b65e_tensorWeightCoeffQ 4 0 0 5 h := by
  decide +kernel

end HodgeLean.Foundations.Program
