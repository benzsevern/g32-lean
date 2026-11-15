import HodgeLean.Foundations.Program.NumeratorJetTensorWeightData

/-! # Finite rational tensor-weight certificates -/

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_1_1_1_0 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 1 1 (b65e_tensorWeightCoeffQ 0 1 1)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 1 1 a b) 0 h = b65e_tensorWeightCoeffQ 1 1 1 0 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_1_1_1_1 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 1 1 (b65e_tensorWeightCoeffQ 0 1 1)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 1 1 a b) 1 h = b65e_tensorWeightCoeffQ 1 1 1 1 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_1_1_1_2 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 1 1 (b65e_tensorWeightCoeffQ 0 1 1)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 1 1 a b) 2 h = b65e_tensorWeightCoeffQ 1 1 1 2 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_1_1_1_3 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 1 1 (b65e_tensorWeightCoeffQ 0 1 1)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 1 1 a b) 3 h = b65e_tensorWeightCoeffQ 1 1 1 3 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_1_1_1_4 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 1 1 (b65e_tensorWeightCoeffQ 0 1 1)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 1 1 a b) 4 h = b65e_tensorWeightCoeffQ 1 1 1 4 h := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A target-coordinate row of the rational geometric weight. -/
theorem b65e_tensorWeight_certificate_1_1_1_5 : ∀ h : Fin 6,
    b65e_tensorCoordinateMulQ 1 1 (b65e_tensorWeightCoeffQ 0 1 1)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 1 1 a b) 5 h = b65e_tensorWeightCoeffQ 1 1 1 5 h := by
  decide +kernel

end HodgeLean.Foundations.Program
