import HodgeLean.Foundations.Program.NumeratorJetTensorWeight0Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight0Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight0Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight0Fibre11
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight1Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight1Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight1Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight1Fibre11
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight2Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight2Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight2Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight2Fibre11
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight3Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight3Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight3Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight3Fibre11
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight4Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight4Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight4Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight4Fibre11
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight5Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight5Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight5Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight5Fibre11
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight6Fibre00
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight6Fibre01
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight6Fibre10
import HodgeLean.Foundations.Program.NumeratorJetTensorWeight6Fibre11

/-! # Tensor-coordinate geometric recurrence certificates through field order six -/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The initial rational tensor arrays agree with the velocity and inverse calculation. -/
theorem b65e_tensorWeight_certificate_zero (e d : Fin 2) (c h : Fin 6) :
    b65e_initialTensorCoordsQ e d c h = b65e_tensorWeightCoeffQ 0 e d c h := by
  fin_cases e <;> fin_cases d <;> fin_cases c
  · exact b65e_tensorWeight_certificate_0_0_0_0 h
  · exact b65e_tensorWeight_certificate_0_0_0_1 h
  · exact b65e_tensorWeight_certificate_0_0_0_2 h
  · exact b65e_tensorWeight_certificate_0_0_0_3 h
  · exact b65e_tensorWeight_certificate_0_0_0_4 h
  · exact b65e_tensorWeight_certificate_0_0_0_5 h
  · exact b65e_tensorWeight_certificate_0_0_1_0 h
  · exact b65e_tensorWeight_certificate_0_0_1_1 h
  · exact b65e_tensorWeight_certificate_0_0_1_2 h
  · exact b65e_tensorWeight_certificate_0_0_1_3 h
  · exact b65e_tensorWeight_certificate_0_0_1_4 h
  · exact b65e_tensorWeight_certificate_0_0_1_5 h
  · exact b65e_tensorWeight_certificate_0_1_0_0 h
  · exact b65e_tensorWeight_certificate_0_1_0_1 h
  · exact b65e_tensorWeight_certificate_0_1_0_2 h
  · exact b65e_tensorWeight_certificate_0_1_0_3 h
  · exact b65e_tensorWeight_certificate_0_1_0_4 h
  · exact b65e_tensorWeight_certificate_0_1_0_5 h
  · exact b65e_tensorWeight_certificate_0_1_1_0 h
  · exact b65e_tensorWeight_certificate_0_1_1_1 h
  · exact b65e_tensorWeight_certificate_0_1_1_2 h
  · exact b65e_tensorWeight_certificate_0_1_1_3 h
  · exact b65e_tensorWeight_certificate_0_1_1_4 h
  · exact b65e_tensorWeight_certificate_0_1_1_5 h

/-- The listed rational arrays obey multiplication by the negative initial weight. -/
theorem b65e_tensorWeight_certificate_succ (n : Fin 6) (e d : Fin 2) (c h : Fin 6) :
    b65e_tensorCoordinateMulQ e d (b65e_tensorWeightCoeffQ n.castSucc e d)
      (fun a b ↦ -b65e_tensorWeightCoeffQ 0 e d a b) c h =
        b65e_tensorWeightCoeffQ n.succ e d c h := by
  fin_cases n <;> fin_cases e <;> fin_cases d <;> fin_cases c
  · exact b65e_tensorWeight_certificate_1_0_0_0 h
  · exact b65e_tensorWeight_certificate_1_0_0_1 h
  · exact b65e_tensorWeight_certificate_1_0_0_2 h
  · exact b65e_tensorWeight_certificate_1_0_0_3 h
  · exact b65e_tensorWeight_certificate_1_0_0_4 h
  · exact b65e_tensorWeight_certificate_1_0_0_5 h
  · exact b65e_tensorWeight_certificate_1_0_1_0 h
  · exact b65e_tensorWeight_certificate_1_0_1_1 h
  · exact b65e_tensorWeight_certificate_1_0_1_2 h
  · exact b65e_tensorWeight_certificate_1_0_1_3 h
  · exact b65e_tensorWeight_certificate_1_0_1_4 h
  · exact b65e_tensorWeight_certificate_1_0_1_5 h
  · exact b65e_tensorWeight_certificate_1_1_0_0 h
  · exact b65e_tensorWeight_certificate_1_1_0_1 h
  · exact b65e_tensorWeight_certificate_1_1_0_2 h
  · exact b65e_tensorWeight_certificate_1_1_0_3 h
  · exact b65e_tensorWeight_certificate_1_1_0_4 h
  · exact b65e_tensorWeight_certificate_1_1_0_5 h
  · exact b65e_tensorWeight_certificate_1_1_1_0 h
  · exact b65e_tensorWeight_certificate_1_1_1_1 h
  · exact b65e_tensorWeight_certificate_1_1_1_2 h
  · exact b65e_tensorWeight_certificate_1_1_1_3 h
  · exact b65e_tensorWeight_certificate_1_1_1_4 h
  · exact b65e_tensorWeight_certificate_1_1_1_5 h
  · exact b65e_tensorWeight_certificate_2_0_0_0 h
  · exact b65e_tensorWeight_certificate_2_0_0_1 h
  · exact b65e_tensorWeight_certificate_2_0_0_2 h
  · exact b65e_tensorWeight_certificate_2_0_0_3 h
  · exact b65e_tensorWeight_certificate_2_0_0_4 h
  · exact b65e_tensorWeight_certificate_2_0_0_5 h
  · exact b65e_tensorWeight_certificate_2_0_1_0 h
  · exact b65e_tensorWeight_certificate_2_0_1_1 h
  · exact b65e_tensorWeight_certificate_2_0_1_2 h
  · exact b65e_tensorWeight_certificate_2_0_1_3 h
  · exact b65e_tensorWeight_certificate_2_0_1_4 h
  · exact b65e_tensorWeight_certificate_2_0_1_5 h
  · exact b65e_tensorWeight_certificate_2_1_0_0 h
  · exact b65e_tensorWeight_certificate_2_1_0_1 h
  · exact b65e_tensorWeight_certificate_2_1_0_2 h
  · exact b65e_tensorWeight_certificate_2_1_0_3 h
  · exact b65e_tensorWeight_certificate_2_1_0_4 h
  · exact b65e_tensorWeight_certificate_2_1_0_5 h
  · exact b65e_tensorWeight_certificate_2_1_1_0 h
  · exact b65e_tensorWeight_certificate_2_1_1_1 h
  · exact b65e_tensorWeight_certificate_2_1_1_2 h
  · exact b65e_tensorWeight_certificate_2_1_1_3 h
  · exact b65e_tensorWeight_certificate_2_1_1_4 h
  · exact b65e_tensorWeight_certificate_2_1_1_5 h
  · exact b65e_tensorWeight_certificate_3_0_0_0 h
  · exact b65e_tensorWeight_certificate_3_0_0_1 h
  · exact b65e_tensorWeight_certificate_3_0_0_2 h
  · exact b65e_tensorWeight_certificate_3_0_0_3 h
  · exact b65e_tensorWeight_certificate_3_0_0_4 h
  · exact b65e_tensorWeight_certificate_3_0_0_5 h
  · exact b65e_tensorWeight_certificate_3_0_1_0 h
  · exact b65e_tensorWeight_certificate_3_0_1_1 h
  · exact b65e_tensorWeight_certificate_3_0_1_2 h
  · exact b65e_tensorWeight_certificate_3_0_1_3 h
  · exact b65e_tensorWeight_certificate_3_0_1_4 h
  · exact b65e_tensorWeight_certificate_3_0_1_5 h
  · exact b65e_tensorWeight_certificate_3_1_0_0 h
  · exact b65e_tensorWeight_certificate_3_1_0_1 h
  · exact b65e_tensorWeight_certificate_3_1_0_2 h
  · exact b65e_tensorWeight_certificate_3_1_0_3 h
  · exact b65e_tensorWeight_certificate_3_1_0_4 h
  · exact b65e_tensorWeight_certificate_3_1_0_5 h
  · exact b65e_tensorWeight_certificate_3_1_1_0 h
  · exact b65e_tensorWeight_certificate_3_1_1_1 h
  · exact b65e_tensorWeight_certificate_3_1_1_2 h
  · exact b65e_tensorWeight_certificate_3_1_1_3 h
  · exact b65e_tensorWeight_certificate_3_1_1_4 h
  · exact b65e_tensorWeight_certificate_3_1_1_5 h
  · exact b65e_tensorWeight_certificate_4_0_0_0 h
  · exact b65e_tensorWeight_certificate_4_0_0_1 h
  · exact b65e_tensorWeight_certificate_4_0_0_2 h
  · exact b65e_tensorWeight_certificate_4_0_0_3 h
  · exact b65e_tensorWeight_certificate_4_0_0_4 h
  · exact b65e_tensorWeight_certificate_4_0_0_5 h
  · exact b65e_tensorWeight_certificate_4_0_1_0 h
  · exact b65e_tensorWeight_certificate_4_0_1_1 h
  · exact b65e_tensorWeight_certificate_4_0_1_2 h
  · exact b65e_tensorWeight_certificate_4_0_1_3 h
  · exact b65e_tensorWeight_certificate_4_0_1_4 h
  · exact b65e_tensorWeight_certificate_4_0_1_5 h
  · exact b65e_tensorWeight_certificate_4_1_0_0 h
  · exact b65e_tensorWeight_certificate_4_1_0_1 h
  · exact b65e_tensorWeight_certificate_4_1_0_2 h
  · exact b65e_tensorWeight_certificate_4_1_0_3 h
  · exact b65e_tensorWeight_certificate_4_1_0_4 h
  · exact b65e_tensorWeight_certificate_4_1_0_5 h
  · exact b65e_tensorWeight_certificate_4_1_1_0 h
  · exact b65e_tensorWeight_certificate_4_1_1_1 h
  · exact b65e_tensorWeight_certificate_4_1_1_2 h
  · exact b65e_tensorWeight_certificate_4_1_1_3 h
  · exact b65e_tensorWeight_certificate_4_1_1_4 h
  · exact b65e_tensorWeight_certificate_4_1_1_5 h
  · exact b65e_tensorWeight_certificate_5_0_0_0 h
  · exact b65e_tensorWeight_certificate_5_0_0_1 h
  · exact b65e_tensorWeight_certificate_5_0_0_2 h
  · exact b65e_tensorWeight_certificate_5_0_0_3 h
  · exact b65e_tensorWeight_certificate_5_0_0_4 h
  · exact b65e_tensorWeight_certificate_5_0_0_5 h
  · exact b65e_tensorWeight_certificate_5_0_1_0 h
  · exact b65e_tensorWeight_certificate_5_0_1_1 h
  · exact b65e_tensorWeight_certificate_5_0_1_2 h
  · exact b65e_tensorWeight_certificate_5_0_1_3 h
  · exact b65e_tensorWeight_certificate_5_0_1_4 h
  · exact b65e_tensorWeight_certificate_5_0_1_5 h
  · exact b65e_tensorWeight_certificate_5_1_0_0 h
  · exact b65e_tensorWeight_certificate_5_1_0_1 h
  · exact b65e_tensorWeight_certificate_5_1_0_2 h
  · exact b65e_tensorWeight_certificate_5_1_0_3 h
  · exact b65e_tensorWeight_certificate_5_1_0_4 h
  · exact b65e_tensorWeight_certificate_5_1_0_5 h
  · exact b65e_tensorWeight_certificate_5_1_1_0 h
  · exact b65e_tensorWeight_certificate_5_1_1_1 h
  · exact b65e_tensorWeight_certificate_5_1_1_2 h
  · exact b65e_tensorWeight_certificate_5_1_1_3 h
  · exact b65e_tensorWeight_certificate_5_1_1_4 h
  · exact b65e_tensorWeight_certificate_5_1_1_5 h
  · exact b65e_tensorWeight_certificate_6_0_0_0 h
  · exact b65e_tensorWeight_certificate_6_0_0_1 h
  · exact b65e_tensorWeight_certificate_6_0_0_2 h
  · exact b65e_tensorWeight_certificate_6_0_0_3 h
  · exact b65e_tensorWeight_certificate_6_0_0_4 h
  · exact b65e_tensorWeight_certificate_6_0_0_5 h
  · exact b65e_tensorWeight_certificate_6_0_1_0 h
  · exact b65e_tensorWeight_certificate_6_0_1_1 h
  · exact b65e_tensorWeight_certificate_6_0_1_2 h
  · exact b65e_tensorWeight_certificate_6_0_1_3 h
  · exact b65e_tensorWeight_certificate_6_0_1_4 h
  · exact b65e_tensorWeight_certificate_6_0_1_5 h
  · exact b65e_tensorWeight_certificate_6_1_0_0 h
  · exact b65e_tensorWeight_certificate_6_1_0_1 h
  · exact b65e_tensorWeight_certificate_6_1_0_2 h
  · exact b65e_tensorWeight_certificate_6_1_0_3 h
  · exact b65e_tensorWeight_certificate_6_1_0_4 h
  · exact b65e_tensorWeight_certificate_6_1_0_5 h
  · exact b65e_tensorWeight_certificate_6_1_1_0 h
  · exact b65e_tensorWeight_certificate_6_1_1_1 h
  · exact b65e_tensorWeight_certificate_6_1_1_2 h
  · exact b65e_tensorWeight_certificate_6_1_1_3 h
  · exact b65e_tensorWeight_certificate_6_1_1_4 h
  · exact b65e_tensorWeight_certificate_6_1_1_5 h

end HodgeLean.Foundations.Program
