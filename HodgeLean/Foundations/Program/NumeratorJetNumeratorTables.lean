import HodgeLean.Foundations.Program.NumeratorJetMomentFibre0Comp0
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre0Comp1
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre0Comp2
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre0Comp3
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre1Comp0
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre1Comp1
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre1Comp2
import HodgeLean.Foundations.Program.NumeratorJetMomentFibre1Comp3
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace0
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace1
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace2
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace3
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace4
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace5
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace6
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace7
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace8
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace9
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace10
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace11
import HodgeLean.Foundations.Program.NumeratorJetMomentTrace12
import HodgeLean.Foundations.Program.NumeratorJetQPart0
import HodgeLean.Foundations.Program.NumeratorJetQPart1
import HodgeLean.Foundations.Program.NumeratorJetQPart2
import HodgeLean.Foundations.Program.NumeratorJetQPart3
import HodgeLean.Foundations.Program.NumeratorJetQPart4
import HodgeLean.Foundations.Program.NumeratorJetQPart5
import HodgeLean.Foundations.Program.NumeratorJetQPart6
import HodgeLean.Foundations.Program.NumeratorJetQPart7
import HodgeLean.Foundations.Program.NumeratorJetQPart8
import HodgeLean.Foundations.Program.NumeratorJetQPart9
import HodgeLean.Foundations.Program.NumeratorJetQPart10
import HodgeLean.Foundations.Program.NumeratorJetQPart11
import HodgeLean.Foundations.Program.NumeratorJetQPart12
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder0
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder1
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder2
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder3
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder4
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder5
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder6
import HodgeLean.Foundations.Program.NumeratorJetNumeratorOrder7

/-! # Assembled table checks for the numerator jets -/

namespace HodgeLean.Foundations.Program

/-- All moving-moment coordinates satisfy their convolution formula. -/
theorem b65e_WT_table : ∀ e jj (m : Fin 13) (n : Fin 8) c,
    b65e_WTQ e jj m n c = b65e_WTFormulaQ e jj m n c := by
  intro e jj m n c
  fin_cases e <;> fin_cases jj <;> fin_cases m
  · exact b65e_WT_table_0_0_0 n c
  · exact b65e_WT_table_0_0_1 n c
  · exact b65e_WT_table_0_0_2 n c
  · exact b65e_WT_table_0_0_3 n c
  · exact b65e_WT_table_0_0_4 n c
  · exact b65e_WT_table_0_0_5 n c
  · exact b65e_WT_table_0_0_6 n c
  · exact b65e_WT_table_0_0_7 n c
  · exact b65e_WT_table_0_0_8 n c
  · exact b65e_WT_table_0_0_9 n c
  · exact b65e_WT_table_0_0_10 n c
  · exact b65e_WT_table_0_0_11 n c
  · exact b65e_WT_table_0_0_12 n c
  · exact b65e_WT_table_0_1_0 n c
  · exact b65e_WT_table_0_1_1 n c
  · exact b65e_WT_table_0_1_2 n c
  · exact b65e_WT_table_0_1_3 n c
  · exact b65e_WT_table_0_1_4 n c
  · exact b65e_WT_table_0_1_5 n c
  · exact b65e_WT_table_0_1_6 n c
  · exact b65e_WT_table_0_1_7 n c
  · exact b65e_WT_table_0_1_8 n c
  · exact b65e_WT_table_0_1_9 n c
  · exact b65e_WT_table_0_1_10 n c
  · exact b65e_WT_table_0_1_11 n c
  · exact b65e_WT_table_0_1_12 n c
  · exact b65e_WT_table_0_2_0 n c
  · exact b65e_WT_table_0_2_1 n c
  · exact b65e_WT_table_0_2_2 n c
  · exact b65e_WT_table_0_2_3 n c
  · exact b65e_WT_table_0_2_4 n c
  · exact b65e_WT_table_0_2_5 n c
  · exact b65e_WT_table_0_2_6 n c
  · exact b65e_WT_table_0_2_7 n c
  · exact b65e_WT_table_0_2_8 n c
  · exact b65e_WT_table_0_2_9 n c
  · exact b65e_WT_table_0_2_10 n c
  · exact b65e_WT_table_0_2_11 n c
  · exact b65e_WT_table_0_2_12 n c
  · exact b65e_WT_table_0_3_0 n c
  · exact b65e_WT_table_0_3_1 n c
  · exact b65e_WT_table_0_3_2 n c
  · exact b65e_WT_table_0_3_3 n c
  · exact b65e_WT_table_0_3_4 n c
  · exact b65e_WT_table_0_3_5 n c
  · exact b65e_WT_table_0_3_6 n c
  · exact b65e_WT_table_0_3_7 n c
  · exact b65e_WT_table_0_3_8 n c
  · exact b65e_WT_table_0_3_9 n c
  · exact b65e_WT_table_0_3_10 n c
  · exact b65e_WT_table_0_3_11 n c
  · exact b65e_WT_table_0_3_12 n c
  · exact b65e_WT_table_1_0_0 n c
  · exact b65e_WT_table_1_0_1 n c
  · exact b65e_WT_table_1_0_2 n c
  · exact b65e_WT_table_1_0_3 n c
  · exact b65e_WT_table_1_0_4 n c
  · exact b65e_WT_table_1_0_5 n c
  · exact b65e_WT_table_1_0_6 n c
  · exact b65e_WT_table_1_0_7 n c
  · exact b65e_WT_table_1_0_8 n c
  · exact b65e_WT_table_1_0_9 n c
  · exact b65e_WT_table_1_0_10 n c
  · exact b65e_WT_table_1_0_11 n c
  · exact b65e_WT_table_1_0_12 n c
  · exact b65e_WT_table_1_1_0 n c
  · exact b65e_WT_table_1_1_1 n c
  · exact b65e_WT_table_1_1_2 n c
  · exact b65e_WT_table_1_1_3 n c
  · exact b65e_WT_table_1_1_4 n c
  · exact b65e_WT_table_1_1_5 n c
  · exact b65e_WT_table_1_1_6 n c
  · exact b65e_WT_table_1_1_7 n c
  · exact b65e_WT_table_1_1_8 n c
  · exact b65e_WT_table_1_1_9 n c
  · exact b65e_WT_table_1_1_10 n c
  · exact b65e_WT_table_1_1_11 n c
  · exact b65e_WT_table_1_1_12 n c
  · exact b65e_WT_table_1_2_0 n c
  · exact b65e_WT_table_1_2_1 n c
  · exact b65e_WT_table_1_2_2 n c
  · exact b65e_WT_table_1_2_3 n c
  · exact b65e_WT_table_1_2_4 n c
  · exact b65e_WT_table_1_2_5 n c
  · exact b65e_WT_table_1_2_6 n c
  · exact b65e_WT_table_1_2_7 n c
  · exact b65e_WT_table_1_2_8 n c
  · exact b65e_WT_table_1_2_9 n c
  · exact b65e_WT_table_1_2_10 n c
  · exact b65e_WT_table_1_2_11 n c
  · exact b65e_WT_table_1_2_12 n c
  · exact b65e_WT_table_1_3_0 n c
  · exact b65e_WT_table_1_3_1 n c
  · exact b65e_WT_table_1_3_2 n c
  · exact b65e_WT_table_1_3_3 n c
  · exact b65e_WT_table_1_3_4 n c
  · exact b65e_WT_table_1_3_5 n c
  · exact b65e_WT_table_1_3_6 n c
  · exact b65e_WT_table_1_3_7 n c
  · exact b65e_WT_table_1_3_8 n c
  · exact b65e_WT_table_1_3_9 n c
  · exact b65e_WT_table_1_3_10 n c
  · exact b65e_WT_table_1_3_11 n c
  · exact b65e_WT_table_1_3_12 n c

/-- All traced moving moments satisfy their formula. -/
theorem b65e_Sq_table : ∀ (m : Fin 13) jj b (n : Fin 8),
    b65e_SqQ m jj b n = b65e_SqFormulaQ m jj b n := by
  intro m jj b n
  fin_cases m <;> fin_cases jj
  · exact b65e_Sq_table_0_0 b n
  · exact b65e_Sq_table_0_1 b n
  · exact b65e_Sq_table_0_2 b n
  · exact b65e_Sq_table_0_3 b n
  · exact b65e_Sq_table_1_0 b n
  · exact b65e_Sq_table_1_1 b n
  · exact b65e_Sq_table_1_2 b n
  · exact b65e_Sq_table_1_3 b n
  · exact b65e_Sq_table_2_0 b n
  · exact b65e_Sq_table_2_1 b n
  · exact b65e_Sq_table_2_2 b n
  · exact b65e_Sq_table_2_3 b n
  · exact b65e_Sq_table_3_0 b n
  · exact b65e_Sq_table_3_1 b n
  · exact b65e_Sq_table_3_2 b n
  · exact b65e_Sq_table_3_3 b n
  · exact b65e_Sq_table_4_0 b n
  · exact b65e_Sq_table_4_1 b n
  · exact b65e_Sq_table_4_2 b n
  · exact b65e_Sq_table_4_3 b n
  · exact b65e_Sq_table_5_0 b n
  · exact b65e_Sq_table_5_1 b n
  · exact b65e_Sq_table_5_2 b n
  · exact b65e_Sq_table_5_3 b n
  · exact b65e_Sq_table_6_0 b n
  · exact b65e_Sq_table_6_1 b n
  · exact b65e_Sq_table_6_2 b n
  · exact b65e_Sq_table_6_3 b n
  · exact b65e_Sq_table_7_0 b n
  · exact b65e_Sq_table_7_1 b n
  · exact b65e_Sq_table_7_2 b n
  · exact b65e_Sq_table_7_3 b n
  · exact b65e_Sq_table_8_0 b n
  · exact b65e_Sq_table_8_1 b n
  · exact b65e_Sq_table_8_2 b n
  · exact b65e_Sq_table_8_3 b n
  · exact b65e_Sq_table_9_0 b n
  · exact b65e_Sq_table_9_1 b n
  · exact b65e_Sq_table_9_2 b n
  · exact b65e_Sq_table_9_3 b n
  · exact b65e_Sq_table_10_0 b n
  · exact b65e_Sq_table_10_1 b n
  · exact b65e_Sq_table_10_2 b n
  · exact b65e_Sq_table_10_3 b n
  · exact b65e_Sq_table_11_0 b n
  · exact b65e_Sq_table_11_1 b n
  · exact b65e_Sq_table_11_2 b n
  · exact b65e_Sq_table_11_3 b n
  · exact b65e_Sq_table_12_0 b n
  · exact b65e_Sq_table_12_1 b n
  · exact b65e_Sq_table_12_2 b n
  · exact b65e_Sq_table_12_3 b n

/-- All polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table : ∀ (k : Fin 13) jj b (n : Fin 8),
    b65e_GQ k jj b n = b65e_GFormulaQ k jj b n := by
  intro k jj b n
  fin_cases k <;> fin_cases jj
  · exact b65e_G_table_0_0 b n
  · exact b65e_G_table_0_1 b n
  · exact b65e_G_table_0_2 b n
  · exact b65e_G_table_0_3 b n
  · exact b65e_G_table_1_0 b n
  · exact b65e_G_table_1_1 b n
  · exact b65e_G_table_1_2 b n
  · exact b65e_G_table_1_3 b n
  · exact b65e_G_table_2_0 b n
  · exact b65e_G_table_2_1 b n
  · exact b65e_G_table_2_2 b n
  · exact b65e_G_table_2_3 b n
  · exact b65e_G_table_3_0 b n
  · exact b65e_G_table_3_1 b n
  · exact b65e_G_table_3_2 b n
  · exact b65e_G_table_3_3 b n
  · exact b65e_G_table_4_0 b n
  · exact b65e_G_table_4_1 b n
  · exact b65e_G_table_4_2 b n
  · exact b65e_G_table_4_3 b n
  · exact b65e_G_table_5_0 b n
  · exact b65e_G_table_5_1 b n
  · exact b65e_G_table_5_2 b n
  · exact b65e_G_table_5_3 b n
  · exact b65e_G_table_6_0 b n
  · exact b65e_G_table_6_1 b n
  · exact b65e_G_table_6_2 b n
  · exact b65e_G_table_6_3 b n
  · exact b65e_G_table_7_0 b n
  · exact b65e_G_table_7_1 b n
  · exact b65e_G_table_7_2 b n
  · exact b65e_G_table_7_3 b n
  · exact b65e_G_table_8_0 b n
  · exact b65e_G_table_8_1 b n
  · exact b65e_G_table_8_2 b n
  · exact b65e_G_table_8_3 b n
  · exact b65e_G_table_9_0 b n
  · exact b65e_G_table_9_1 b n
  · exact b65e_G_table_9_2 b n
  · exact b65e_G_table_9_3 b n
  · exact b65e_G_table_10_0 b n
  · exact b65e_G_table_10_1 b n
  · exact b65e_G_table_10_2 b n
  · exact b65e_G_table_10_3 b n
  · exact b65e_G_table_11_0 b n
  · exact b65e_G_table_11_1 b n
  · exact b65e_G_table_11_2 b n
  · exact b65e_G_table_11_3 b n
  · exact b65e_G_table_12_0 b n
  · exact b65e_G_table_12_1 b n
  · exact b65e_G_table_12_2 b n
  · exact b65e_G_table_12_3 b n

/-- All stored numerator jets satisfy the product formula. -/
theorem b65e_N_table : ∀ (n : Fin 8) (a b : Fin 3) (j : Fin 10),
    b65e_N n (finProdFinEquiv (a, b)) j = b65e_NFormulaQ n a b j := by
  intro n a b j
  fin_cases n <;> fin_cases a <;> fin_cases b
  · exact b65e_N_table_0_0_0 j
  · exact b65e_N_table_0_0_1 j
  · exact b65e_N_table_0_0_2 j
  · exact b65e_N_table_0_1_0 j
  · exact b65e_N_table_0_1_1 j
  · exact b65e_N_table_0_1_2 j
  · exact b65e_N_table_0_2_0 j
  · exact b65e_N_table_0_2_1 j
  · exact b65e_N_table_0_2_2 j
  · exact b65e_N_table_1_0_0 j
  · exact b65e_N_table_1_0_1 j
  · exact b65e_N_table_1_0_2 j
  · exact b65e_N_table_1_1_0 j
  · exact b65e_N_table_1_1_1 j
  · exact b65e_N_table_1_1_2 j
  · exact b65e_N_table_1_2_0 j
  · exact b65e_N_table_1_2_1 j
  · exact b65e_N_table_1_2_2 j
  · exact b65e_N_table_2_0_0 j
  · exact b65e_N_table_2_0_1 j
  · exact b65e_N_table_2_0_2 j
  · exact b65e_N_table_2_1_0 j
  · exact b65e_N_table_2_1_1 j
  · exact b65e_N_table_2_1_2 j
  · exact b65e_N_table_2_2_0 j
  · exact b65e_N_table_2_2_1 j
  · exact b65e_N_table_2_2_2 j
  · exact b65e_N_table_3_0_0 j
  · exact b65e_N_table_3_0_1 j
  · exact b65e_N_table_3_0_2 j
  · exact b65e_N_table_3_1_0 j
  · exact b65e_N_table_3_1_1 j
  · exact b65e_N_table_3_1_2 j
  · exact b65e_N_table_3_2_0 j
  · exact b65e_N_table_3_2_1 j
  · exact b65e_N_table_3_2_2 j
  · exact b65e_N_table_4_0_0 j
  · exact b65e_N_table_4_0_1 j
  · exact b65e_N_table_4_0_2 j
  · exact b65e_N_table_4_1_0 j
  · exact b65e_N_table_4_1_1 j
  · exact b65e_N_table_4_1_2 j
  · exact b65e_N_table_4_2_0 j
  · exact b65e_N_table_4_2_1 j
  · exact b65e_N_table_4_2_2 j
  · exact b65e_N_table_5_0_0 j
  · exact b65e_N_table_5_0_1 j
  · exact b65e_N_table_5_0_2 j
  · exact b65e_N_table_5_1_0 j
  · exact b65e_N_table_5_1_1 j
  · exact b65e_N_table_5_1_2 j
  · exact b65e_N_table_5_2_0 j
  · exact b65e_N_table_5_2_1 j
  · exact b65e_N_table_5_2_2 j
  · exact b65e_N_table_6_0_0 j
  · exact b65e_N_table_6_0_1 j
  · exact b65e_N_table_6_0_2 j
  · exact b65e_N_table_6_1_0 j
  · exact b65e_N_table_6_1_1 j
  · exact b65e_N_table_6_1_2 j
  · exact b65e_N_table_6_2_0 j
  · exact b65e_N_table_6_2_1 j
  · exact b65e_N_table_6_2_2 j
  · exact b65e_N_table_7_0_0 j
  · exact b65e_N_table_7_0_1 j
  · exact b65e_N_table_7_0_2 j
  · exact b65e_N_table_7_1_0 j
  · exact b65e_N_table_7_1_1 j
  · exact b65e_N_table_7_1_2 j
  · exact b65e_N_table_7_2_0 j
  · exact b65e_N_table_7_2_1 j
  · exact b65e_N_table_7_2_2 j

end HodgeLean.Foundations.Program
