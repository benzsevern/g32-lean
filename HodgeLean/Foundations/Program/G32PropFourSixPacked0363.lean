import HodgeLean.Foundations.Program.G32PropFourSixPacked0362
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow14
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_row13_classSupport) :
    g32p_literalTraceValue (g32p_row13_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_row13_classSupport →
    g32p_literalTraceValue (g32p_row13_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row13_zeroTrace_block_00 r k
  · exact g32p_row13_zeroTrace_block_01 r k
  · exact g32p_row13_zeroTrace_block_02 r k
  · exact g32p_row13_zeroTrace_block_03 r k
  · exact g32p_row13_zeroTrace_block_04 r k
  · exact g32p_row13_zeroTrace_block_05 r k
  · exact g32p_row13_zeroTrace_block_06 r k

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_row13_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_row13_classSupport) :
    (g32p_recordedInductionGenerators (g32p_row13_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row13_generatorIndex k) c) := by
  rw [g32p_row13_recordedGenerator_zero c hc k, g32p_row13_zeroTrace_arithmetic c k hc]
  norm_num [HurwitzPrymRex_ev]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 0) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 0) (g32p_literalTraceValue 12 0)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row13_traceCoefficients_000]
  decide +kernel

theorem g32p_row13_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 5 = [0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 5) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 5) (g32p_literalTraceValue 12 5)
      [1, 0, -1, 0, 1] [0, 0, 0, 288, 0, 288] = true := by
  rw [g32p_row13_traceCoefficients_005]
  decide +kernel

theorem g32p_row13_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 7 = [0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 7) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 7) (g32p_literalTraceValue 12 7)
      [1, 0, -1, 0, 1] [0, 72, 0, 72] = true := by
  rw [g32p_row13_traceCoefficients_007]
  decide +kernel

theorem g32p_row13_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 18 = [1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 18) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 18) (g32p_literalTraceValue 12 18)
      [1, 0, -1, 0, 1] [1728, 0, 1728] = true := by
  rw [g32p_row13_traceCoefficients_018]
  decide +kernel

theorem g32p_row13_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 19 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 19) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 19) (g32p_literalTraceValue 12 19)
      [1, 0, -1, 0, 1] [-432] = true := by
  rw [g32p_row13_traceCoefficients_019]
  decide +kernel

theorem g32p_row13_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 20 = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 20) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 20) (g32p_literalTraceValue 12 20)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 0, 72, 0, 72] = true := by
  rw [g32p_row13_traceCoefficients_020]
  decide +kernel

theorem g32p_row13_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 23 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 23) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 23) (g32p_literalTraceValue 12 23)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 432, 0, 432] = true := by
  rw [g32p_row13_traceCoefficients_023]
  decide +kernel

theorem g32p_row13_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 41 = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 41) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 41) (g32p_literalTraceValue 12 41)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 0, 72, 0, 72] = true := by
  rw [g32p_row13_traceCoefficients_041]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 44 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 44) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 44) (g32p_literalTraceValue 12 44)
      [1, 0, -1, 0, 1] [-3888] = true := by
  rw [g32p_row13_traceCoefficients_044]
  decide +kernel

theorem g32p_row13_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 67 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 67) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 67) (g32p_literalTraceValue 12 67)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row13_traceCoefficients_067]
  decide +kernel

theorem g32p_row13_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 72 = [0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 72) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 72) (g32p_literalTraceValue 12 72)
      [1, 0, -1, 0, 1] [0, 72, 0, 72] = true := by
  rw [g32p_row13_traceCoefficients_072]
  decide +kernel

theorem g32p_row13_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 76 = [0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 76) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 76) (g32p_literalTraceValue 12 76)
      [1, 0, -1, 0, 1] [3888, 0, 3888, 0, 3888] = true := by
  rw [g32p_row13_traceCoefficients_076]
  decide +kernel

theorem g32p_row13_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 77 = [0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 77) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 77) (g32p_literalTraceValue 12 77)
      [1, 0, -1, 0, 1] [432, 0, 432, 0, 432] = true := by
  rw [g32p_row13_traceCoefficients_077]
  decide +kernel

theorem g32p_row13_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 79 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 79) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 79) (g32p_literalTraceValue 12 79)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row13_traceCoefficients_079]
  decide +kernel

theorem g32p_row13_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 94 = [0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 94) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 94) (g32p_literalTraceValue 12 94)
      [1, 0, -1, 0, 1] [0, 0, 0, 288, 0, 288] = true := by
  rw [g32p_row13_traceCoefficients_094]
  decide +kernel

theorem g32p_row13_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 95 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 95) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 95) (g32p_literalTraceValue 12 95)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 3888, 0, 3888] = true := by
  rw [g32p_row13_traceCoefficients_095]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 99 = [0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row13_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 99) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) 99) (g32p_literalTraceValue 12 99)
      [1, 0, -1, 0, 1] [155520, 0, 155520] = true := by
  rw [g32p_row13_traceCoefficients_099]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row13_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else [0, 0, 0, 288, 0, 288]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [0, 72, 0, 72] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [1728, 0, 1728] else (if i.val < 20 then [-432] else [0, 0, 0, 0, 0, 72, 0, 72])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [0, 0, 0, 0, 432, 0, 432] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [0, 0, 0, 0, 0, 72, 0, 72] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [-3888] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [0, 72, 0, 72] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [3888, 0, 3888, 0, 3888] else (if i.val < 78 then [432, 0, 432, 0, 432] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [0, 0, 0, 288, 0, 288]))) else (if i.val < 98 then (if i.val < 96 then [0, 0, 0, 0, 3888, 0, 3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else [155520, 0, 155520]) else (if i.val < 101 then [] else [])))))))

theorem g32p_row13_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_row13_classSupport) :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer c) 12
      (g32p_supplierTraceCoefficients g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) c) (g32p_literalTraceValue 12 c)
      [1, 0, -1, 0, 1] (g32p_row13_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row13_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_007
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_018
  · exact g32p_row13_tracePolynomial_019
  · exact g32p_row13_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_044
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_076
  · exact g32p_row13_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_094
  · exact g32p_row13_tracePolynomial_095
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact g32p_row13_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_row13_classSupport) hc)
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_row13_classSupport) hc)

theorem g32p_row13_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 12 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 12 c) := by
  by_cases hc : c ∈ g32p_row13_classSupport
  · have hclass (j : Fin 24) :
        IsConj (g32p_literalRepresentative c) (g32p_row13_groupEquiv j : g32p_G) ↔
          g32p_row13_supplierClassifier j = c := by
      simpa only [g32p_row13_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row13_supplierClass_iff (g32p_row13_groupEquiv j) c
    have hχ (j : Fin 24) :
        (g32p_recordedSupplierCharacters 12 (g32p_row13_groupEquiv j) : ℂ) =
          g32p_root 12 ^ (Multiplicative.toAdd (g32p_row13_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 12 (show (g32p_recordedSuppliers 12).H from g32p_row13_groupEquiv j)]
      change g32p_root 12 ^ (Multiplicative.toAdd
        (g32p_row13_characterValues (g32p_row13_groupEquiv.symm (g32p_row13_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 12).H (g32p_recordedSupplierCharacters 12)
      (g32p_literalRepresentative c) g32p_row13_groupEquiv g32p_row13_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row13_characterValues j)).val) c 12 24
      (g32p_literalCentralizer c) (g32p_literalTraceValue 12 c) [1, 0, -1, 0, 1]
      (g32p_row13_traceQuotient c) (g32p_root 12) (by decide)
      g32p_row13_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_twelve
        (g32p_root_primitive (g32p_recordedSuppliers 12)))
      (g32p_row13_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 12 (by decide)] at h
    exact h
  · exact g32p_row13_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row13_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_0 r
  · exact g32p_row13_variantArithmetic_01_0 r
  · exact g32p_row13_variantArithmetic_02_0 r
  · exact g32p_row13_variantArithmetic_03_0 r
  · exact g32p_row13_variantArithmetic_04_0 r
  · exact g32p_row13_variantArithmetic_05_0 r
  · exact g32p_row13_variantArithmetic_06_0 r

theorem g32p_row13_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_1 r
  · exact g32p_row13_variantArithmetic_01_1 r
  · exact g32p_row13_variantArithmetic_02_1 r
  · exact g32p_row13_variantArithmetic_03_1 r
  · exact g32p_row13_variantArithmetic_04_1 r
  · exact g32p_row13_variantArithmetic_05_1 r
  · exact g32p_row13_variantArithmetic_06_1 r

theorem g32p_row13_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_2 r
  · exact g32p_row13_variantArithmetic_01_2 r
  · exact g32p_row13_variantArithmetic_02_2 r
  · exact g32p_row13_variantArithmetic_03_2 r
  · exact g32p_row13_variantArithmetic_04_2 r
  · exact g32p_row13_variantArithmetic_05_2 r
  · exact g32p_row13_variantArithmetic_06_2 r

theorem g32p_row13_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_3 r
  · exact g32p_row13_variantArithmetic_01_3 r
  · exact g32p_row13_variantArithmetic_02_3 r
  · exact g32p_row13_variantArithmetic_03_3 r
  · exact g32p_row13_variantArithmetic_04_3 r
  · exact g32p_row13_variantArithmetic_05_3 r
  · exact g32p_row13_variantArithmetic_06_3 r

theorem g32p_row13_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_4 r
  · exact g32p_row13_variantArithmetic_01_4 r
  · exact g32p_row13_variantArithmetic_02_4 r
  · exact g32p_row13_variantArithmetic_03_4 r
  · exact g32p_row13_variantArithmetic_04_4 r
  · exact g32p_row13_variantArithmetic_05_4 r
  · exact g32p_row13_variantArithmetic_06_4 r

theorem g32p_row13_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_5 r
  · exact g32p_row13_variantArithmetic_01_5 r
  · exact g32p_row13_variantArithmetic_02_5 r
  · exact g32p_row13_variantArithmetic_03_5 r
  · exact g32p_row13_variantArithmetic_04_5 r
  · exact g32p_row13_variantArithmetic_05_5 r
  · exact g32p_row13_variantArithmetic_06_5 r

theorem g32p_row13_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_6 r
  · exact g32p_row13_variantArithmetic_01_6 r
  · exact g32p_row13_variantArithmetic_02_6 r
  · exact g32p_row13_variantArithmetic_03_6 r
  · exact g32p_row13_variantArithmetic_04_6 r
  · exact g32p_row13_variantArithmetic_05_6 r
  · exact g32p_row13_variantArithmetic_06_6 r

theorem g32p_row13_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row13_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 12 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row13_variantArithmetic_00_7 r
  · exact g32p_row13_variantArithmetic_01_7 r
  · exact g32p_row13_variantArithmetic_02_7 r
  · exact g32p_row13_variantArithmetic_03_7 r
  · exact g32p_row13_variantArithmetic_04_7 r
  · exact g32p_row13_variantArithmetic_05_7 r
  · exact g32p_row13_variantArithmetic_06_7 r

theorem g32p_row13_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row13_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row13_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 12 c _ (g32p_row13_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row13_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup09_source : Fin 24 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (1, 223) else (85, 101))) else (if i.val < 4 then (0, 99) else (if i.val < 5 then (2, 129) else (130, 212)))) else (if i.val < 9 then (if i.val < 7 then (82, 22) else (if i.val < 8 then (78, 188) else (15, 30))) else (if i.val < 10 then (31, 212) else (if i.val < 11 then (48, 55) else (54, 126))))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then (139, 81) else (if i.val < 14 then (7, 250) else (13, 97))) else (if i.val < 16 then (141, 173) else (if i.val < 17 then (54, 187) else (28, 193)))) else (if i.val < 21 then (if i.val < 19 then (70, 77) else (if i.val < 20 then (134, 51) else (105, 163))) else (if i.val < 22 then (58, 214) else (if i.val < 23 then (116, 124) else (133, 250))))))

def g32p_supplierGroup09_classify : Fin 24 → Fin 102 :=
  fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 5 else 100)) else (if i.val < 4 then 99 else (if i.val < 5 then 18 else 55))) else (if i.val < 9 then (if i.val < 7 then 94 else (if i.val < 8 then 87 else 28)) else (if i.val < 10 then 5 else (if i.val < 11 then 51 else 18)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 61 else (if i.val < 14 then 27 else 88)) else (if i.val < 16 then 55 else (if i.val < 17 then 94 else 91))) else (if i.val < 21 then (if i.val < 19 then 85 else (if i.val < 20 then 17 else 61)) else (if i.val < 22 then 27 else (if i.val < 23 then 64 else 17)))))

def g32p_supplierGroup09_support : Finset (Fin 102) :=
  {0, 5, 17, 18, 27, 28, 51, 55, 61, 64, 85, 87, 88, 91, 94, 99, 100}

end HodgeLean.Foundations.Program

end
end
