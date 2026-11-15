import HodgeLean.Foundations.Program.G32PropFourSixPacked0344
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row05_supplierClassifier : Fin 486 → Fin 102 := g32p_supplierGroup03_classify

theorem g32p_row05_groupEquiv_isConj (i : Fin 486) :
    IsConj (g32p_row05_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row05_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup03_source i).1 (g32p_supplierGroup03_source i).2
  rw [g32p_supplierGroup03_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row05_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup03_matrix i)

def g32p_row05_supplierClass (h : (g32p_recordedSuppliers 4).H) : Fin 102 :=
  g32p_row05_supplierClassifier (g32p_row05_groupEquiv.symm h)

theorem g32p_row05_supplierClass_isConj (h : (g32p_recordedSuppliers 4).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row05_supplierClass h)) := by
  have he : (g32p_row05_groupEquiv (g32p_row05_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 4).H => (a : g32p_G))
      (g32p_row05_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row05_supplierClassifier (g32p_row05_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row05_groupEquiv_isConj (g32p_row05_groupEquiv.symm h)

theorem g32p_row05_supplierClass_iff (h : (g32p_recordedSuppliers 4).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row05_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row05_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row05_supplierClass_isConj h).symm

theorem g32p_row05_supplierClass_mem_support (h : (g32p_recordedSuppliers 4).H) :
    g32p_row05_supplierClass h ∈ g32p_supplierGroup03_support :=
  g32p_supplierGroup03_support_mem (g32p_row05_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row05_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 0) (g32p_literalTraceValue 4 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_000]
  decide +kernel

theorem g32p_row05_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 1 = [1, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 1) (g32p_literalTraceValue 4 1)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_001]
  decide +kernel

theorem g32p_row05_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 2 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 2) (g32p_literalTraceValue 4 2)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row05_traceCoefficients_002]
  decide +kernel

theorem g32p_row05_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 3 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 3) (g32p_literalTraceValue 4 3)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row05_traceCoefficients_003]
  decide +kernel

theorem g32p_row05_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 4 = [0, 3, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 4) (g32p_literalTraceValue 4 4)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row05_traceCoefficients_004]
  decide +kernel

theorem g32p_row05_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 6 = [24, 3, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 6) (g32p_literalTraceValue 4 6)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_006]
  decide +kernel

theorem g32p_row05_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 8 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 8) (g32p_literalTraceValue 4 8)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_008]
  decide +kernel

theorem g32p_row05_traceCoefficients_009 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 9 = [0, 18] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_009 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 9) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 9) (g32p_literalTraceValue 4 9)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_009]
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

theorem g32p_row05_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 10 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 10) (g32p_literalTraceValue 4 10)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_010]
  decide +kernel

theorem g32p_row05_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 11 = [0, 3, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 11) (g32p_literalTraceValue 4 11)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row05_traceCoefficients_011]
  decide +kernel

theorem g32p_row05_traceCoefficients_014 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 14 = [0, 0, 18] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_014 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 14) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 14) (g32p_literalTraceValue 4 14)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_014]
  decide +kernel

theorem g32p_row05_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 15 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 15) (g32p_literalTraceValue 4 15)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_015]
  decide +kernel

theorem g32p_row05_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 18 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 18) (g32p_literalTraceValue 4 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_018]
  decide +kernel

theorem g32p_row05_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 19 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 19) (g32p_literalTraceValue 4 19)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_019]
  decide +kernel

theorem g32p_row05_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 23 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 23) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 23) (g32p_literalTraceValue 4 23)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_023]
  decide +kernel

theorem g32p_row05_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 25 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 25) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 25) (g32p_literalTraceValue 4 25)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_025]
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

theorem g32p_row05_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 29 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 29) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 29) (g32p_literalTraceValue 4 29)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_029]
  decide +kernel

theorem g32p_row05_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 35 = [24, 3, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 35) (g32p_literalTraceValue 4 35)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_035]
  decide +kernel

theorem g32p_row05_traceCoefficients_036 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 36 = [0, 18] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_036 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 36) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 36) (g32p_literalTraceValue 4 36)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_036]
  decide +kernel

theorem g32p_row05_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 40 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 40) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 40) (g32p_literalTraceValue 4 40)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_040]
  decide +kernel

theorem g32p_row05_traceCoefficients_042 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 42 = [0, 18] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_042 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 42) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 42) (g32p_literalTraceValue 4 42)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_042]
  decide +kernel

theorem g32p_row05_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 43 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 43) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 43) (g32p_literalTraceValue 4 43)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_043]
  decide +kernel

theorem g32p_row05_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 45 = [24, 3, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 45) (g32p_literalTraceValue 4 45)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_045]
  decide +kernel

theorem g32p_row05_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 50 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 50) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 50) (g32p_literalTraceValue 4 50)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_050]
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

theorem g32p_row05_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 51 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 51) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 51) (g32p_literalTraceValue 4 51)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_051]
  decide +kernel

theorem g32p_row05_traceCoefficients_054 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 54 = [0, 0, 18] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_054 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 54) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 54) (g32p_literalTraceValue 4 54)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_054]
  decide +kernel

theorem g32p_row05_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 59 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 59) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 59) (g32p_literalTraceValue 4 59)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_059]
  decide +kernel

theorem g32p_row05_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 64 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 64) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 64) (g32p_literalTraceValue 4 64)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_064]
  decide +kernel

theorem g32p_row05_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 65 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 65) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 65) (g32p_literalTraceValue 4 65)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_065]
  decide +kernel

theorem g32p_row05_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 66 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 66) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 66) (g32p_literalTraceValue 4 66)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_066]
  decide +kernel

theorem g32p_row05_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 67 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 67) (g32p_literalTraceValue 4 67)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row05_traceCoefficients_067]
  decide +kernel

theorem g32p_row05_traceCoefficients_068 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 68 = [0, 0, 18] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_068 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 68) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 68) (g32p_literalTraceValue 4 68)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_068]
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

theorem g32p_row05_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 71 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 71) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 71) (g32p_literalTraceValue 4 71)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_071]
  decide +kernel

theorem g32p_row05_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 74 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 74) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 74) (g32p_literalTraceValue 4 74)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_074]
  decide +kernel

theorem g32p_row05_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 76 = [1, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 76) (g32p_literalTraceValue 4 76)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_076]
  decide +kernel

theorem g32p_row05_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 77 = [0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 77) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 77) (g32p_literalTraceValue 4 77)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_077]
  decide +kernel

theorem g32p_row05_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 78 = [0, 3, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 78) (g32p_literalTraceValue 4 78)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row05_traceCoefficients_078]
  decide +kernel

theorem g32p_row05_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 79 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 79) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 79) (g32p_literalTraceValue 4 79)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row05_traceCoefficients_079]
  decide +kernel

theorem g32p_row05_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 81 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 81) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 81) (g32p_literalTraceValue 4 81)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_081]
  decide +kernel

theorem g32p_row05_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 82 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 82) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 82) (g32p_literalTraceValue 4 82)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_082]
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

theorem g32p_row05_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 85 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 85) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 85) (g32p_literalTraceValue 4 85)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row05_traceCoefficients_085]
  decide +kernel

theorem g32p_row05_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 86 = [0, 0, 9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 86) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 86) (g32p_literalTraceValue 4 86)
      [1, 1, 1] [972] = true := by
  rw [g32p_row05_traceCoefficients_086]
  decide +kernel

theorem g32p_row05_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 87 = [1, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 87) (g32p_literalTraceValue 4 87)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_087]
  decide +kernel

theorem g32p_row05_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 89 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 89) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 89) (g32p_literalTraceValue 4 89)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_089]
  decide +kernel

theorem g32p_row05_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 91 = [9] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 91) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 91) (g32p_literalTraceValue 4 91)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_091]
  decide +kernel

theorem g32p_row05_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 96 = [1] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 96) (g32p_literalTraceValue 4 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_096]
  decide +kernel

theorem g32p_row05_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 100 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 100) (g32p_literalTraceValue 4 100)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row05_traceCoefficients_100]
  decide +kernel

theorem g32p_row05_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 101 = [1] := by
  decide +kernel

theorem g32p_row05_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) 101) (g32p_literalTraceValue 4 101)
      [1, 1, 1] [] = true := by
  rw [g32p_row05_traceCoefficients_101]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row05_generatorIndex : Fin 8 → Fin 408 :=
  ![4, 55, 106, 157, 212, 213, 314, 315]

theorem g32p_row05_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup03_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 4 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 4 g32p_row05_supplierClass
    g32p_row05_supplierClass_isConj g32p_supplierGroup03_support g32p_row05_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row05_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup03_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row05_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 4 c false (g32p_row05_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 4 c true (g32p_row05_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 4 c false (g32p_row05_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 4 c true (g32p_row05_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 4 c false (g32p_row05_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 4 c false (g32p_row05_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 4 c true (g32p_row05_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 4 c true (g32p_row05_coinduced_zero c hc true) 3

theorem g32p_row05_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup03_support →
      g32p_literalTraceValue (g32p_row05_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row05_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup03_support) :
    g32p_literalTraceValue (g32p_row05_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup03_support →
    g32p_literalTraceValue (g32p_row05_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row05_zeroTrace_block_00 r k
  · exact g32p_row05_zeroTrace_block_01 r k
  · exact g32p_row05_zeroTrace_block_02 r k
  · exact g32p_row05_zeroTrace_block_03 r k
  · exact g32p_row05_zeroTrace_block_04 r k
  · exact g32p_row05_zeroTrace_block_05 r k
  · exact g32p_row05_zeroTrace_block_06 r k

theorem g32p_row05_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup03_support) :
    (g32p_recordedInductionGenerators (g32p_row05_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row05_generatorIndex k) c) := by
  rw [g32p_row05_recordedGenerator_zero c hc k, g32p_row05_zeroTrace_arithmetic c k hc]
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
set_option backward.isDefEq.respectTransparency false

def g32p_row05_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [11664])) else (if i.val < 4 then [3888] else (if i.val < 5 then [1944] else []))) else (if i.val < 9 then (if i.val < 7 then [972] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [1944])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [972])) else (if i.val < 16 then [972] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [972] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [972]) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [972])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [972]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [972] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [972])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [972] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [11664] else [972]))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [1944])) else (if i.val < 80 then [3888] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [3888] else [972]) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [11664] else [])))))))

theorem g32p_row05_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup03_support) :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) c) (g32p_literalTraceValue 4 c)
      [1, 1, 1] (g32p_row05_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row05_tracePolynomial_000
  · exact g32p_row05_tracePolynomial_001
  · exact g32p_row05_tracePolynomial_002
  · exact g32p_row05_tracePolynomial_003
  · exact g32p_row05_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_008
  · exact g32p_row05_tracePolynomial_009
  · exact g32p_row05_tracePolynomial_010
  · exact g32p_row05_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_014
  · exact g32p_row05_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_018
  · exact g32p_row05_tracePolynomial_019
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_035
  · exact g32p_row05_tracePolynomial_036
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_042
  · exact g32p_row05_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_050
  · exact g32p_row05_tracePolynomial_051
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_054
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_064
  · exact g32p_row05_tracePolynomial_065
  · exact g32p_row05_tracePolynomial_066
  · exact g32p_row05_tracePolynomial_067
  · exact g32p_row05_tracePolynomial_068
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_076
  · exact g32p_row05_tracePolynomial_077
  · exact g32p_row05_tracePolynomial_078
  · exact g32p_row05_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_081
  · exact g32p_row05_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_085
  · exact g32p_row05_tracePolynomial_086
  · exact g32p_row05_tracePolynomial_087
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_089
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_091
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_096
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact False.elim ((by decide : (99 : Fin 102) ∉ g32p_supplierGroup03_support) hc)
  · exact g32p_row05_tracePolynomial_100
  · exact g32p_row05_tracePolynomial_101

theorem g32p_row05_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 4 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 4 c) := by
  by_cases hc : c ∈ g32p_supplierGroup03_support
  · have hclass (j : Fin 486) :
        IsConj (g32p_literalRepresentative c) (g32p_row05_groupEquiv j : g32p_G) ↔
          g32p_row05_supplierClassifier j = c := by
      simpa only [g32p_row05_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row05_supplierClass_iff (g32p_row05_groupEquiv j) c
    have hχ (j : Fin 486) :
        (g32p_recordedSupplierCharacters 4 (g32p_row05_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row05_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 4 (show (g32p_recordedSuppliers 4).H from g32p_row05_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row05_characterValues (g32p_row05_groupEquiv.symm (g32p_row05_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 4).H (g32p_recordedSupplierCharacters 4)
      (g32p_literalRepresentative c) g32p_row05_groupEquiv g32p_row05_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row05_characterValues j)).val) c 3 486
      (g32p_literalCentralizer c) (g32p_literalTraceValue 4 c) [1, 1, 1]
      (g32p_row05_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row05_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 4)))
      (g32p_row05_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row05_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row05_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
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

theorem g32p_row05_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
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

theorem g32p_row05_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
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

theorem g32p_row05_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
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

theorem g32p_row05_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
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

theorem g32p_row05_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
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

theorem g32p_row05_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row05_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
