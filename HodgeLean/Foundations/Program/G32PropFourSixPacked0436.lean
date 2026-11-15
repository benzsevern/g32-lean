import HodgeLean.Foundations.Program.G32PropFourSixPacked0435
import HodgeLean.Foundations.Program.G32PropFourSixPacked0418
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow49
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row47_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_0 r
  · exact g32p_row47_variantArithmetic_01_0 r
  · exact g32p_row47_variantArithmetic_02_0 r
  · exact g32p_row47_variantArithmetic_03_0 r
  · exact g32p_row47_variantArithmetic_04_0 r
  · exact g32p_row47_variantArithmetic_05_0 r
  · exact g32p_row47_variantArithmetic_06_0 r

theorem g32p_row47_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_1 r
  · exact g32p_row47_variantArithmetic_01_1 r
  · exact g32p_row47_variantArithmetic_02_1 r
  · exact g32p_row47_variantArithmetic_03_1 r
  · exact g32p_row47_variantArithmetic_04_1 r
  · exact g32p_row47_variantArithmetic_05_1 r
  · exact g32p_row47_variantArithmetic_06_1 r

theorem g32p_row47_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_2 r
  · exact g32p_row47_variantArithmetic_01_2 r
  · exact g32p_row47_variantArithmetic_02_2 r
  · exact g32p_row47_variantArithmetic_03_2 r
  · exact g32p_row47_variantArithmetic_04_2 r
  · exact g32p_row47_variantArithmetic_05_2 r
  · exact g32p_row47_variantArithmetic_06_2 r

theorem g32p_row47_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_3 r
  · exact g32p_row47_variantArithmetic_01_3 r
  · exact g32p_row47_variantArithmetic_02_3 r
  · exact g32p_row47_variantArithmetic_03_3 r
  · exact g32p_row47_variantArithmetic_04_3 r
  · exact g32p_row47_variantArithmetic_05_3 r
  · exact g32p_row47_variantArithmetic_06_3 r

theorem g32p_row47_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_4 r
  · exact g32p_row47_variantArithmetic_01_4 r
  · exact g32p_row47_variantArithmetic_02_4 r
  · exact g32p_row47_variantArithmetic_03_4 r
  · exact g32p_row47_variantArithmetic_04_4 r
  · exact g32p_row47_variantArithmetic_05_4 r
  · exact g32p_row47_variantArithmetic_06_4 r

theorem g32p_row47_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_5 r
  · exact g32p_row47_variantArithmetic_01_5 r
  · exact g32p_row47_variantArithmetic_02_5 r
  · exact g32p_row47_variantArithmetic_03_5 r
  · exact g32p_row47_variantArithmetic_04_5 r
  · exact g32p_row47_variantArithmetic_05_5 r
  · exact g32p_row47_variantArithmetic_06_5 r

theorem g32p_row47_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_6 r
  · exact g32p_row47_variantArithmetic_01_6 r
  · exact g32p_row47_variantArithmetic_02_6 r
  · exact g32p_row47_variantArithmetic_03_6 r
  · exact g32p_row47_variantArithmetic_04_6 r
  · exact g32p_row47_variantArithmetic_05_6 r
  · exact g32p_row47_variantArithmetic_06_6 r

theorem g32p_row47_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row47_variantArithmetic_00_7 r
  · exact g32p_row47_variantArithmetic_01_7 r
  · exact g32p_row47_variantArithmetic_02_7 r
  · exact g32p_row47_variantArithmetic_03_7 r
  · exact g32p_row47_variantArithmetic_04_7 r
  · exact g32p_row47_variantArithmetic_05_7 r
  · exact g32p_row47_variantArithmetic_06_7 r

theorem g32p_row47_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row47_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row47_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 46 c _ (g32p_row47_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row47_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row48_supplierClassifier : Fin 384 → Fin 102 := g32p_supplierGroup26_classify

theorem g32p_row48_groupEquiv_isConj (i : Fin 384) :
    IsConj (g32p_row36_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row48_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup26_source i).1 (g32p_supplierGroup26_source i).2
  rw [g32p_supplierGroup26_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row36_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup26_matrix i)

def g32p_row48_supplierClass (h : (g32p_recordedSuppliers 47).H) : Fin 102 :=
  g32p_row48_supplierClassifier (g32p_row36_groupEquiv.symm h)

theorem g32p_row48_supplierClass_isConj (h : (g32p_recordedSuppliers 47).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row48_supplierClass h)) := by
  have he : (g32p_row36_groupEquiv (g32p_row36_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 47).H => (a : g32p_G))
      (g32p_row36_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row48_supplierClassifier (g32p_row36_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row48_groupEquiv_isConj (g32p_row36_groupEquiv.symm h)

theorem g32p_row48_supplierClass_iff (h : (g32p_recordedSuppliers 47).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row48_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row48_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row48_supplierClass_isConj h).symm

theorem g32p_row48_supplierClass_mem_support (h : (g32p_recordedSuppliers 47).H) :
    g32p_row48_supplierClass h ∈ g32p_supplierGroup26_support :=
  g32p_supplierGroup26_support_mem (g32p_row36_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row48_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 0) (g32p_literalTraceValue 47 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row48_traceCoefficients_000]
  decide +kernel

theorem g32p_row48_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 5 = [4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 5) (g32p_literalTraceValue 47 5)
      [1, -1, 1] [2304, 2304] = true := by
  rw [g32p_row48_traceCoefficients_005]
  decide +kernel

theorem g32p_row48_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 13 = [0, 0, 28, 0, 0, 16] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 13) (g32p_literalTraceValue 47 13)
      [1, -1, 1] [0, 0, 4608, 4608] = true := by
  rw [g32p_row48_traceCoefficients_013]
  decide +kernel

theorem g32p_row48_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 18 = [10] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 18) (g32p_literalTraceValue 47 18)
      [1, -1, 1] [] = true := by
  rw [g32p_row48_traceCoefficients_018]
  decide +kernel

theorem g32p_row48_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 31 = [0, 8, 0, 0, 4] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 31) (g32p_literalTraceValue 47 31)
      [1, -1, 1] [-1152, 1152, 1152] = true := by
  rw [g32p_row48_traceCoefficients_031]
  decide +kernel

theorem g32p_row48_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 34 = [0, 16, 0, 0, 28] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 34) (g32p_literalTraceValue 47 34)
      [1, -1, 1] [3456, 8064, 8064] = true := by
  rw [g32p_row48_traceCoefficients_034]
  decide +kernel

theorem g32p_row48_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 37) (g32p_literalTraceValue 47 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row48_traceCoefficients_037]
  decide +kernel

theorem g32p_row48_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 38 = [16, 0, 0, 32] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 38) (g32p_literalTraceValue 47 38)
      [1, -1, 1] [768, 768] = true := by
  rw [g32p_row48_traceCoefficients_038]
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

theorem g32p_row48_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 49 = [0, 0, 16, 0, 0, 32] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 49) (g32p_literalTraceValue 47 49)
      [1, -1, 1] [0, 0, 768, 768] = true := by
  rw [g32p_row48_traceCoefficients_049]
  decide +kernel

theorem g32p_row48_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 52 = [0, 0, 4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 52) (g32p_literalTraceValue 47 52)
      [1, -1, 1] [0, 0, 2304, 2304] = true := by
  rw [g32p_row48_traceCoefficients_052]
  decide +kernel

theorem g32p_row48_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 57 = [0, 32, 0, 0, 16] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 57) (g32p_literalTraceValue 47 57)
      [1, -1, 1] [-384, 384, 384] = true := by
  rw [g32p_row48_traceCoefficients_057]
  decide +kernel

theorem g32p_row48_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 65 = [0, 0, 0, 0, 10] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 65) (g32p_literalTraceValue 47 65)
      [1, -1, 1] [17280, 17280, 17280] = true := by
  rw [g32p_row48_traceCoefficients_065]
  decide +kernel

theorem g32p_row48_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 69 = [28, 0, 0, 16] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 69) (g32p_literalTraceValue 47 69)
      [1, -1, 1] [4608, 4608] = true := by
  rw [g32p_row48_traceCoefficients_069]
  decide +kernel

theorem g32p_row48_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 82 = [0, 0, 10] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 82) (g32p_literalTraceValue 47 82)
      [1, -1, 1] [] = true := by
  rw [g32p_row48_traceCoefficients_082]
  decide +kernel

theorem g32p_row48_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 83 = [0, 0, 4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 83) (g32p_literalTraceValue 47 83)
      [1, -1, 1] [0, 0, 2304, 2304] = true := by
  rw [g32p_row48_traceCoefficients_083]
  decide +kernel

theorem g32p_row48_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 90 = [0, 8, 0, 0, 4] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 90) (g32p_literalTraceValue 47 90)
      [1, -1, 1] [-1152, 1152, 1152] = true := by
  rw [g32p_row48_traceCoefficients_090]
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

theorem g32p_row48_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 94 = [4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 94) (g32p_literalTraceValue 47 94)
      [1, -1, 1] [2304, 2304] = true := by
  rw [g32p_row48_traceCoefficients_094]
  decide +kernel

theorem g32p_row48_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 96 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 96) (g32p_literalTraceValue 47 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row48_traceCoefficients_096]
  decide +kernel

theorem g32p_row48_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 97 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 97) (g32p_literalTraceValue 47 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row48_traceCoefficients_097]
  decide +kernel

theorem g32p_row48_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 99) (g32p_literalTraceValue 47 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row48_traceCoefficients_099]
  decide +kernel

theorem g32p_row48_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row48_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) 101) (g32p_literalTraceValue 47 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row48_traceCoefficients_101]
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

def g32p_row48_generatorIndex : Fin 8 → Fin 408 :=
  ![47, 98, 149, 200, 298, 299, 400, 401]

theorem g32p_row48_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup26_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 47 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 47 g32p_row48_supplierClass
    g32p_row48_supplierClass_isConj g32p_supplierGroup26_support g32p_row48_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row48_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup26_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row48_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 47 c false (g32p_row48_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 47 c true (g32p_row48_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 47 c false (g32p_row48_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 47 c true (g32p_row48_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 47 c false (g32p_row48_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 47 c false (g32p_row48_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 47 c true (g32p_row48_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 47 c true (g32p_row48_coinduced_zero c hc true) 3

theorem g32p_row48_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row48_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row48_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup26_support) :
    g32p_literalTraceValue (g32p_row48_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup26_support →
    g32p_literalTraceValue (g32p_row48_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row48_zeroTrace_block_00 r k
  · exact g32p_row48_zeroTrace_block_01 r k
  · exact g32p_row48_zeroTrace_block_02 r k
  · exact g32p_row48_zeroTrace_block_03 r k
  · exact g32p_row48_zeroTrace_block_04 r k
  · exact g32p_row48_zeroTrace_block_05 r k
  · exact g32p_row48_zeroTrace_block_06 r k

theorem g32p_row48_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup26_support) :
    (g32p_recordedInductionGenerators (g32p_row48_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row48_generatorIndex k) c) := by
  rw [g32p_row48_recordedGenerator_zero c hc k, g32p_row48_zeroTrace_arithmetic c k hc]
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

def g32p_row48_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else [2304, 2304]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 4608, 4608] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [-1152, 1152, 1152] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [3456, 8064, 8064] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [768, 768] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 768, 768] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [0, 0, 2304, 2304] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [-384, 384, 384] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [17280, 17280, 17280])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [4608, 4608] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [0, 0, 2304, 2304] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [-1152, 1152, 1152] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [2304, 2304]))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row48_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup26_support) :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) c) (g32p_literalTraceValue 47 c)
      [1, -1, 1] (g32p_row48_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row48_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_037
  · exact g32p_row48_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_049
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_082
  · exact g32p_row48_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_096
  · exact g32p_row48_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row48_tracePolynomial_101

theorem g32p_row48_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 47 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 47 c) := by
  by_cases hc : c ∈ g32p_supplierGroup26_support
  · have hclass (j : Fin 384) :
        IsConj (g32p_literalRepresentative c) (g32p_row36_groupEquiv j : g32p_G) ↔
          g32p_row48_supplierClassifier j = c := by
      simpa only [g32p_row48_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row48_supplierClass_iff (g32p_row36_groupEquiv j) c
    have hχ (j : Fin 384) :
        (g32p_recordedSupplierCharacters 47 (g32p_row36_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row48_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 47 (show (g32p_recordedSuppliers 47).H from g32p_row36_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row48_characterValues (g32p_row36_groupEquiv.symm (g32p_row36_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 47).H (g32p_recordedSupplierCharacters 47)
      (g32p_literalRepresentative c) g32p_row36_groupEquiv g32p_row48_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row48_characterValues j)).val) c 6 384
      (g32p_literalCentralizer c) (g32p_literalTraceValue 47 c) [1, -1, 1]
      (g32p_row48_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row48_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 47)))
      (g32p_row48_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row48_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row48_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row48_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
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

theorem g32p_row48_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_0 r
  · exact g32p_row48_variantArithmetic_01_0 r
  · exact g32p_row48_variantArithmetic_02_0 r
  · exact g32p_row48_variantArithmetic_03_0 r
  · exact g32p_row48_variantArithmetic_04_0 r
  · exact g32p_row48_variantArithmetic_05_0 r
  · exact g32p_row48_variantArithmetic_06_0 r

theorem g32p_row48_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_1 r
  · exact g32p_row48_variantArithmetic_01_1 r
  · exact g32p_row48_variantArithmetic_02_1 r
  · exact g32p_row48_variantArithmetic_03_1 r
  · exact g32p_row48_variantArithmetic_04_1 r
  · exact g32p_row48_variantArithmetic_05_1 r
  · exact g32p_row48_variantArithmetic_06_1 r

theorem g32p_row48_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_2 r
  · exact g32p_row48_variantArithmetic_01_2 r
  · exact g32p_row48_variantArithmetic_02_2 r
  · exact g32p_row48_variantArithmetic_03_2 r
  · exact g32p_row48_variantArithmetic_04_2 r
  · exact g32p_row48_variantArithmetic_05_2 r
  · exact g32p_row48_variantArithmetic_06_2 r

theorem g32p_row48_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_3 r
  · exact g32p_row48_variantArithmetic_01_3 r
  · exact g32p_row48_variantArithmetic_02_3 r
  · exact g32p_row48_variantArithmetic_03_3 r
  · exact g32p_row48_variantArithmetic_04_3 r
  · exact g32p_row48_variantArithmetic_05_3 r
  · exact g32p_row48_variantArithmetic_06_3 r

theorem g32p_row48_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_4 r
  · exact g32p_row48_variantArithmetic_01_4 r
  · exact g32p_row48_variantArithmetic_02_4 r
  · exact g32p_row48_variantArithmetic_03_4 r
  · exact g32p_row48_variantArithmetic_04_4 r
  · exact g32p_row48_variantArithmetic_05_4 r
  · exact g32p_row48_variantArithmetic_06_4 r

theorem g32p_row48_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_5 r
  · exact g32p_row48_variantArithmetic_01_5 r
  · exact g32p_row48_variantArithmetic_02_5 r
  · exact g32p_row48_variantArithmetic_03_5 r
  · exact g32p_row48_variantArithmetic_04_5 r
  · exact g32p_row48_variantArithmetic_05_5 r
  · exact g32p_row48_variantArithmetic_06_5 r

theorem g32p_row48_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_6 r
  · exact g32p_row48_variantArithmetic_01_6 r
  · exact g32p_row48_variantArithmetic_02_6 r
  · exact g32p_row48_variantArithmetic_03_6 r
  · exact g32p_row48_variantArithmetic_04_6 r
  · exact g32p_row48_variantArithmetic_05_6 r
  · exact g32p_row48_variantArithmetic_06_6 r

theorem g32p_row48_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row48_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 47 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row48_variantArithmetic_00_7 r
  · exact g32p_row48_variantArithmetic_01_7 r
  · exact g32p_row48_variantArithmetic_02_7 r
  · exact g32p_row48_variantArithmetic_03_7 r
  · exact g32p_row48_variantArithmetic_04_7 r
  · exact g32p_row48_variantArithmetic_05_7 r
  · exact g32p_row48_variantArithmetic_06_7 r

theorem g32p_row48_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row48_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row48_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 47 c _ (g32p_row48_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row48_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup32_source : Fin 324 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (37, 244)) else (if i.val < 3 then (104, 194) else (if i.val < 4 then (100, 224) else (30, 165)))) else (if i.val < 7 then (if i.val < 6 then (0, 97) else (137, 60)) else (if i.val < 8 then (53, 59) else (if i.val < 9 then (104, 172) else (110, 240))))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then (54, 114) else (90, 123)) else (if i.val < 13 then (22, 151) else (if i.val < 14 then (28, 245) else (69, 112)))) else (if i.val < 17 then (if i.val < 16 then (9, 119) else (56, 149)) else (if i.val < 18 then (95, 16) else (if i.val < 19 then (56, 179) else (0, 174)))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then (44, 94) else (95, 8)) else (if i.val < 23 then (90, 142) else (if i.val < 24 then (137, 91) else (85, 231)))) else (if i.val < 27 then (if i.val < 26 then (71, 16) else (29, 134)) else (if i.val < 28 then (72, 186) else (if i.val < 29 then (0, 2) else (70, 35))))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then (75, 187) else (0, 1)) else (if i.val < 33 then (10, 87) else (if i.val < 34 then (69, 201) else (85, 74)))) else (if i.val < 37 then (if i.val < 36 then (43, 148) else (67, 81)) else (if i.val < 38 then (98, 191) else (if i.val < 39 then (62, 205) else (40, 59))))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then (84, 219) else (68, 101)) else (if i.val < 43 then (0, 101) else (if i.val < 44 then (116, 76) else (100, 53)))) else (if i.val < 47 then (if i.val < 46 then (96, 27) else (52, 47)) else (if i.val < 48 then (55, 153) else (if i.val < 49 then (94, 7) else (70, 61))))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then (109, 164) else (91, 51)) else (if i.val < 53 then (23, 171) else (if i.val < 54 then (137, 15) else (120, 51)))) else (if i.val < 57 then (if i.val < 56 then (1, 175) else (95, 172)) else (if i.val < 58 then (116, 133) else (if i.val < 59 then (54, 196) else (0, 99)))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then (80, 125) else (96, 9)) else (if i.val < 63 then (8, 102) else (if i.val < 64 then (91, 86) else (85, 41)))) else (if i.val < 67 then (if i.val < 66 then (136, 196) else (52, 144)) else (if i.val < 68 then (31, 142) else (if i.val < 69 then (129, 100) else (97, 57))))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then (66, 192) else (103, 202)) else (if i.val < 73 then (40, 137) else (if i.val < 74 then (55, 228) else (127, 113)))) else (if i.val < 78 then (if i.val < 76 then (93, 129) else (if i.val < 77 then (126, 48) else (76, 144))) else (if i.val < 79 then (44, 110) else (if i.val < 80 then (38, 164) else (25, 125)))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then (75, 114) else (90, 199)) else (if i.val < 84 then (25, 223) else (if i.val < 85 then (47, 128) else (33, 179)))) else (if i.val < 88 then (if i.val < 87 then (86, 62) else (37, 28)) else (if i.val < 89 then (99, 223) else (if i.val < 90 then (135, 118) else (76, 41))))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then (32, 157) else (38, 20)) else (if i.val < 94 then (47, 208) else (if i.val < 95 then (63, 14) else (5, 120)))) else (if i.val < 98 then (if i.val < 97 then (35, 226) else (136, 60)) else (if i.val < 99 then (13, 127) else (if i.val < 100 then (3, 21) else (124, 246)))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then (38, 99) else (25, 14)) else (if i.val < 104 then (77, 20) else (if i.val < 105 then (16, 93) else (24, 251)))) else (if i.val < 108 then (if i.val < 107 then (43, 176) else (29, 107)) else (if i.val < 109 then (76, 254) else (if i.val < 110 then (73, 247) else (38, 188))))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then (5, 28) else (46, 44)) else (if i.val < 114 then (12, 181) else (if i.val < 115 then (82, 13) else (17, 58)))) else (if i.val < 118 then (if i.val < 117 then (44, 229) else (101, 119)) else (if i.val < 119 then (42, 96) else (if i.val < 120 then (99, 34) else (66, 10))))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then (42, 27) else (16, 107)) else (if i.val < 124 then (66, 216) else (if i.val < 125 then (51, 17) else (123, 159)))) else (if i.val < 128 then (if i.val < 127 then (20, 223) else (65, 64)) else (if i.val < 129 then (97, 159) else (if i.val < 130 then (111, 230) else (121, 141))))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then (137, 184) else (128, 107)) else (if i.val < 134 then (124, 89) else (if i.val < 135 then (107, 102) else (66, 5)))) else (if i.val < 138 then (if i.val < 137 then (31, 204) else (22, 71)) else (if i.val < 139 then (41, 85) else (if i.val < 140 then (79, 107) else (68, 91)))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then (78, 30) else (20, 134)) else (if i.val < 144 then (38, 196) else (if i.val < 145 then (68, 147) else (1, 135)))) else (if i.val < 148 then (if i.val < 147 then (98, 38) else (99, 238)) else (if i.val < 149 then (94, 101) else (if i.val < 150 then (115, 255) else (137, 34))))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then (51, 206) else (100, 204)) else (if i.val < 154 then (10, 141) else (if i.val < 155 then (55, 210) else (0, 96)))) else (if i.val < 159 then (if i.val < 157 then (56, 148) else (if i.val < 158 then (9, 165) else (94, 113))) else (if i.val < 160 then (30, 136) else (if i.val < 161 then (102, 160) else (15, 33))))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then (10, 120) else (124, 176)) else (if i.val < 165 then (69, 183) else (if i.val < 166 then (41, 79) else (98, 194)))) else (if i.val < 169 then (if i.val < 168 then (38, 72) else (108, 217)) else (if i.val < 170 then (128, 164) else (if i.val < 171 then (80, 192) else (38, 121))))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then (65, 136) else (20, 200)) else (if i.val < 175 then (106, 68) else (if i.val < 176 then (78, 116) else (77, 246)))) else (if i.val < 179 then (if i.val < 178 then (33, 211) else (10, 140)) else (if i.val < 180 then (6, 32) else (if i.val < 181 then (50, 100) else (10, 104)))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then (68, 67) else (32, 221)) else (if i.val < 185 then (9, 145) else (if i.val < 186 then (0, 44) else (77, 197)))) else (if i.val < 189 then (if i.val < 188 then (9, 151) else (38, 32)) else (if i.val < 190 then (0, 93) else (if i.val < 191 then (11, 161) else (0, 37))))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then (73, 160) else (24, 147)) else (if i.val < 195 then (44, 53) else (if i.val < 196 then (66, 210) else (105, 155)))) else (if i.val < 199 then (if i.val < 198 then (93, 61) else (75, 202)) else (if i.val < 200 then (90, 188) else (if i.val < 201 then (14, 210) else (49, 135))))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then (75, 190) else (138, 48)) else (if i.val < 205 then (91, 185) else (if i.val < 206 then (124, 58) else (99, 205)))) else (if i.val < 209 then (if i.val < 208 then (122, 33) else (52, 138)) else (if i.val < 210 then (95, 10) else (if i.val < 211 then (56, 155) else (40, 22))))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then (31, 199) else (9, 67)) else (if i.val < 215 then (43, 157) else (if i.val < 216 then (0, 100) else (118, 228)))) else (if i.val < 219 then (if i.val < 218 then (103, 185) else (66, 242)) else (if i.val < 220 then (56, 145) else (if i.val < 221 then (85, 69) else (121, 113)))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then (9, 158) else (91, 213)) else (if i.val < 225 then (111, 226) else (if i.val < 226 then (84, 213) else (44, 186)))) else (if i.val < 229 then (if i.val < 228 then (71, 60) else (136, 97)) else (if i.val < 230 then (139, 23) else (if i.val < 231 then (118, 94) else (121, 86))))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then (13, 1) else (28, 80)) else (if i.val < 235 then (116, 197) else (if i.val < 236 then (122, 228) else (139, 61)))) else (if i.val < 240 then (if i.val < 238 then (99, 207) else (if i.val < 239 then (123, 97) else (124, 107))) else (if i.val < 241 then (124, 128) else (if i.val < 242 then (66, 68) else (44, 212)))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then (42, 160) else (53, 92)) else (if i.val < 246 then (13, 247) else (if i.val < 247 then (31, 172) else (55, 176)))) else (if i.val < 250 then (if i.val < 249 then (27, 80) else (14, 166)) else (if i.val < 251 then (31, 20) else (if i.val < 252 then (44, 108) else (14, 160))))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then (5, 129) else (99, 195)) else (if i.val < 256 then (54, 223) else (if i.val < 257 then (30, 92) else (40, 224)))) else (if i.val < 260 then (if i.val < 259 then (31, 158) else (13, 145)) else (if i.val < 261 then (93, 4) else (if i.val < 262 then (122, 155) else (135, 112)))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then (136, 117) else (107, 227)) else (if i.val < 266 then (133, 187) else (if i.val < 267 then (105, 49) else (32, 100)))) else (if i.val < 270 then (if i.val < 269 then (8, 77) else (92, 205)) else (if i.val < 271 then (32, 52) else (if i.val < 272 then (11, 159) else (107, 192))))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then (7, 237) else (70, 103)) else (if i.val < 276 then (32, 11) else (if i.val < 277 then (94, 50) else (92, 25)))) else (if i.val < 280 then (if i.val < 279 then (40, 187) else (91, 103)) else (if i.val < 281 then (36, 82) else (if i.val < 282 then (97, 156) else (108, 84))))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then (70, 153) else (67, 160)) else (if i.val < 286 then (119, 109) else (if i.val < 287 then (65, 125) else (92, 44)))) else (if i.val < 290 then (if i.val < 289 then (105, 7) else (118, 97)) else (if i.val < 291 then (105, 177) else (if i.val < 292 then (62, 99) else (89, 111))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then (74, 58) else (7, 243)) else (if i.val < 296 then (49, 69) else (if i.val < 297 then (41, 255) else (38, 37)))) else (if i.val < 300 then (if i.val < 299 then (12, 188) else (35, 249)) else (if i.val < 301 then (121, 71) else (if i.val < 302 then (25, 31) else (102, 60)))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then (137, 40) else (9, 154)) else (if i.val < 306 then (30, 26) else (if i.val < 307 then (111, 229) else (9, 164)))) else (if i.val < 310 then (if i.val < 309 then (31, 111) else (31, 203)) else (if i.val < 311 then (44, 203) else (if i.val < 312 then (121, 187) else (78, 14))))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then (136, 252) else (138, 72)) else (if i.val < 316 then (100, 183) else (if i.val < 317 then (22, 118) else (140, 100)))) else (if i.val < 321 then (if i.val < 319 then (69, 84) else (if i.val < 320 then (94, 99) else (56, 120))) else (if i.val < 322 then (41, 39) else (if i.val < 323 then (116, 123) else (51, 67))))))))))

def g32p_supplierGroup32_classify : Fin 324 → Fin 102 :=
  fun i => (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 0 else 34) else (if i.val < 3 then 4 else (if i.val < 4 then 45 else 78))) else (if i.val < 7 then (if i.val < 6 then 97 else 46) else (if i.val < 8 then 69 else (if i.val < 9 then 34 else 11)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 76 else 35) else (if i.val < 13 then 69 else (if i.val < 14 then 35 else 45))) else (if i.val < 17 then (if i.val < 16 then 34 else 78) else (if i.val < 18 then 69 else (if i.val < 19 then 24 else 32))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 56 else 21) else (if i.val < 23 then 30 else (if i.val < 24 then 46 else 32))) else (if i.val < 27 then (if i.val < 26 then 13 else 69) else (if i.val < 28 then 56 else (if i.val < 29 then 2 else 45)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 30 else 1) else (if i.val < 33 then 67 else (if i.val < 34 then 46 else 35))) else (if i.val < 37 then (if i.val < 36 then 13 else 69) else (if i.val < 38 then 13 else (if i.val < 39 then 4 else 69)))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then 11 else 69) else (if i.val < 43 then 101 else (if i.val < 44 then 30 else 13))) else (if i.val < 47 then (if i.val < 46 then 69 else 92) else (if i.val < 48 then 98 else (if i.val < 49 then 75 else 13)))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then 75 else 32) else (if i.val < 53 then 69 else (if i.val < 54 then 46 else 21))) else (if i.val < 57 then (if i.val < 56 then 98 else 21) else (if i.val < 58 then 30 else (if i.val < 59 then 75 else 99))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then 92 else 75) else (if i.val < 63 then 13 else (if i.val < 64 then 32 else 92))) else (if i.val < 67 then (if i.val < 66 then 46 else 67) else (if i.val < 68 then 87 else (if i.val < 69 then 21 else 45)))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then 21 else 30) else (if i.val < 73 then 21 else (if i.val < 74 then 45 else 30))) else (if i.val < 78 then (if i.val < 76 then 6 else (if i.val < 77 then 30 else 34)) else (if i.val < 79 then 13 else (if i.val < 80 then 34 else 13))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then 13 else 35) else (if i.val < 84 then 13 else (if i.val < 85 then 13 else 11))) else (if i.val < 88 then (if i.val < 87 then 6 else 4) else (if i.val < 89 then 46 else (if i.val < 90 then 21 else 30)))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then 6 else 34) else (if i.val < 94 then 13 else (if i.val < 95 then 4 else 95))) else (if i.val < 98 then (if i.val < 97 then 32 else 21) else (if i.val < 99 then 88 else (if i.val < 100 then 28 else 30))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 34 else 13) else (if i.val < 104 then 34 else (if i.val < 105 then 24 else 13))) else (if i.val < 108 then (if i.val < 107 then 13 else 95) else (if i.val < 109 then 30 else (if i.val < 110 then 46 else 32)))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then 92 else 84) else (if i.val < 114 then 88 else (if i.val < 115 then 21 else 28))) else (if i.val < 118 then (if i.val < 117 then 84 else 84) else (if i.val < 119 then 24 else (if i.val < 120 then 84 else 75)))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then 24 else 24) else (if i.val < 124 then 75 else (if i.val < 125 then 30 else 46))) else (if i.val < 128 then (if i.val < 127 then 30 else 6) else (if i.val < 129 then 46 else (if i.val < 130 then 35 else 46)))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then 46 else 21) else (if i.val < 134 then 46 else (if i.val < 135 then 21 else 21))) else (if i.val < 138 then (if i.val < 137 then 100 else 21) else (if i.val < 139 then 21 else (if i.val < 140 then 34 else 69))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then 34 else 34) else (if i.val < 144 then 34 else (if i.val < 145 then 78 else 87))) else (if i.val < 148 then (if i.val < 147 then 45 else 45) else (if i.val < 149 then 6 else (if i.val < 150 then 30 else 46)))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then 87 else 46) else (if i.val < 154 then 21 else (if i.val < 155 then 45 else 96))) else (if i.val < 159 then (if i.val < 157 then 78 else (if i.val < 158 then 34 else 6)) else (if i.val < 160 then 78 else (if i.val < 161 then 30 else 28)))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then 44 else 46) else (if i.val < 165 then 46 else (if i.val < 166 then 21 else 46))) else (if i.val < 169 then (if i.val < 168 then 32 else 21) else (if i.val < 170 then 21 else (if i.val < 171 then 69 else 34)))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then 69 else 34) else (if i.val < 175 then 34 else (if i.val < 176 then 34 else 34))) else (if i.val < 179 then (if i.val < 178 then 56 else 75) else (if i.val < 180 then 28 else (if i.val < 181 then 30 else 44))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then 75 else 44) else (if i.val < 185 then 32 else (if i.val < 186 then 44 else 93))) else (if i.val < 189 then (if i.val < 188 then 32 else 32) else (if i.val < 190 then 93 else (if i.val < 191 then 84 else 37)))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then 56 else 84) else (if i.val < 195 then 56 else (if i.val < 196 then 21 else 30))) else (if i.val < 199 then (if i.val < 198 then 21 else 30) else (if i.val < 200 then 30 else (if i.val < 201 then 76 else 30)))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then 30 else 46) else (if i.val < 205 then 30 else (if i.val < 206 then 46 else 46))) else (if i.val < 209 then (if i.val < 208 then 46 else 69) else (if i.val < 210 then 69 else (if i.val < 211 then 100 else 6)))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then 76 else 2) else (if i.val < 215 then 11 else (if i.val < 216 then 100 else 21))) else (if i.val < 219 then (if i.val < 218 then 30 else 6) else (if i.val < 220 then 78 else (if i.val < 221 then 35 else 46))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then 2 else 35) else (if i.val < 225 then 35 else (if i.val < 226 then 11 else 11))) else (if i.val < 229 then (if i.val < 228 then 45 else 21) else (if i.val < 230 then 30 else (if i.val < 231 then 21 else 84)))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then 30 else 30) else (if i.val < 235 then 30 else (if i.val < 236 then 46 else 30))) else (if i.val < 240 then (if i.val < 238 then 46 else (if i.val < 239 then 46 else 46)) else (if i.val < 241 then 46 else (if i.val < 242 then 69 else 13))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then 69 else 69) else (if i.val < 246 then 69 else (if i.val < 247 then 93 else 84))) else (if i.val < 250 then (if i.val < 249 then 93 else 98) else (if i.val < 251 then 84 else (if i.val < 252 then 84 else 98)))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then 95 else 56) else (if i.val < 256 then 75 else (if i.val < 257 then 95 else 75))) else (if i.val < 260 then (if i.val < 259 then 92 else 92) else (if i.val < 261 then 21 else (if i.val < 262 then 46 else 21))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then 21 else 21) else (if i.val < 266 then 30 else (if i.val < 267 then 30 else 2))) else (if i.val < 270 then (if i.val < 269 then 1 else 6) else (if i.val < 271 then 4 else (if i.val < 272 then 45 else 21)))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then 1 else 45) else (if i.val < 276 then 1 else (if i.val < 277 then 6 else 6))) else (if i.val < 280 then (if i.val < 279 then 67 else 35) else (if i.val < 281 then 4 else (if i.val < 282 then 46 else 21)))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then 46 else 21) else (if i.val < 286 then 21 else (if i.val < 287 then 21 else 21))) else (if i.val < 290 then (if i.val < 289 then 30 else 21) else (if i.val < 291 then 30 else (if i.val < 292 then 30 else 30)))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then 13 else 13) else (if i.val < 296 then 88 else (if i.val < 297 then 24 else 32))) else (if i.val < 300 then (if i.val < 299 then 88 else 32) else (if i.val < 301 then 84 else (if i.val < 302 then 84 else 46))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then 46 else 35) else (if i.val < 306 then 67 else (if i.val < 307 then 35 else 35))) else (if i.val < 310 then (if i.val < 309 then 87 else 100) else (if i.val < 311 then 45 else (if i.val < 312 then 46 else 30)))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then 46 else 46) else (if i.val < 316 then 46 else (if i.val < 317 then 21 else 21))) else (if i.val < 321 then (if i.val < 319 then 75 else (if i.val < 320 then 75 else 76)) else (if i.val < 322 then 6 else (if i.val < 323 then 30 else 30)))))))))

def g32p_supplierGroup32_support : Finset (Fin 102) :=
  {0, 1, 2, 4, 6, 11, 13, 21, 24, 28, 30, 32, 34, 35, 37, 44, 45, 46, 56, 67, 69, 75, 76, 78, 84, 87, 88, 92, 93, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end
