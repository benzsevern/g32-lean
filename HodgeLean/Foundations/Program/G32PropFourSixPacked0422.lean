import HodgeLean.Foundations.Program.G32PropFourSixPacked0421
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
set_option maxRecDepth 10000

theorem g32p_row38_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_0 r
  · exact g32p_row38_variantArithmetic_01_0 r
  · exact g32p_row38_variantArithmetic_02_0 r
  · exact g32p_row38_variantArithmetic_03_0 r
  · exact g32p_row38_variantArithmetic_04_0 r
  · exact g32p_row38_variantArithmetic_05_0 r
  · exact g32p_row38_variantArithmetic_06_0 r

theorem g32p_row38_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_1 r
  · exact g32p_row38_variantArithmetic_01_1 r
  · exact g32p_row38_variantArithmetic_02_1 r
  · exact g32p_row38_variantArithmetic_03_1 r
  · exact g32p_row38_variantArithmetic_04_1 r
  · exact g32p_row38_variantArithmetic_05_1 r
  · exact g32p_row38_variantArithmetic_06_1 r

theorem g32p_row38_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_2 r
  · exact g32p_row38_variantArithmetic_01_2 r
  · exact g32p_row38_variantArithmetic_02_2 r
  · exact g32p_row38_variantArithmetic_03_2 r
  · exact g32p_row38_variantArithmetic_04_2 r
  · exact g32p_row38_variantArithmetic_05_2 r
  · exact g32p_row38_variantArithmetic_06_2 r

theorem g32p_row38_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_3 r
  · exact g32p_row38_variantArithmetic_01_3 r
  · exact g32p_row38_variantArithmetic_02_3 r
  · exact g32p_row38_variantArithmetic_03_3 r
  · exact g32p_row38_variantArithmetic_04_3 r
  · exact g32p_row38_variantArithmetic_05_3 r
  · exact g32p_row38_variantArithmetic_06_3 r

theorem g32p_row38_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_4 r
  · exact g32p_row38_variantArithmetic_01_4 r
  · exact g32p_row38_variantArithmetic_02_4 r
  · exact g32p_row38_variantArithmetic_03_4 r
  · exact g32p_row38_variantArithmetic_04_4 r
  · exact g32p_row38_variantArithmetic_05_4 r
  · exact g32p_row38_variantArithmetic_06_4 r

theorem g32p_row38_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_5 r
  · exact g32p_row38_variantArithmetic_01_5 r
  · exact g32p_row38_variantArithmetic_02_5 r
  · exact g32p_row38_variantArithmetic_03_5 r
  · exact g32p_row38_variantArithmetic_04_5 r
  · exact g32p_row38_variantArithmetic_05_5 r
  · exact g32p_row38_variantArithmetic_06_5 r

theorem g32p_row38_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_6 r
  · exact g32p_row38_variantArithmetic_01_6 r
  · exact g32p_row38_variantArithmetic_02_6 r
  · exact g32p_row38_variantArithmetic_03_6 r
  · exact g32p_row38_variantArithmetic_04_6 r
  · exact g32p_row38_variantArithmetic_05_6 r
  · exact g32p_row38_variantArithmetic_06_6 r

theorem g32p_row38_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row38_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row38_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 37 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row38_variantArithmetic_00_7 r
  · exact g32p_row38_variantArithmetic_01_7 r
  · exact g32p_row38_variantArithmetic_02_7 r
  · exact g32p_row38_variantArithmetic_03_7 r
  · exact g32p_row38_variantArithmetic_04_7 r
  · exact g32p_row38_variantArithmetic_05_7 r
  · exact g32p_row38_variantArithmetic_06_7 r

theorem g32p_row38_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row38_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row38_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 37 c _ (g32p_row38_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row38_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row39_supplierClassifier : Fin 144 → Fin 102 := g32p_supplierGroup28_classify

theorem g32p_row39_groupEquiv_isConj (i : Fin 144) :
    IsConj (g32p_row38_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row39_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup28_source i).1 (g32p_supplierGroup28_source i).2
  rw [g32p_supplierGroup28_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row38_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup28_matrix i)

def g32p_row39_supplierClass (h : (g32p_recordedSuppliers 38).H) : Fin 102 :=
  g32p_row39_supplierClassifier (g32p_row38_groupEquiv.symm h)

theorem g32p_row39_supplierClass_isConj (h : (g32p_recordedSuppliers 38).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row39_supplierClass h)) := by
  have he : (g32p_row38_groupEquiv (g32p_row38_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 38).H => (a : g32p_G))
      (g32p_row38_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row39_supplierClassifier (g32p_row38_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row39_groupEquiv_isConj (g32p_row38_groupEquiv.symm h)

theorem g32p_row39_supplierClass_iff (h : (g32p_recordedSuppliers 38).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row39_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row39_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row39_supplierClass_isConj h).symm

theorem g32p_row39_supplierClass_mem_support (h : (g32p_recordedSuppliers 38).H) :
    g32p_row39_supplierClass h ∈ g32p_supplierGroup28_support :=
  g32p_supplierGroup28_support_mem (g32p_row38_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row39_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 0) (g32p_literalTraceValue 38 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_000]
  decide +kernel

theorem g32p_row39_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 4 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 4) (g32p_literalTraceValue 38 4)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_004]
  decide +kernel

theorem g32p_row39_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 5) (g32p_literalTraceValue 38 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_005]
  decide +kernel

theorem g32p_row39_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 7 = [0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 7) (g32p_literalTraceValue 38 7)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_007]
  decide +kernel

theorem g32p_row39_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 10 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 10) (g32p_literalTraceValue 38 10)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_010]
  decide +kernel

theorem g32p_row39_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 11 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 11) (g32p_literalTraceValue 38 11)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row39_traceCoefficients_011]
  decide +kernel

theorem g32p_row39_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 15 = [0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 15) (g32p_literalTraceValue 38 15)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row39_traceCoefficients_015]
  decide +kernel

theorem g32p_row39_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 18 = [1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 18) (g32p_literalTraceValue 38 18)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row39_traceCoefficients_018]
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

theorem g32p_row39_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 19 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 19) (g32p_literalTraceValue 38 19)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_019]
  decide +kernel

theorem g32p_row39_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 20 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 20) (g32p_literalTraceValue 38 20)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_020]
  decide +kernel

theorem g32p_row39_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 23 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 23) (g32p_literalTraceValue 38 23)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_023]
  decide +kernel

theorem g32p_row39_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 28 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 28) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 28) (g32p_literalTraceValue 38 28)
      [1, -1, 1] [15552, 15552] = true := by
  rw [g32p_row39_traceCoefficients_028]
  decide +kernel

theorem g32p_row39_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 32 = [0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 32) (g32p_literalTraceValue 38 32)
      [1, -1, 1] [-1296] = true := by
  rw [g32p_row39_traceCoefficients_032]
  decide +kernel

theorem g32p_row39_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 35 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 35) (g32p_literalTraceValue 38 35)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row39_traceCoefficients_035]
  decide +kernel

theorem g32p_row39_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 41 = [0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 41) (g32p_literalTraceValue 38 41)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_041]
  decide +kernel

theorem g32p_row39_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 44 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 44) (g32p_literalTraceValue 38 44)
      [1, -1, 1] [0, 0, 3888, 3888] = true := by
  rw [g32p_row39_traceCoefficients_044]
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

theorem g32p_row39_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 45 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 45) (g32p_literalTraceValue 38 45)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_045]
  decide +kernel

theorem g32p_row39_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 50 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 50) (g32p_literalTraceValue 38 50)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_050]
  decide +kernel

theorem g32p_row39_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 51 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 51) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 51) (g32p_literalTraceValue 38 51)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row39_traceCoefficients_051]
  decide +kernel

theorem g32p_row39_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 56 = [0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 56) (g32p_literalTraceValue 38 56)
      [1, -1, 1] [-2592] = true := by
  rw [g32p_row39_traceCoefficients_056]
  decide +kernel

theorem g32p_row39_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 59 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 59) (g32p_literalTraceValue 38 59)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_059]
  decide +kernel

theorem g32p_row39_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 64 = [4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 64) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 64) (g32p_literalTraceValue 38 64)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_064]
  decide +kernel

theorem g32p_row39_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 66 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 66) (g32p_literalTraceValue 38 66)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_066]
  decide +kernel

theorem g32p_row39_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 67 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 67) (g32p_literalTraceValue 38 67)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row39_traceCoefficients_067]
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

theorem g32p_row39_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 72 = [0, 6] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 72) (g32p_literalTraceValue 38 72)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row39_traceCoefficients_072]
  decide +kernel

theorem g32p_row39_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 76 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 76) (g32p_literalTraceValue 38 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_076]
  decide +kernel

theorem g32p_row39_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 77 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 77) (g32p_literalTraceValue 38 77)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row39_traceCoefficients_077]
  decide +kernel

theorem g32p_row39_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 79 = [0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 79) (g32p_literalTraceValue 38 79)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row39_traceCoefficients_079]
  decide +kernel

theorem g32p_row39_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 84 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 84) (g32p_literalTraceValue 38 84)
      [1, -1, 1] [0, 0, 1296, 1296] = true := by
  rw [g32p_row39_traceCoefficients_084]
  decide +kernel

theorem g32p_row39_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 85 = [4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 85) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 85) (g32p_literalTraceValue 38 85)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_085]
  decide +kernel

theorem g32p_row39_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 86 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 86) (g32p_literalTraceValue 38 86)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_086]
  decide +kernel

theorem g32p_row39_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 87 = [4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 87) (g32p_literalTraceValue 38 87)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_087]
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

theorem g32p_row39_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 88 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 88) (g32p_literalTraceValue 38 88)
      [1, -1, 1] [15552, 15552] = true := by
  rw [g32p_row39_traceCoefficients_088]
  decide +kernel

theorem g32p_row39_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 91 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 91) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 91) (g32p_literalTraceValue 38 91)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row39_traceCoefficients_091]
  decide +kernel

theorem g32p_row39_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 92 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 92) (g32p_literalTraceValue 38 92)
      [1, -1, 1] [0, 0, 2592, 2592] = true := by
  rw [g32p_row39_traceCoefficients_092]
  decide +kernel

theorem g32p_row39_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 94 = [0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 94) (g32p_literalTraceValue 38 94)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row39_traceCoefficients_094]
  decide +kernel

theorem g32p_row39_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 95 = [0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 95) (g32p_literalTraceValue 38 95)
      [1, -1, 1] [-3888] = true := by
  rw [g32p_row39_traceCoefficients_095]
  decide +kernel

theorem g32p_row39_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 99 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 99) (g32p_literalTraceValue 38 99)
      [1, -1, 1] [155520, 155520] = true := by
  rw [g32p_row39_traceCoefficients_099]
  decide +kernel

theorem g32p_row39_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 100 = [4] := by
  decide +kernel

theorem g32p_row39_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) 100) (g32p_literalTraceValue 38 100)
      [1, -1, 1] [] = true := by
  rw [g32p_row39_traceCoefficients_100]
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

def g32p_row39_generatorIndex : Fin 8 → Fin 408 :=
  ![38, 89, 140, 191, 280, 281, 382, 383]

theorem g32p_row39_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup28_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 38 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 38 g32p_row39_supplierClass
    g32p_row39_supplierClass_isConj g32p_supplierGroup28_support g32p_row39_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row39_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup28_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row39_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 38 c false (g32p_row39_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 38 c true (g32p_row39_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 38 c false (g32p_row39_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 38 c true (g32p_row39_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 38 c false (g32p_row39_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 38 c false (g32p_row39_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 38 c true (g32p_row39_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 38 c true (g32p_row39_coinduced_zero c hc true) 3

theorem g32p_row39_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup28_support →
      g32p_literalTraceValue (g32p_row39_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row39_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup28_support) :
    g32p_literalTraceValue (g32p_row39_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup28_support →
    g32p_literalTraceValue (g32p_row39_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row39_zeroTrace_block_00 r k
  · exact g32p_row39_zeroTrace_block_01 r k
  · exact g32p_row39_zeroTrace_block_02 r k
  · exact g32p_row39_zeroTrace_block_03 r k
  · exact g32p_row39_zeroTrace_block_04 r k
  · exact g32p_row39_zeroTrace_block_05 r k
  · exact g32p_row39_zeroTrace_block_06 r k

theorem g32p_row39_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup28_support) :
    (g32p_recordedInductionGenerators (g32p_row39_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row39_generatorIndex k) c) := by
  rw [g32p_row39_recordedGenerator_zero c hc k, g32p_row39_zeroTrace_arithmetic c k hc]
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

def g32p_row39_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [432, 432, 432] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [0, 0, 432, 432] else [2592, 2592, 2592])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [-432] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [1728, 1728] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [432, 432, 432] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [15552, 15552] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [-1296] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [1296, 1296, 1296]) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [0, 0, 432, 432] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [0, 0, 3888, 3888] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [0, 432, 432])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [1728, 1728] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [-2592]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [0, 0, 432, 432])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [432, 432, 432] else (if i.val < 68 then [3888, 3888, 3888] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [-432] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [0, 0, 432, 432] else [])) else (if i.val < 80 then [-432] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [0, 0, 1296, 1296])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [15552, 15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [1728, 1728])) else (if i.val < 93 then [0, 0, 2592, 2592] else (if i.val < 94 then [] else [1728, 1728]))) else (if i.val < 98 then (if i.val < 96 then [-3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else [155520, 155520]) else (if i.val < 101 then [] else [])))))))

theorem g32p_row39_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup28_support) :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) c) (g32p_literalTraceValue 38 c)
      [1, -1, 1] (g32p_row39_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row39_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_004
  · exact g32p_row39_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_007
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_010
  · exact g32p_row39_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_018
  · exact g32p_row39_tracePolynomial_019
  · exact g32p_row39_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_044
  · exact g32p_row39_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_050
  · exact g32p_row39_tracePolynomial_051
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_064
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_066
  · exact g32p_row39_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_076
  · exact g32p_row39_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_084
  · exact g32p_row39_tracePolynomial_085
  · exact g32p_row39_tracePolynomial_086
  · exact g32p_row39_tracePolynomial_087
  · exact g32p_row39_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_091
  · exact g32p_row39_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_094
  · exact g32p_row39_tracePolynomial_095
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup28_support) hc)
  · exact g32p_row39_tracePolynomial_099
  · exact g32p_row39_tracePolynomial_100
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_supplierGroup28_support) hc)

theorem g32p_row39_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 38 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 38 c) := by
  by_cases hc : c ∈ g32p_supplierGroup28_support
  · have hclass (j : Fin 144) :
        IsConj (g32p_literalRepresentative c) (g32p_row38_groupEquiv j : g32p_G) ↔
          g32p_row39_supplierClassifier j = c := by
      simpa only [g32p_row39_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row39_supplierClass_iff (g32p_row38_groupEquiv j) c
    have hχ (j : Fin 144) :
        (g32p_recordedSupplierCharacters 38 (g32p_row38_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row39_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 38 (show (g32p_recordedSuppliers 38).H from g32p_row38_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row39_characterValues (g32p_row38_groupEquiv.symm (g32p_row38_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 38).H (g32p_recordedSupplierCharacters 38)
      (g32p_literalRepresentative c) g32p_row38_groupEquiv g32p_row39_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row39_characterValues j)).val) c 6 144
      (g32p_literalCentralizer c) (g32p_literalTraceValue 38 c) [1, -1, 1]
      (g32p_row39_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row39_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 38)))
      (g32p_row39_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row39_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row39_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
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

theorem g32p_row39_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
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

theorem g32p_row39_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
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

theorem g32p_row39_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
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

theorem g32p_row39_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
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

theorem g32p_row39_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
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

theorem g32p_row39_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row39_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
