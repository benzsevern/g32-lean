import HodgeLean.Foundations.Program.G32PropFourSixPacked0365
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow16
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
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

theorem g32p_row15_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_0 r
  · exact g32p_row15_variantArithmetic_01_0 r
  · exact g32p_row15_variantArithmetic_02_0 r
  · exact g32p_row15_variantArithmetic_03_0 r
  · exact g32p_row15_variantArithmetic_04_0 r
  · exact g32p_row15_variantArithmetic_05_0 r
  · exact g32p_row15_variantArithmetic_06_0 r

theorem g32p_row15_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_1 r
  · exact g32p_row15_variantArithmetic_01_1 r
  · exact g32p_row15_variantArithmetic_02_1 r
  · exact g32p_row15_variantArithmetic_03_1 r
  · exact g32p_row15_variantArithmetic_04_1 r
  · exact g32p_row15_variantArithmetic_05_1 r
  · exact g32p_row15_variantArithmetic_06_1 r

theorem g32p_row15_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_2 r
  · exact g32p_row15_variantArithmetic_01_2 r
  · exact g32p_row15_variantArithmetic_02_2 r
  · exact g32p_row15_variantArithmetic_03_2 r
  · exact g32p_row15_variantArithmetic_04_2 r
  · exact g32p_row15_variantArithmetic_05_2 r
  · exact g32p_row15_variantArithmetic_06_2 r

theorem g32p_row15_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_3 r
  · exact g32p_row15_variantArithmetic_01_3 r
  · exact g32p_row15_variantArithmetic_02_3 r
  · exact g32p_row15_variantArithmetic_03_3 r
  · exact g32p_row15_variantArithmetic_04_3 r
  · exact g32p_row15_variantArithmetic_05_3 r
  · exact g32p_row15_variantArithmetic_06_3 r

theorem g32p_row15_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_4 r
  · exact g32p_row15_variantArithmetic_01_4 r
  · exact g32p_row15_variantArithmetic_02_4 r
  · exact g32p_row15_variantArithmetic_03_4 r
  · exact g32p_row15_variantArithmetic_04_4 r
  · exact g32p_row15_variantArithmetic_05_4 r
  · exact g32p_row15_variantArithmetic_06_4 r

theorem g32p_row15_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_5 r
  · exact g32p_row15_variantArithmetic_01_5 r
  · exact g32p_row15_variantArithmetic_02_5 r
  · exact g32p_row15_variantArithmetic_03_5 r
  · exact g32p_row15_variantArithmetic_04_5 r
  · exact g32p_row15_variantArithmetic_05_5 r
  · exact g32p_row15_variantArithmetic_06_5 r

theorem g32p_row15_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_6 r
  · exact g32p_row15_variantArithmetic_01_6 r
  · exact g32p_row15_variantArithmetic_02_6 r
  · exact g32p_row15_variantArithmetic_03_6 r
  · exact g32p_row15_variantArithmetic_04_6 r
  · exact g32p_row15_variantArithmetic_05_6 r
  · exact g32p_row15_variantArithmetic_06_6 r

theorem g32p_row15_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row15_variantArithmetic_00_7 r
  · exact g32p_row15_variantArithmetic_01_7 r
  · exact g32p_row15_variantArithmetic_02_7 r
  · exact g32p_row15_variantArithmetic_03_7 r
  · exact g32p_row15_variantArithmetic_04_7 r
  · exact g32p_row15_variantArithmetic_05_7 r
  · exact g32p_row15_variantArithmetic_06_7 r

theorem g32p_row15_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row15_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row15_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 14 c _ (g32p_row15_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row15_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup11_source : Fin 15 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (63, 20) else (87, 161))) else (if i.val < 5 then (if i.val < 4 then (118, 132) else (126, 169)) else (if i.val < 6 then (0, 96) else (129, 167)))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then (131, 217) else (124, 6)) else (if i.val < 10 then (107, 128) else (0, 101))) else (if i.val < 13 then (if i.val < 12 then (137, 114) else (82, 228)) else (if i.val < 14 then (115, 18) else (100, 115)))))

def g32p_supplierGroup11_classify : Fin 15 → Fin 102 :=
  fun i => (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 16 else 26)) else (if i.val < 5 then (if i.val < 4 then 73 else 16) else (if i.val < 6 then 96 else 73))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 16 else 26) else (if i.val < 10 then 73 else 101)) else (if i.val < 13 then (if i.val < 12 then 26 else 73) else (if i.val < 14 then 16 else 26))))

def g32p_supplierGroup11_support : Finset (Fin 102) :=
  {0, 16, 26, 73, 96, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup11_matrix_000 : ∀ r : Fin 16,
    g32p_row16_groupNodes (g32p_finBlockIndex 15 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup11_source (g32p_finBlockIndex 15 0 r)).1 (g32p_supplierGroup11_source (g32p_finBlockIndex 15 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup11_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup11_source (g32p_finBlockIndex 15 0 r)).1 (g32p_supplierGroup11_source (g32p_finBlockIndex 15 0 r)).2 =
      g32p_supplierGroup11_classify (g32p_finBlockIndex 15 0 r) := by
  decide +kernel

theorem g32p_supplierGroup11_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup11_classify (g32p_finBlockIndex 15 0 r) ∈ g32p_supplierGroup11_support := by
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

theorem g32p_supplierGroup11_matrix (i : Fin 15) :
    g32p_row16_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup11_source i).1 (g32p_supplierGroup11_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row16_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup11_source i).1 (g32p_supplierGroup11_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup11_matrix_000 r

theorem g32p_supplierGroup11_class (i : Fin 15) :
    g32p_supplierForest_classes (g32p_supplierGroup11_source i).1 (g32p_supplierGroup11_source i).2 =
      g32p_supplierGroup11_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup11_source i).1 (g32p_supplierGroup11_source i).2 =
      g32p_supplierGroup11_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup11_class_000 r

theorem g32p_supplierGroup11_support_mem (i : Fin 15) :
    g32p_supplierGroup11_classify i ∈ g32p_supplierGroup11_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup11_classify i ∈ g32p_supplierGroup11_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup11_support_000 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row16_supplierClassifier : Fin 15 → Fin 102 := g32p_supplierGroup11_classify

theorem g32p_row16_groupEquiv_isConj (i : Fin 15) :
    IsConj (g32p_row16_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row16_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup11_source i).1 (g32p_supplierGroup11_source i).2
  rw [g32p_supplierGroup11_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row16_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup11_matrix i)

def g32p_row16_supplierClass (h : (g32p_recordedSuppliers 15).H) : Fin 102 :=
  g32p_row16_supplierClassifier (g32p_row16_groupEquiv.symm h)

theorem g32p_row16_supplierClass_isConj (h : (g32p_recordedSuppliers 15).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row16_supplierClass h)) := by
  have he : (g32p_row16_groupEquiv (g32p_row16_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 15).H => (a : g32p_G))
      (g32p_row16_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row16_supplierClassifier (g32p_row16_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row16_groupEquiv_isConj (g32p_row16_groupEquiv.symm h)

theorem g32p_row16_supplierClass_iff (h : (g32p_recordedSuppliers 15).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row16_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row16_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row16_supplierClass_isConj h).symm

theorem g32p_row16_supplierClass_mem_support (h : (g32p_recordedSuppliers 15).H) :
    g32p_row16_supplierClass h ∈ g32p_supplierGroup11_support :=
  g32p_supplierGroup11_support_mem (g32p_row16_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row16_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row16_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer 0) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 0) (g32p_literalTraceValue 15 0)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row16_traceCoefficients_000]
  decide +kernel

theorem g32p_row16_traceCoefficients_016 :
    g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 16 = [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row16_tracePolynomial_016 :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer 16) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 16) (g32p_literalTraceValue 15 16)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-30, 0, 0, 30, 30, 30] = true := by
  rw [g32p_row16_traceCoefficients_016]
  decide +kernel

theorem g32p_row16_traceCoefficients_026 :
    g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 26 = [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row16_tracePolynomial_026 :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer 26) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 26) (g32p_literalTraceValue 15 26)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [0, 0, 30, 30, 30, 30, 30] = true := by
  rw [g32p_row16_traceCoefficients_026]
  decide +kernel

theorem g32p_row16_traceCoefficients_073 :
    g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 73 = [0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row16_tracePolynomial_073 :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer 73) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 73) (g32p_literalTraceValue 15 73)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [30, 30, 30, 30, 30] = true := by
  rw [g32p_row16_traceCoefficients_073]
  decide +kernel

theorem g32p_row16_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 96 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row16_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer 96) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 96) (g32p_literalTraceValue 15 96)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row16_traceCoefficients_096]
  decide +kernel

theorem g32p_row16_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 101 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row16_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer 101) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) 101) (g32p_literalTraceValue 15 101)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row16_traceCoefficients_101]
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

def g32p_row16_generatorIndex : Fin 8 → Fin 408 :=
  ![15, 66, 117, 168, 234, 235, 336, 337]

theorem g32p_row16_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup11_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 15 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 15 g32p_row16_supplierClass
    g32p_row16_supplierClass_isConj g32p_supplierGroup11_support g32p_row16_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row16_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup11_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row16_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 15 c false (g32p_row16_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 15 c true (g32p_row16_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 15 c false (g32p_row16_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 15 c true (g32p_row16_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 15 c false (g32p_row16_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 15 c false (g32p_row16_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 15 c true (g32p_row16_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 15 c true (g32p_row16_coinduced_zero c hc true) 3

theorem g32p_row16_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup11_support →
      g32p_literalTraceValue (g32p_row16_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row16_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup11_support) :
    g32p_literalTraceValue (g32p_row16_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup11_support →
    g32p_literalTraceValue (g32p_row16_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row16_zeroTrace_block_00 r k
  · exact g32p_row16_zeroTrace_block_01 r k
  · exact g32p_row16_zeroTrace_block_02 r k
  · exact g32p_row16_zeroTrace_block_03 r k
  · exact g32p_row16_zeroTrace_block_04 r k
  · exact g32p_row16_zeroTrace_block_05 r k
  · exact g32p_row16_zeroTrace_block_06 r k

theorem g32p_row16_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup11_support) :
    (g32p_recordedInductionGenerators (g32p_row16_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row16_generatorIndex k) c) := by
  rw [g32p_row16_recordedGenerator_zero c hc k, g32p_row16_zeroTrace_arithmetic c k hc]
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

def g32p_row16_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [-30, 0, 0, 30, 30, 30] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [0, 0, 30, 30, 30, 30, 30] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else [30, 30, 30, 30, 30]) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row16_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup11_support) :
    g32p_supplierTracePolynomialCheck 15 (g32p_literalCentralizer c) 15
      (g32p_supplierTraceCoefficients g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) c) (g32p_literalTraceValue 15 c)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] (g32p_row16_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row16_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact g32p_row16_tracePolynomial_016
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact g32p_row16_tracePolynomial_026
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact g32p_row16_tracePolynomial_073
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact g32p_row16_tracePolynomial_096
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (99 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup11_support) hc)
  · exact g32p_row16_tracePolynomial_101

theorem g32p_row16_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 15 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 15 c) := by
  by_cases hc : c ∈ g32p_supplierGroup11_support
  · have hclass (j : Fin 15) :
        IsConj (g32p_literalRepresentative c) (g32p_row16_groupEquiv j : g32p_G) ↔
          g32p_row16_supplierClassifier j = c := by
      simpa only [g32p_row16_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row16_supplierClass_iff (g32p_row16_groupEquiv j) c
    have hχ (j : Fin 15) :
        (g32p_recordedSupplierCharacters 15 (g32p_row16_groupEquiv j) : ℂ) =
          g32p_root 15 ^ (Multiplicative.toAdd (g32p_row16_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 15 (show (g32p_recordedSuppliers 15).H from g32p_row16_groupEquiv j)]
      change g32p_root 15 ^ (Multiplicative.toAdd
        (g32p_row16_characterValues (g32p_row16_groupEquiv.symm (g32p_row16_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 15).H (g32p_recordedSupplierCharacters 15)
      (g32p_literalRepresentative c) g32p_row16_groupEquiv g32p_row16_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row16_characterValues j)).val) c 15 15
      (g32p_literalCentralizer c) (g32p_literalTraceValue 15 c) [1, -1, 0, 1, -1, 1, 0, -1, 1]
      (g32p_row16_traceQuotient c) (g32p_root 15) (by decide)
      g32p_row16_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_fifteen
        (g32p_root_primitive (g32p_recordedSuppliers 15)))
      (g32p_row16_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 15 (by decide)] at h
    exact h
  · exact g32p_row16_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row16_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row16_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
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

theorem g32p_row16_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_0 r
  · exact g32p_row16_variantArithmetic_01_0 r
  · exact g32p_row16_variantArithmetic_02_0 r
  · exact g32p_row16_variantArithmetic_03_0 r
  · exact g32p_row16_variantArithmetic_04_0 r
  · exact g32p_row16_variantArithmetic_05_0 r
  · exact g32p_row16_variantArithmetic_06_0 r

theorem g32p_row16_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_1 r
  · exact g32p_row16_variantArithmetic_01_1 r
  · exact g32p_row16_variantArithmetic_02_1 r
  · exact g32p_row16_variantArithmetic_03_1 r
  · exact g32p_row16_variantArithmetic_04_1 r
  · exact g32p_row16_variantArithmetic_05_1 r
  · exact g32p_row16_variantArithmetic_06_1 r

theorem g32p_row16_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_2 r
  · exact g32p_row16_variantArithmetic_01_2 r
  · exact g32p_row16_variantArithmetic_02_2 r
  · exact g32p_row16_variantArithmetic_03_2 r
  · exact g32p_row16_variantArithmetic_04_2 r
  · exact g32p_row16_variantArithmetic_05_2 r
  · exact g32p_row16_variantArithmetic_06_2 r

theorem g32p_row16_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_3 r
  · exact g32p_row16_variantArithmetic_01_3 r
  · exact g32p_row16_variantArithmetic_02_3 r
  · exact g32p_row16_variantArithmetic_03_3 r
  · exact g32p_row16_variantArithmetic_04_3 r
  · exact g32p_row16_variantArithmetic_05_3 r
  · exact g32p_row16_variantArithmetic_06_3 r

theorem g32p_row16_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_4 r
  · exact g32p_row16_variantArithmetic_01_4 r
  · exact g32p_row16_variantArithmetic_02_4 r
  · exact g32p_row16_variantArithmetic_03_4 r
  · exact g32p_row16_variantArithmetic_04_4 r
  · exact g32p_row16_variantArithmetic_05_4 r
  · exact g32p_row16_variantArithmetic_06_4 r

theorem g32p_row16_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_5 r
  · exact g32p_row16_variantArithmetic_01_5 r
  · exact g32p_row16_variantArithmetic_02_5 r
  · exact g32p_row16_variantArithmetic_03_5 r
  · exact g32p_row16_variantArithmetic_04_5 r
  · exact g32p_row16_variantArithmetic_05_5 r
  · exact g32p_row16_variantArithmetic_06_5 r

theorem g32p_row16_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_6 r
  · exact g32p_row16_variantArithmetic_01_6 r
  · exact g32p_row16_variantArithmetic_02_6 r
  · exact g32p_row16_variantArithmetic_03_6 r
  · exact g32p_row16_variantArithmetic_04_6 r
  · exact g32p_row16_variantArithmetic_05_6 r
  · exact g32p_row16_variantArithmetic_06_6 r

theorem g32p_row16_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row16_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 15 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row16_variantArithmetic_00_7 r
  · exact g32p_row16_variantArithmetic_01_7 r
  · exact g32p_row16_variantArithmetic_02_7 r
  · exact g32p_row16_variantArithmetic_03_7 r
  · exact g32p_row16_variantArithmetic_04_7 r
  · exact g32p_row16_variantArithmetic_05_7 r
  · exact g32p_row16_variantArithmetic_06_7 r

theorem g32p_row16_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row16_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row16_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 15 c _ (g32p_row16_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row16_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end
