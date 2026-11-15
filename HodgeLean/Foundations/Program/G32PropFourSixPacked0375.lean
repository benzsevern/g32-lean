import HodgeLean.Foundations.Program.G32PropFourSixPacked0374
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow18
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
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

theorem g32p_row17_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_0 r
  · exact g32p_row17_variantArithmetic_01_0 r
  · exact g32p_row17_variantArithmetic_02_0 r
  · exact g32p_row17_variantArithmetic_03_0 r
  · exact g32p_row17_variantArithmetic_04_0 r
  · exact g32p_row17_variantArithmetic_05_0 r
  · exact g32p_row17_variantArithmetic_06_0 r

theorem g32p_row17_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_1 r
  · exact g32p_row17_variantArithmetic_01_1 r
  · exact g32p_row17_variantArithmetic_02_1 r
  · exact g32p_row17_variantArithmetic_03_1 r
  · exact g32p_row17_variantArithmetic_04_1 r
  · exact g32p_row17_variantArithmetic_05_1 r
  · exact g32p_row17_variantArithmetic_06_1 r

theorem g32p_row17_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_2 r
  · exact g32p_row17_variantArithmetic_01_2 r
  · exact g32p_row17_variantArithmetic_02_2 r
  · exact g32p_row17_variantArithmetic_03_2 r
  · exact g32p_row17_variantArithmetic_04_2 r
  · exact g32p_row17_variantArithmetic_05_2 r
  · exact g32p_row17_variantArithmetic_06_2 r

theorem g32p_row17_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_3 r
  · exact g32p_row17_variantArithmetic_01_3 r
  · exact g32p_row17_variantArithmetic_02_3 r
  · exact g32p_row17_variantArithmetic_03_3 r
  · exact g32p_row17_variantArithmetic_04_3 r
  · exact g32p_row17_variantArithmetic_05_3 r
  · exact g32p_row17_variantArithmetic_06_3 r

theorem g32p_row17_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_4 r
  · exact g32p_row17_variantArithmetic_01_4 r
  · exact g32p_row17_variantArithmetic_02_4 r
  · exact g32p_row17_variantArithmetic_03_4 r
  · exact g32p_row17_variantArithmetic_04_4 r
  · exact g32p_row17_variantArithmetic_05_4 r
  · exact g32p_row17_variantArithmetic_06_4 r

theorem g32p_row17_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_5 r
  · exact g32p_row17_variantArithmetic_01_5 r
  · exact g32p_row17_variantArithmetic_02_5 r
  · exact g32p_row17_variantArithmetic_03_5 r
  · exact g32p_row17_variantArithmetic_04_5 r
  · exact g32p_row17_variantArithmetic_05_5 r
  · exact g32p_row17_variantArithmetic_06_5 r

theorem g32p_row17_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_6 r
  · exact g32p_row17_variantArithmetic_01_6 r
  · exact g32p_row17_variantArithmetic_02_6 r
  · exact g32p_row17_variantArithmetic_03_6 r
  · exact g32p_row17_variantArithmetic_04_6 r
  · exact g32p_row17_variantArithmetic_05_6 r
  · exact g32p_row17_variantArithmetic_06_6 r

theorem g32p_row17_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row17_variantArithmetic_00_7 r
  · exact g32p_row17_variantArithmetic_01_7 r
  · exact g32p_row17_variantArithmetic_02_7 r
  · exact g32p_row17_variantArithmetic_03_7 r
  · exact g32p_row17_variantArithmetic_04_7 r
  · exact g32p_row17_variantArithmetic_05_7 r
  · exact g32p_row17_variantArithmetic_06_7 r

theorem g32p_row17_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row17_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row17_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 16 c _ (g32p_row17_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row17_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup13_source : Fin 36 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (105, 126)) else (if i.val < 3 then (30, 150) else (0, 99))) else (if i.val < 6 then (if i.val < 5 then (0, 96) else (116, 169)) else (if i.val < 7 then (19, 212) else (if i.val < 8 then (14, 66) else (7, 89))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (16, 48) else (59, 10)) else (if i.val < 12 then (0, 97) else (131, 183))) else (if i.val < 15 then (if i.val < 14 then (90, 36) else (23, 41)) else (if i.val < 16 then (0, 101) else (if i.val < 17 then (82, 82) else (109, 106)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (70, 196) else (75, 47)) else (if i.val < 21 then (140, 48) else (4, 145))) else (if i.val < 24 then (if i.val < 23 then (62, 90) else (0, 37)) else (if i.val < 25 then (120, 62) else (if i.val < 26 then (117, 57) else (71, 44))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (112, 2) else (122, 5)) else (if i.val < 30 then (57, 13) else (80, 45))) else (if i.val < 33 then (if i.val < 32 then (43, 109) else (75, 78)) else (if i.val < 34 then (144, 14) else (if i.val < 35 then (31, 121) else (87, 118)))))))

def g32p_supplierGroup13_classify : Fin 36 → Fin 102 :=
  fun i => (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 65) else (if i.val < 3 then 78 else 99)) else (if i.val < 6 then (if i.val < 5 then 96 else 59) else (if i.val < 7 then 65 else (if i.val < 8 then 78 else 24)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 18 else 11) else (if i.val < 12 then 97 else 29)) else (if i.val < 15 then (if i.val < 14 then 59 else 24) else (if i.val < 16 then 101 else (if i.val < 17 then 74 else 18))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 11 else 56) else (if i.val < 21 then 29 else 82)) else (if i.val < 24 then (if i.val < 23 then 4 else 37) else (if i.val < 25 then 43 else (if i.val < 26 then 74 else 56)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 25 else 82) else (if i.val < 30 then 4 else 92)) else (if i.val < 33 then (if i.val < 32 then 43 else 50) else (if i.val < 34 then 25 else (if i.val < 35 then 92 else 50))))))

def g32p_supplierGroup13_support : Finset (Fin 102) :=
  {0, 4, 11, 18, 24, 25, 29, 37, 43, 50, 56, 59, 65, 74, 78, 82, 92, 96, 97, 99, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup13_matrix_000 : ∀ r : Fin 16,
    g32p_row18_groupNodes (g32p_finBlockIndex 36 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup13_source (g32p_finBlockIndex 36 0 r)).1 (g32p_supplierGroup13_source (g32p_finBlockIndex 36 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup13_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup13_source (g32p_finBlockIndex 36 0 r)).1 (g32p_supplierGroup13_source (g32p_finBlockIndex 36 0 r)).2 =
      g32p_supplierGroup13_classify (g32p_finBlockIndex 36 0 r) := by
  decide +kernel

theorem g32p_supplierGroup13_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup13_classify (g32p_finBlockIndex 36 0 r) ∈ g32p_supplierGroup13_support := by
  decide +kernel

theorem g32p_supplierGroup13_matrix_001 : ∀ r : Fin 16,
    g32p_row18_groupNodes (g32p_finBlockIndex 36 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup13_source (g32p_finBlockIndex 36 1 r)).1 (g32p_supplierGroup13_source (g32p_finBlockIndex 36 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup13_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup13_source (g32p_finBlockIndex 36 1 r)).1 (g32p_supplierGroup13_source (g32p_finBlockIndex 36 1 r)).2 =
      g32p_supplierGroup13_classify (g32p_finBlockIndex 36 1 r) := by
  decide +kernel

theorem g32p_supplierGroup13_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup13_classify (g32p_finBlockIndex 36 1 r) ∈ g32p_supplierGroup13_support := by
  decide +kernel

theorem g32p_supplierGroup13_matrix_002 : ∀ r : Fin 16,
    g32p_row18_groupNodes (g32p_finBlockIndex 36 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup13_source (g32p_finBlockIndex 36 2 r)).1 (g32p_supplierGroup13_source (g32p_finBlockIndex 36 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup13_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup13_source (g32p_finBlockIndex 36 2 r)).1 (g32p_supplierGroup13_source (g32p_finBlockIndex 36 2 r)).2 =
      g32p_supplierGroup13_classify (g32p_finBlockIndex 36 2 r) := by
  decide +kernel

theorem g32p_supplierGroup13_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup13_classify (g32p_finBlockIndex 36 2 r) ∈ g32p_supplierGroup13_support := by
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

theorem g32p_supplierGroup13_matrix (i : Fin 36) :
    g32p_row18_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup13_source i).1 (g32p_supplierGroup13_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row18_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup13_source i).1 (g32p_supplierGroup13_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup13_matrix_000 r
  · exact g32p_supplierGroup13_matrix_001 r
  · exact g32p_supplierGroup13_matrix_002 r

theorem g32p_supplierGroup13_class (i : Fin 36) :
    g32p_supplierForest_classes (g32p_supplierGroup13_source i).1 (g32p_supplierGroup13_source i).2 =
      g32p_supplierGroup13_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup13_source i).1 (g32p_supplierGroup13_source i).2 =
      g32p_supplierGroup13_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup13_class_000 r
  · exact g32p_supplierGroup13_class_001 r
  · exact g32p_supplierGroup13_class_002 r

theorem g32p_supplierGroup13_support_mem (i : Fin 36) :
    g32p_supplierGroup13_classify i ∈ g32p_supplierGroup13_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup13_classify i ∈ g32p_supplierGroup13_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup13_support_000 r
  · exact g32p_supplierGroup13_support_001 r
  · exact g32p_supplierGroup13_support_002 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_supplierClassifier : Fin 36 → Fin 102 := g32p_supplierGroup13_classify

theorem g32p_row18_groupEquiv_isConj (i : Fin 36) :
    IsConj (g32p_row18_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row18_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup13_source i).1 (g32p_supplierGroup13_source i).2
  rw [g32p_supplierGroup13_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row18_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup13_matrix i)

def g32p_row18_supplierClass (h : (g32p_recordedSuppliers 17).H) : Fin 102 :=
  g32p_row18_supplierClassifier (g32p_row18_groupEquiv.symm h)

theorem g32p_row18_supplierClass_isConj (h : (g32p_recordedSuppliers 17).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row18_supplierClass h)) := by
  have he : (g32p_row18_groupEquiv (g32p_row18_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 17).H => (a : g32p_G))
      (g32p_row18_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row18_supplierClassifier (g32p_row18_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row18_groupEquiv_isConj (g32p_row18_groupEquiv.symm h)

theorem g32p_row18_supplierClass_iff (h : (g32p_recordedSuppliers 17).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row18_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row18_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row18_supplierClass_isConj h).symm

theorem g32p_row18_supplierClass_mem_support (h : (g32p_recordedSuppliers 17).H) :
    g32p_row18_supplierClass h ∈ g32p_supplierGroup13_support :=
  g32p_supplierGroup13_support_mem (g32p_row18_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row18_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 0) (g32p_literalTraceValue 17 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row18_traceCoefficients_000]
  decide +kernel

theorem g32p_row18_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 4 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 4) (g32p_literalTraceValue 17 4)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row18_traceCoefficients_004]
  decide +kernel

theorem g32p_row18_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 11 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 11) (g32p_literalTraceValue 17 11)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row18_traceCoefficients_011]
  decide +kernel

theorem g32p_row18_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 18 = [0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 18) (g32p_literalTraceValue 17 18)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row18_traceCoefficients_018]
  decide +kernel

theorem g32p_row18_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 24 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 24) (g32p_literalTraceValue 17 24)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row18_traceCoefficients_024]
  decide +kernel

theorem g32p_row18_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 25 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 25) (g32p_literalTraceValue 17 25)
      [1, -1, 1] [0, 0, 216, 216] = true := by
  rw [g32p_row18_traceCoefficients_025]
  decide +kernel

theorem g32p_row18_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 29 = [0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 29) (g32p_literalTraceValue 17 29)
      [1, -1, 1] [-216] = true := by
  rw [g32p_row18_traceCoefficients_029]
  decide +kernel

theorem g32p_row18_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 37 = [1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 37) (g32p_literalTraceValue 17 37)
      [1, -1, 1] [] = true := by
  rw [g32p_row18_traceCoefficients_037]
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

theorem g32p_row18_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 43 = [0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 43) (g32p_literalTraceValue 17 43)
      [1, -1, 1] [-216] = true := by
  rw [g32p_row18_traceCoefficients_043]
  decide +kernel

theorem g32p_row18_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 50 = [0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 50) (g32p_literalTraceValue 17 50)
      [1, -1, 1] [-216] = true := by
  rw [g32p_row18_traceCoefficients_050]
  decide +kernel

theorem g32p_row18_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 56 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 56) (g32p_literalTraceValue 17 56)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row18_traceCoefficients_056]
  decide +kernel

theorem g32p_row18_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 59 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 59) (g32p_literalTraceValue 17 59)
      [1, -1, 1] [0, 0, 216, 216] = true := by
  rw [g32p_row18_traceCoefficients_059]
  decide +kernel

theorem g32p_row18_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 65 = [0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 65) (g32p_literalTraceValue 17 65)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row18_traceCoefficients_065]
  decide +kernel

theorem g32p_row18_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 74 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 74) (g32p_literalTraceValue 17 74)
      [1, -1, 1] [0, 0, 216, 216] = true := by
  rw [g32p_row18_traceCoefficients_074]
  decide +kernel

theorem g32p_row18_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 78 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 78) (g32p_literalTraceValue 17 78)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row18_traceCoefficients_078]
  decide +kernel

theorem g32p_row18_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 82 = [0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 82) (g32p_literalTraceValue 17 82)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row18_traceCoefficients_082]
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

theorem g32p_row18_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 92 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 92) (g32p_literalTraceValue 17 92)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row18_traceCoefficients_092]
  decide +kernel

theorem g32p_row18_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 96 = [1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 96) (g32p_literalTraceValue 17 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row18_traceCoefficients_096]
  decide +kernel

theorem g32p_row18_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 97 = [1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 97) (g32p_literalTraceValue 17 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row18_traceCoefficients_097]
  decide +kernel

theorem g32p_row18_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 99) (g32p_literalTraceValue 17 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row18_traceCoefficients_099]
  decide +kernel

theorem g32p_row18_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 101 = [1] := by
  decide +kernel

theorem g32p_row18_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) 101) (g32p_literalTraceValue 17 101)
      [1, -1, 1] [] = true := by
  rw [g32p_row18_traceCoefficients_101]
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

def g32p_row18_generatorIndex : Fin 8 → Fin 408 :=
  ![17, 68, 119, 170, 238, 239, 340, 341]

theorem g32p_row18_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup13_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 17 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 17 g32p_row18_supplierClass
    g32p_row18_supplierClass_isConj g32p_supplierGroup13_support g32p_row18_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row18_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup13_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row18_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 17 c false (g32p_row18_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 17 c true (g32p_row18_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 17 c false (g32p_row18_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 17 c true (g32p_row18_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 17 c false (g32p_row18_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 17 c false (g32p_row18_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 17 c true (g32p_row18_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 17 c true (g32p_row18_coinduced_zero c hc true) 3

theorem g32p_row18_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup13_support →
      g32p_literalTraceValue (g32p_row18_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row18_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup13_support) :
    g32p_literalTraceValue (g32p_row18_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup13_support →
    g32p_literalTraceValue (g32p_row18_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row18_zeroTrace_block_00 r k
  · exact g32p_row18_zeroTrace_block_01 r k
  · exact g32p_row18_zeroTrace_block_02 r k
  · exact g32p_row18_zeroTrace_block_03 r k
  · exact g32p_row18_zeroTrace_block_04 r k
  · exact g32p_row18_zeroTrace_block_05 r k
  · exact g32p_row18_zeroTrace_block_06 r k

theorem g32p_row18_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup13_support) :
    (g32p_recordedInductionGenerators (g32p_row18_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row18_generatorIndex k) c) := by
  rw [g32p_row18_recordedGenerator_zero c hc k, g32p_row18_zeroTrace_arithmetic c k hc]
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

def g32p_row18_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [648, 648, 648] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [648, 648, 648])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [3456, 3456] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else [648, 648, 648]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [0, 0, 216, 216] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [-216] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [-216]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [-216])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [648, 648, 648]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [0, 0, 216, 216])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [3456, 3456])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [0, 0, 216, 216] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [648, 648, 648])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [3456, 3456] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [648, 648, 648] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [])))))))

theorem g32p_row18_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup13_support) :
    g32p_supplierTracePolynomialCheck 36 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) c) (g32p_literalTraceValue 17 c)
      [1, -1, 1] (g32p_row18_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row18_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_024
  · exact g32p_row18_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_050
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_096
  · exact g32p_row18_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup13_support) hc)
  · exact g32p_row18_tracePolynomial_101

theorem g32p_row18_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 17 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 17 c) := by
  by_cases hc : c ∈ g32p_supplierGroup13_support
  · have hclass (j : Fin 36) :
        IsConj (g32p_literalRepresentative c) (g32p_row18_groupEquiv j : g32p_G) ↔
          g32p_row18_supplierClassifier j = c := by
      simpa only [g32p_row18_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row18_supplierClass_iff (g32p_row18_groupEquiv j) c
    have hχ (j : Fin 36) :
        (g32p_recordedSupplierCharacters 17 (g32p_row18_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row18_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 17 (show (g32p_recordedSuppliers 17).H from g32p_row18_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row18_characterValues (g32p_row18_groupEquiv.symm (g32p_row18_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 17).H (g32p_recordedSupplierCharacters 17)
      (g32p_literalRepresentative c) g32p_row18_groupEquiv g32p_row18_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row18_characterValues j)).val) c 6 36
      (g32p_literalCentralizer c) (g32p_literalTraceValue 17 c) [1, -1, 1]
      (g32p_row18_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row18_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 17)))
      (g32p_row18_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row18_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row18_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
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

theorem g32p_row18_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
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

theorem g32p_row18_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
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

theorem g32p_row18_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
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

theorem g32p_row18_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row18_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row18_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 17 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
