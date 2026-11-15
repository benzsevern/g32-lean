import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow15
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
set_option maxRecDepth 2048

def g32p_supplierGroup10_source : Fin 96 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 48 then (if i.val < 24 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (47, 208) else (86, 199))) else (if i.val < 4 then (42, 183) else (if i.val < 5 then (0, 37) else (46, 17)))) else (if i.val < 9 then (if i.val < 7 then (43, 218) else (if i.val < 8 then (53, 197) else (30, 148))) else (if i.val < 10 then (84, 90) else (if i.val < 11 then (0, 99) else (29, 134))))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then (90, 208) else (if i.val < 14 then (62, 178) else (73, 96))) else (if i.val < 16 then (34, 124) else (if i.val < 17 then (51, 15) else (25, 125)))) else (if i.val < 21 then (if i.val < 19 then (40, 0) else (if i.val < 20 then (11, 61) else (102, 38))) else (if i.val < 22 then (54, 211) else (if i.val < 23 then (66, 31) else (0, 96)))))) else (if i.val < 36 then (if i.val < 30 then (if i.val < 27 then (if i.val < 25 then (31, 214) else (if i.val < 26 then (85, 108) else (51, 26))) else (if i.val < 28 then (111, 224) else (if i.val < 29 then (32, 175) else (0, 101)))) else (if i.val < 33 then (if i.val < 31 then (102, 10) else (if i.val < 32 then (25, 109) else (56, 16))) else (if i.val < 34 then (12, 11) else (if i.val < 35 then (55, 156) else (56, 163))))) else (if i.val < 42 then (if i.val < 39 then (if i.val < 37 then (32, 174) else (if i.val < 38 then (31, 213) else (20, 200))) else (if i.val < 40 then (72, 143) else (if i.val < 41 then (98, 186) else (67, 127)))) else (if i.val < 45 then (if i.val < 43 then (41, 27) else (if i.val < 44 then (47, 150) else (66, 68))) else (if i.val < 46 then (85, 196) else (if i.val < 47 then (9, 201) else (109, 228))))))) else (if i.val < 72 then (if i.val < 60 then (if i.val < 54 then (if i.val < 51 then (if i.val < 49 then (27, 175) else (if i.val < 50 then (62, 27) else (72, 195))) else (if i.val < 52 then (71, 145) else (if i.val < 53 then (72, 176) else (83, 68)))) else (if i.val < 57 then (if i.val < 55 then (66, 180) else (if i.val < 56 then (6, 161) else (20, 105))) else (if i.val < 58 then (72, 34) else (if i.val < 59 then (46, 164) else (0, 188))))) else (if i.val < 66 then (if i.val < 63 then (if i.val < 61 then (0, 97) else (if i.val < 62 then (5, 145) else (83, 7))) else (if i.val < 64 then (70, 37) else (if i.val < 65 then (129, 202) else (14, 217)))) else (if i.val < 69 then (if i.val < 67 then (2, 105) else (if i.val < 68 then (38, 79) else (2, 97))) else (if i.val < 70 then (69, 221) else (if i.val < 71 then (107, 105) else (62, 177)))))) else (if i.val < 84 then (if i.val < 78 then (if i.val < 75 then (if i.val < 73 then (79, 181) else (if i.val < 74 then (79, 107) else (100, 45))) else (if i.val < 76 then (35, 62) else (if i.val < 77 then (63, 1) else (101, 177)))) else (if i.val < 81 then (if i.val < 79 then (73, 154) else (if i.val < 80 then (41, 5) else (93, 183))) else (if i.val < 82 then (5, 116) else (if i.val < 83 then (140, 39) else (111, 165))))) else (if i.val < 90 then (if i.val < 87 then (if i.val < 85 then (31, 165) else (if i.val < 86 then (85, 42) else (131, 122))) else (if i.val < 88 then (43, 171) else (if i.val < 89 then (12, 120) else (74, 130)))) else (if i.val < 93 then (if i.val < 91 then (56, 162) else (if i.val < 92 then (49, 236) else (60, 196))) else (if i.val < 94 then (38, 171) else (if i.val < 95 then (47, 26) else (6, 146))))))))

def g32p_supplierGroup10_classify : Fin 96 → Fin 102 :=
  fun i => (if i.val < 48 then (if i.val < 24 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 13 else 5)) else (if i.val < 4 then 69 else (if i.val < 5 then 37 else 83))) else (if i.val < 9 then (if i.val < 7 then 83 else (if i.val < 8 then 18 else 94)) else (if i.val < 10 then 83 else (if i.val < 11 then 99 else 69)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 31 else (if i.val < 14 then 34 else 13)) else (if i.val < 16 then 13 else (if i.val < 17 then 34 else 13))) else (if i.val < 21 then (if i.val < 19 then 5 else (if i.val < 20 then 69 else 13)) else (if i.val < 22 then 94 else (if i.val < 23 then 69 else 96))))) else (if i.val < 36 then (if i.val < 30 then (if i.val < 27 then (if i.val < 25 then 5 else (if i.val < 26 then 5 else 65)) else (if i.val < 28 then 90 else (if i.val < 29 then 5 else 101))) else (if i.val < 33 then (if i.val < 31 then 52 else (if i.val < 32 then 52 else 90)) else (if i.val < 34 then 52 else (if i.val < 35 then 52 else 5)))) else (if i.val < 42 then (if i.val < 39 then (if i.val < 37 then 18 else (if i.val < 38 then 5 else 34)) else (if i.val < 40 then 52 else (if i.val < 41 then 13 else 69))) else (if i.val < 45 then (if i.val < 43 then 69 else (if i.val < 44 then 13 else 69)) else (if i.val < 46 then 31 else (if i.val < 47 then 34 else 69)))))) else (if i.val < 72 then (if i.val < 60 then (if i.val < 54 then (if i.val < 51 then (if i.val < 49 then 90 else (if i.val < 50 then 34 else 13)) else (if i.val < 52 then 13 else (if i.val < 53 then 13 else 94))) else (if i.val < 57 then (if i.val < 55 then 69 else (if i.val < 56 then 31 else 31)) else (if i.val < 58 then 82 else (if i.val < 59 then 83 else 31)))) else (if i.val < 66 then (if i.val < 63 then (if i.val < 61 then 97 else (if i.val < 62 then 94 else 94)) else (if i.val < 64 then 83 else (if i.val < 65 then 94 else 94))) else (if i.val < 69 then (if i.val < 67 then 31 else (if i.val < 68 then 65 else 31)) else (if i.val < 70 then 83 else (if i.val < 71 then 94 else 34))))) else (if i.val < 84 then (if i.val < 78 then (if i.val < 75 then (if i.val < 73 then 34 else (if i.val < 74 then 34 else 52)) else (if i.val < 76 then 13 else (if i.val < 77 then 34 else 83))) else (if i.val < 81 then (if i.val < 79 then 13 else (if i.val < 80 then 69 else 69)) else (if i.val < 82 then 69 else (if i.val < 83 then 90 else 90)))) else (if i.val < 90 then (if i.val < 87 then (if i.val < 85 then 90 else (if i.val < 86 then 90 else 90)) else (if i.val < 88 then 52 else (if i.val < 89 then 82 else 52))) else (if i.val < 93 then (if i.val < 91 then 5 else (if i.val < 92 then 34 else 34)) else (if i.val < 94 then 34 else (if i.val < 95 then 83 else 31)))))))

def g32p_supplierGroup10_support : Finset (Fin 102) :=
  {0, 5, 13, 18, 31, 34, 37, 52, 65, 69, 82, 83, 90, 94, 96, 97, 99, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup10_matrix_000 : ∀ r : Fin 16,
    g32p_row15_groupNodes (g32p_finBlockIndex 96 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 0 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup10_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 0 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 0 r)).2 =
      g32p_supplierGroup10_classify (g32p_finBlockIndex 96 0 r) := by
  decide +kernel

theorem g32p_supplierGroup10_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup10_classify (g32p_finBlockIndex 96 0 r) ∈ g32p_supplierGroup10_support := by
  decide +kernel

theorem g32p_supplierGroup10_matrix_001 : ∀ r : Fin 16,
    g32p_row15_groupNodes (g32p_finBlockIndex 96 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 1 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup10_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 1 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 1 r)).2 =
      g32p_supplierGroup10_classify (g32p_finBlockIndex 96 1 r) := by
  decide +kernel

theorem g32p_supplierGroup10_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup10_classify (g32p_finBlockIndex 96 1 r) ∈ g32p_supplierGroup10_support := by
  decide +kernel

theorem g32p_supplierGroup10_matrix_002 : ∀ r : Fin 16,
    g32p_row15_groupNodes (g32p_finBlockIndex 96 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 2 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup10_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 2 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 2 r)).2 =
      g32p_supplierGroup10_classify (g32p_finBlockIndex 96 2 r) := by
  decide +kernel

theorem g32p_supplierGroup10_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup10_classify (g32p_finBlockIndex 96 2 r) ∈ g32p_supplierGroup10_support := by
  decide +kernel

theorem g32p_supplierGroup10_matrix_003 : ∀ r : Fin 16,
    g32p_row15_groupNodes (g32p_finBlockIndex 96 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 3 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup10_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 3 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 3 r)).2 =
      g32p_supplierGroup10_classify (g32p_finBlockIndex 96 3 r) := by
  decide +kernel

theorem g32p_supplierGroup10_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup10_classify (g32p_finBlockIndex 96 3 r) ∈ g32p_supplierGroup10_support := by
  decide +kernel

theorem g32p_supplierGroup10_matrix_004 : ∀ r : Fin 16,
    g32p_row15_groupNodes (g32p_finBlockIndex 96 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 4 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup10_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 4 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 4 r)).2 =
      g32p_supplierGroup10_classify (g32p_finBlockIndex 96 4 r) := by
  decide +kernel

theorem g32p_supplierGroup10_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup10_classify (g32p_finBlockIndex 96 4 r) ∈ g32p_supplierGroup10_support := by
  decide +kernel

theorem g32p_supplierGroup10_matrix_005 : ∀ r : Fin 16,
    g32p_row15_groupNodes (g32p_finBlockIndex 96 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 5 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup10_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup10_source (g32p_finBlockIndex 96 5 r)).1 (g32p_supplierGroup10_source (g32p_finBlockIndex 96 5 r)).2 =
      g32p_supplierGroup10_classify (g32p_finBlockIndex 96 5 r) := by
  decide +kernel

theorem g32p_supplierGroup10_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup10_classify (g32p_finBlockIndex 96 5 r) ∈ g32p_supplierGroup10_support := by
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

theorem g32p_supplierGroup10_matrix (i : Fin 96) :
    g32p_row15_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source i).1 (g32p_supplierGroup10_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row15_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup10_source i).1 (g32p_supplierGroup10_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup10_matrix_000 r
  · exact g32p_supplierGroup10_matrix_001 r
  · exact g32p_supplierGroup10_matrix_002 r
  · exact g32p_supplierGroup10_matrix_003 r
  · exact g32p_supplierGroup10_matrix_004 r
  · exact g32p_supplierGroup10_matrix_005 r

theorem g32p_supplierGroup10_class (i : Fin 96) :
    g32p_supplierForest_classes (g32p_supplierGroup10_source i).1 (g32p_supplierGroup10_source i).2 =
      g32p_supplierGroup10_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup10_source i).1 (g32p_supplierGroup10_source i).2 =
      g32p_supplierGroup10_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup10_class_000 r
  · exact g32p_supplierGroup10_class_001 r
  · exact g32p_supplierGroup10_class_002 r
  · exact g32p_supplierGroup10_class_003 r
  · exact g32p_supplierGroup10_class_004 r
  · exact g32p_supplierGroup10_class_005 r

theorem g32p_supplierGroup10_support_mem (i : Fin 96) :
    g32p_supplierGroup10_classify i ∈ g32p_supplierGroup10_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup10_classify i ∈ g32p_supplierGroup10_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup10_support_000 r
  · exact g32p_supplierGroup10_support_001 r
  · exact g32p_supplierGroup10_support_002 r
  · exact g32p_supplierGroup10_support_003 r
  · exact g32p_supplierGroup10_support_004 r
  · exact g32p_supplierGroup10_support_005 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row15_supplierClassifier : Fin 96 → Fin 102 := g32p_supplierGroup10_classify

theorem g32p_row15_groupEquiv_isConj (i : Fin 96) :
    IsConj (g32p_row15_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row15_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup10_source i).1 (g32p_supplierGroup10_source i).2
  rw [g32p_supplierGroup10_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row15_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup10_matrix i)

def g32p_row15_supplierClass (h : (g32p_recordedSuppliers 14).H) : Fin 102 :=
  g32p_row15_supplierClassifier (g32p_row15_groupEquiv.symm h)

theorem g32p_row15_supplierClass_isConj (h : (g32p_recordedSuppliers 14).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row15_supplierClass h)) := by
  have he : (g32p_row15_groupEquiv (g32p_row15_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 14).H => (a : g32p_G))
      (g32p_row15_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row15_supplierClassifier (g32p_row15_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row15_groupEquiv_isConj (g32p_row15_groupEquiv.symm h)

theorem g32p_row15_supplierClass_iff (h : (g32p_recordedSuppliers 14).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row15_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row15_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row15_supplierClass_isConj h).symm

theorem g32p_row15_supplierClass_mem_support (h : (g32p_recordedSuppliers 14).H) :
    g32p_row15_supplierClass h ∈ g32p_supplierGroup10_support :=
  g32p_supplierGroup10_support_mem (g32p_row15_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row15_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 0) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 0) (g32p_literalTraceValue 14 0)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row15_traceCoefficients_000]
  decide +kernel

theorem g32p_row15_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 5 = [2, 0, 0, 1, 0, 0, 4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 5) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 5) (g32p_literalTraceValue 14 5)
      [1, 0, -1, 0, 1] [1152, 0, 1152, 288, 0, 288] = true := by
  rw [g32p_row15_traceCoefficients_005]
  decide +kernel

theorem g32p_row15_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 13 = [0, 6, 0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 13) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 13) (g32p_literalTraceValue 14 13)
      [1, 0, -1, 0, 1] [0, 1728, 0, 1728] = true := by
  rw [g32p_row15_traceCoefficients_013]
  decide +kernel

theorem g32p_row15_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 18 = [1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 18) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 18) (g32p_literalTraceValue 14 18)
      [1, 0, -1, 0, 1] [1728, 0, 1728] = true := by
  rw [g32p_row15_traceCoefficients_018]
  decide +kernel

theorem g32p_row15_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 31 = [0, 0, 2, 0, 0, 1, 0, 0, 4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 31) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 31) (g32p_literalTraceValue 14 31)
      [1, 0, -1, 0, 1] [576, 0, 1152, 0, 1152, 288, 0, 288] = true := by
  rw [g32p_row15_traceCoefficients_031]
  decide +kernel

theorem g32p_row15_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 34 = [0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 34) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 34) (g32p_literalTraceValue 14 34)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 0, 1728, 0, 1728] = true := by
  rw [g32p_row15_traceCoefficients_034]
  decide +kernel

theorem g32p_row15_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 37 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 37) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 37) (g32p_literalTraceValue 14 37)
      [1, 0, -1, 0, 1] [-155520] = true := by
  rw [g32p_row15_traceCoefficients_037]
  decide +kernel

theorem g32p_row15_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 52 = [0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 52) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 52) (g32p_literalTraceValue 14 52)
      [1, 0, -1, 0, 1] [0, 288, 0, 288, 1152, 0, 1152] = true := by
  rw [g32p_row15_traceCoefficients_052]
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

theorem g32p_row15_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 65 = [0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 65) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 65) (g32p_literalTraceValue 14 65)
      [1, 0, -1, 0, 1] [0, 0, 1728, 0, 1728] = true := by
  rw [g32p_row15_traceCoefficients_065]
  decide +kernel

theorem g32p_row15_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 69 = [0, 0, 0, 6, 0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 69) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 69) (g32p_literalTraceValue 14 69)
      [1, 0, -1, 0, 1] [0, 0, 0, 1728, 0, 1728] = true := by
  rw [g32p_row15_traceCoefficients_069]
  decide +kernel

theorem g32p_row15_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 82 = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 82) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 82) (g32p_literalTraceValue 14 82)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 1728, 0, 1728] = true := by
  rw [g32p_row15_traceCoefficients_082]
  decide +kernel

theorem g32p_row15_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 83 = [0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 2] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 83) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 83) (g32p_literalTraceValue 14 83)
      [1, 0, -1, 0, 1] [0, 288, 0, 288, 576, 0, 576] = true := by
  rw [g32p_row15_traceCoefficients_083]
  decide +kernel

theorem g32p_row15_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 90 = [0, 0, 4, 0, 0, 1, 0, 0, 2, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 90) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 90) (g32p_literalTraceValue 14 90)
      [1, 0, -1, 0, 1] [-576, 0, 576, 0, 576, 288, 0, 288] = true := by
  rw [g32p_row15_traceCoefficients_090]
  decide +kernel

theorem g32p_row15_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 94 = [4, 0, 0, 1, 0, 0, 2, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 94) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 94) (g32p_literalTraceValue 14 94)
      [1, 0, -1, 0, 1] [576, 0, 576, 288, 0, 288] = true := by
  rw [g32p_row15_traceCoefficients_094]
  decide +kernel

theorem g32p_row15_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 96 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 96) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 96) (g32p_literalTraceValue 14 96)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row15_traceCoefficients_096]
  decide +kernel

theorem g32p_row15_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 97 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 97) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 97) (g32p_literalTraceValue 14 97)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 155520, 0, 155520] = true := by
  rw [g32p_row15_traceCoefficients_097]
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

theorem g32p_row15_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 99 = [0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 99) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 99) (g32p_literalTraceValue 14 99)
      [1, 0, -1, 0, 1] [155520, 0, 155520] = true := by
  rw [g32p_row15_traceCoefficients_099]
  decide +kernel

theorem g32p_row15_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 101 = [0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row15_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer 101) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) 101) (g32p_literalTraceValue 14 101)
      [1, 0, -1, 0, 1] [155520, 0, 155520, 0, 155520] = true := by
  rw [g32p_row15_traceCoefficients_101]
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

def g32p_row15_generatorIndex : Fin 8 → Fin 408 :=
  ![14, 65, 116, 167, 232, 233, 334, 335]

theorem g32p_row15_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup10_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 14 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 14 g32p_row15_supplierClass
    g32p_row15_supplierClass_isConj g32p_supplierGroup10_support g32p_row15_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row15_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup10_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row15_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 14 c false (g32p_row15_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 14 c true (g32p_row15_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 14 c false (g32p_row15_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 14 c true (g32p_row15_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 14 c false (g32p_row15_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 14 c false (g32p_row15_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 14 c true (g32p_row15_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 14 c true (g32p_row15_coinduced_zero c hc true) 3

theorem g32p_row15_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup10_support →
      g32p_literalTraceValue (g32p_row15_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row15_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup10_support) :
    g32p_literalTraceValue (g32p_row15_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup10_support →
    g32p_literalTraceValue (g32p_row15_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row15_zeroTrace_block_00 r k
  · exact g32p_row15_zeroTrace_block_01 r k
  · exact g32p_row15_zeroTrace_block_02 r k
  · exact g32p_row15_zeroTrace_block_03 r k
  · exact g32p_row15_zeroTrace_block_04 r k
  · exact g32p_row15_zeroTrace_block_05 r k
  · exact g32p_row15_zeroTrace_block_06 r k

theorem g32p_row15_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup10_support) :
    (g32p_recordedInductionGenerators (g32p_row15_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row15_generatorIndex k) c) := by
  rw [g32p_row15_recordedGenerator_zero c hc k, g32p_row15_zeroTrace_arithmetic c k hc]
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

def g32p_row15_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else [1152, 0, 1152, 288, 0, 288]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 1728, 0, 1728] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [1728, 0, 1728] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [576, 0, 1152, 0, 1152, 288, 0, 288] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [0, 0, 0, 0, 0, 1728, 0, 1728] else []) else (if i.val < 37 then [] else [-155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [0, 288, 0, 288, 1152, 0, 1152] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [0, 0, 1728, 0, 1728])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [0, 0, 0, 1728, 0, 1728] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 0, 0, 1728, 0, 1728] else (if i.val < 84 then [0, 288, 0, 288, 576, 0, 576] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [-576, 0, 576, 0, 576, 288, 0, 288] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [576, 0, 576, 288, 0, 288]))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [0, 0, 0, 0, 155520, 0, 155520])) else (if i.val < 100 then (if i.val < 99 then [] else [155520, 0, 155520]) else (if i.val < 101 then [] else [155520, 0, 155520, 0, 155520])))))))

theorem g32p_row15_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup10_support) :
    g32p_supplierTracePolynomialCheck 96 (g32p_literalCentralizer c) 12
      (g32p_supplierTraceCoefficients g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) c) (g32p_literalTraceValue 14 c)
      [1, 0, -1, 0, 1] (g32p_row15_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row15_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_082
  · exact g32p_row15_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_096
  · exact g32p_row15_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup10_support) hc)
  · exact g32p_row15_tracePolynomial_101

theorem g32p_row15_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 14 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 14 c) := by
  by_cases hc : c ∈ g32p_supplierGroup10_support
  · have hclass (j : Fin 96) :
        IsConj (g32p_literalRepresentative c) (g32p_row15_groupEquiv j : g32p_G) ↔
          g32p_row15_supplierClassifier j = c := by
      simpa only [g32p_row15_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row15_supplierClass_iff (g32p_row15_groupEquiv j) c
    have hχ (j : Fin 96) :
        (g32p_recordedSupplierCharacters 14 (g32p_row15_groupEquiv j) : ℂ) =
          g32p_root 12 ^ (Multiplicative.toAdd (g32p_row15_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 14 (show (g32p_recordedSuppliers 14).H from g32p_row15_groupEquiv j)]
      change g32p_root 12 ^ (Multiplicative.toAdd
        (g32p_row15_characterValues (g32p_row15_groupEquiv.symm (g32p_row15_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 14).H (g32p_recordedSupplierCharacters 14)
      (g32p_literalRepresentative c) g32p_row15_groupEquiv g32p_row15_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row15_characterValues j)).val) c 12 96
      (g32p_literalCentralizer c) (g32p_literalTraceValue 14 c) [1, 0, -1, 0, 1]
      (g32p_row15_traceQuotient c) (g32p_root 12) (by decide)
      g32p_row15_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_twelve
        (g32p_root_primitive (g32p_recordedSuppliers 14)))
      (g32p_row15_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 12 (by decide)] at h
    exact h
  · exact g32p_row15_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row15_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
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

theorem g32p_row15_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
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

theorem g32p_row15_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
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

theorem g32p_row15_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
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

theorem g32p_row15_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
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

theorem g32p_row15_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
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

theorem g32p_row15_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row15_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row15_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 14 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
