import HodgeLean.Foundations.Program.G32PropFourSixPacked0380
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

theorem g32p_supplierGroup15_matrix_000 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 0 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 0 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 0 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_001 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 1 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 1 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 1 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_002 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 2 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 2 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 2 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_003 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 3 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 3 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 3 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_004 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 4 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 4 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 4 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_005 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 5 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 5 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 5 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_006 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 6 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 6 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 6 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_007 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 7 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 7 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 7 r) ∈ g32p_supplierGroup15_support := by
  decide +kernel

theorem g32p_supplierGroup15_matrix_008 : ∀ r : Fin 16,
    g32p_row20_groupNodes (g32p_finBlockIndex 144 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup15_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup15_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup15_source (g32p_finBlockIndex 144 8 r)).2 =
      g32p_supplierGroup15_classify (g32p_finBlockIndex 144 8 r) := by
  decide +kernel

theorem g32p_supplierGroup15_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup15_classify (g32p_finBlockIndex 144 8 r) ∈ g32p_supplierGroup15_support := by
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

theorem g32p_supplierGroup15_matrix (i : Fin 144) :
    g32p_row20_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source i).1 (g32p_supplierGroup15_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row20_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup15_source i).1 (g32p_supplierGroup15_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup15_matrix_000 r
  · exact g32p_supplierGroup15_matrix_001 r
  · exact g32p_supplierGroup15_matrix_002 r
  · exact g32p_supplierGroup15_matrix_003 r
  · exact g32p_supplierGroup15_matrix_004 r
  · exact g32p_supplierGroup15_matrix_005 r
  · exact g32p_supplierGroup15_matrix_006 r
  · exact g32p_supplierGroup15_matrix_007 r
  · exact g32p_supplierGroup15_matrix_008 r

theorem g32p_supplierGroup15_class (i : Fin 144) :
    g32p_supplierForest_classes (g32p_supplierGroup15_source i).1 (g32p_supplierGroup15_source i).2 =
      g32p_supplierGroup15_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup15_source i).1 (g32p_supplierGroup15_source i).2 =
      g32p_supplierGroup15_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup15_class_000 r
  · exact g32p_supplierGroup15_class_001 r
  · exact g32p_supplierGroup15_class_002 r
  · exact g32p_supplierGroup15_class_003 r
  · exact g32p_supplierGroup15_class_004 r
  · exact g32p_supplierGroup15_class_005 r
  · exact g32p_supplierGroup15_class_006 r
  · exact g32p_supplierGroup15_class_007 r
  · exact g32p_supplierGroup15_class_008 r

theorem g32p_supplierGroup15_support_mem (i : Fin 144) :
    g32p_supplierGroup15_classify i ∈ g32p_supplierGroup15_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup15_classify i ∈ g32p_supplierGroup15_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup15_support_000 r
  · exact g32p_supplierGroup15_support_001 r
  · exact g32p_supplierGroup15_support_002 r
  · exact g32p_supplierGroup15_support_003 r
  · exact g32p_supplierGroup15_support_004 r
  · exact g32p_supplierGroup15_support_005 r
  · exact g32p_supplierGroup15_support_006 r
  · exact g32p_supplierGroup15_support_007 r
  · exact g32p_supplierGroup15_support_008 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row20_supplierClassifier : Fin 144 → Fin 102 := g32p_supplierGroup15_classify

theorem g32p_row20_groupEquiv_isConj (i : Fin 144) :
    IsConj (g32p_row20_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row20_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup15_source i).1 (g32p_supplierGroup15_source i).2
  rw [g32p_supplierGroup15_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row20_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup15_matrix i)

def g32p_row20_supplierClass (h : (g32p_recordedSuppliers 19).H) : Fin 102 :=
  g32p_row20_supplierClassifier (g32p_row20_groupEquiv.symm h)

theorem g32p_row20_supplierClass_isConj (h : (g32p_recordedSuppliers 19).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row20_supplierClass h)) := by
  have he : (g32p_row20_groupEquiv (g32p_row20_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 19).H => (a : g32p_G))
      (g32p_row20_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row20_supplierClassifier (g32p_row20_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row20_groupEquiv_isConj (g32p_row20_groupEquiv.symm h)

theorem g32p_row20_supplierClass_iff (h : (g32p_recordedSuppliers 19).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row20_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row20_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row20_supplierClass_isConj h).symm

theorem g32p_row20_supplierClass_mem_support (h : (g32p_recordedSuppliers 19).H) :
    g32p_row20_supplierClass h ∈ g32p_supplierGroup15_support :=
  g32p_supplierGroup15_support_mem (g32p_row20_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row20_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 0) (g32p_literalTraceValue 19 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_000]
  decide +kernel

theorem g32p_row20_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 1 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 1) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 1) (g32p_literalTraceValue 19 1)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_001]
  decide +kernel

theorem g32p_row20_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 2 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 2) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 2) (g32p_literalTraceValue 19 2)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row20_traceCoefficients_002]
  decide +kernel

theorem g32p_row20_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 3 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 3) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 3) (g32p_literalTraceValue 19 3)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row20_traceCoefficients_003]
  decide +kernel

theorem g32p_row20_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 5 = [2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 5) (g32p_literalTraceValue 19 5)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row20_traceCoefficients_005]
  decide +kernel

theorem g32p_row20_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 7 = [0, 4, 0, 0, 2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 7) (g32p_literalTraceValue 19 7)
      [1, -1, 1] [-144, 144, 144] = true := by
  rw [g32p_row20_traceCoefficients_007]
  decide +kernel

theorem g32p_row20_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 8 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 8) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 8) (g32p_literalTraceValue 19 8)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_008]
  decide +kernel

theorem g32p_row20_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 17 = [0, 0, 2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 17) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 17) (g32p_literalTraceValue 19 17)
      [1, -1, 1] [0, 0, 288, 288] = true := by
  rw [g32p_row20_traceCoefficients_017]
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

theorem g32p_row20_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 18 = [2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 18) (g32p_literalTraceValue 19 18)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_018]
  decide +kernel

theorem g32p_row20_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 19 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 19) (g32p_literalTraceValue 19 19)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_019]
  decide +kernel

theorem g32p_row20_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 20 = [0, 0, 2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 20) (g32p_literalTraceValue 19 20)
      [1, -1, 1] [0, 0, 288, 288] = true := by
  rw [g32p_row20_traceCoefficients_020]
  decide +kernel

theorem g32p_row20_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 23 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 23) (g32p_literalTraceValue 19 23)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row20_traceCoefficients_023]
  decide +kernel

theorem g32p_row20_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 27 = [0, 4, 0, 0, 2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 27) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 27) (g32p_literalTraceValue 19 27)
      [1, -1, 1] [-144, 144, 144] = true := by
  rw [g32p_row20_traceCoefficients_027]
  decide +kernel

theorem g32p_row20_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 28 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 28) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 28) (g32p_literalTraceValue 19 28)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row20_traceCoefficients_028]
  decide +kernel

theorem g32p_row20_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 31 = [2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 31) (g32p_literalTraceValue 19 31)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row20_traceCoefficients_031]
  decide +kernel

theorem g32p_row20_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 37 = [1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 37) (g32p_literalTraceValue 19 37)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_037]
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

theorem g32p_row20_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 41 = [0, 0, 2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 41) (g32p_literalTraceValue 19 41)
      [1, -1, 1] [0, 0, 288, 288] = true := by
  rw [g32p_row20_traceCoefficients_041]
  decide +kernel

theorem g32p_row20_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 44 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 44) (g32p_literalTraceValue 19 44)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_044]
  decide +kernel

theorem g32p_row20_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 48 = [0, 0, 2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 48) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 48) (g32p_literalTraceValue 19 48)
      [1, -1, 1] [0, 0, 288, 288] = true := by
  rw [g32p_row20_traceCoefficients_048]
  decide +kernel

theorem g32p_row20_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 51 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 51) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 51) (g32p_literalTraceValue 19 51)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row20_traceCoefficients_051]
  decide +kernel

theorem g32p_row20_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 52 = [2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 52) (g32p_literalTraceValue 19 52)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row20_traceCoefficients_052]
  decide +kernel

theorem g32p_row20_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 55 = [0, 4, 0, 0, 2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 55) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 55) (g32p_literalTraceValue 19 55)
      [1, -1, 1] [-144, 144, 144] = true := by
  rw [g32p_row20_traceCoefficients_055]
  decide +kernel

theorem g32p_row20_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 58 = [0, 4, 0, 0, 2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 58) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 58) (g32p_literalTraceValue 19 58)
      [1, -1, 1] [-144, 144, 144] = true := by
  rw [g32p_row20_traceCoefficients_058]
  decide +kernel

theorem g32p_row20_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 61 = [0, 0, 2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 61) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 61) (g32p_literalTraceValue 19 61)
      [1, -1, 1] [0, 0, 288, 288] = true := by
  rw [g32p_row20_traceCoefficients_061]
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

theorem g32p_row20_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 63 = [0, 4, 0, 0, 2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 63) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 63) (g32p_literalTraceValue 19 63)
      [1, -1, 1] [-144, 144, 144] = true := by
  rw [g32p_row20_traceCoefficients_063]
  decide +kernel

theorem g32p_row20_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 64 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 64) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 64) (g32p_literalTraceValue 19 64)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_064]
  decide +kernel

theorem g32p_row20_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 65 = [2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 65) (g32p_literalTraceValue 19 65)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_065]
  decide +kernel

theorem g32p_row20_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 67 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 67) (g32p_literalTraceValue 19 67)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row20_traceCoefficients_067]
  decide +kernel

theorem g32p_row20_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 72 = [0, 4, 0, 0, 2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 72) (g32p_literalTraceValue 19 72)
      [1, -1, 1] [-144, 144, 144] = true := by
  rw [g32p_row20_traceCoefficients_072]
  decide +kernel

theorem g32p_row20_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 76 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 76) (g32p_literalTraceValue 19 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_076]
  decide +kernel

theorem g32p_row20_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 77 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 77) (g32p_literalTraceValue 19 77)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_077]
  decide +kernel

theorem g32p_row20_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 79 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 79) (g32p_literalTraceValue 19 79)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row20_traceCoefficients_079]
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

theorem g32p_row20_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 80 = [0, 0, 2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 80) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 80) (g32p_literalTraceValue 19 80)
      [1, -1, 1] [0, 0, 288, 288] = true := by
  rw [g32p_row20_traceCoefficients_080]
  decide +kernel

theorem g32p_row20_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 81 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 81) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 81) (g32p_literalTraceValue 19 81)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_081]
  decide +kernel

theorem g32p_row20_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 82 = [2] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 82) (g32p_literalTraceValue 19 82)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_082]
  decide +kernel

theorem g32p_row20_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 83 = [2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 83) (g32p_literalTraceValue 19 83)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row20_traceCoefficients_083]
  decide +kernel

theorem g32p_row20_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 85 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 85) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 85) (g32p_literalTraceValue 19 85)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row20_traceCoefficients_085]
  decide +kernel

theorem g32p_row20_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 87 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 87) (g32p_literalTraceValue 19 87)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_087]
  decide +kernel

theorem g32p_row20_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 88 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 88) (g32p_literalTraceValue 19 88)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_088]
  decide +kernel

theorem g32p_row20_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 89 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 89) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 89) (g32p_literalTraceValue 19 89)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row20_traceCoefficients_089]
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

theorem g32p_row20_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 90 = [2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 90) (g32p_literalTraceValue 19 90)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row20_traceCoefficients_090]
  decide +kernel

theorem g32p_row20_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 91 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 91) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 91) (g32p_literalTraceValue 19 91)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_091]
  decide +kernel

theorem g32p_row20_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 93 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 93) (g32p_literalTraceValue 19 93)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row20_traceCoefficients_093]
  decide +kernel

theorem g32p_row20_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 94 = [2, 0, 0, 4] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 94) (g32p_literalTraceValue 19 94)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row20_traceCoefficients_094]
  decide +kernel

theorem g32p_row20_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 95 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 95) (g32p_literalTraceValue 19 95)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row20_traceCoefficients_095]
  decide +kernel

theorem g32p_row20_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 96 = [1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 96) (g32p_literalTraceValue 19 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_096]
  decide +kernel

theorem g32p_row20_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 97 = [1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 97) (g32p_literalTraceValue 19 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_097]
  decide +kernel

theorem g32p_row20_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 98 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 98) (g32p_literalTraceValue 19 98)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_098]
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

theorem g32p_row20_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 99) (g32p_literalTraceValue 19 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_099]
  decide +kernel

theorem g32p_row20_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 100 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 100) (g32p_literalTraceValue 19 100)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row20_traceCoefficients_100]
  decide +kernel

theorem g32p_row20_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 101 = [1] := by
  decide +kernel

theorem g32p_row20_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) 101) (g32p_literalTraceValue 19 101)
      [1, -1, 1] [] = true := by
  rw [g32p_row20_traceCoefficients_101]
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

def g32p_row20_generatorIndex : Fin 8 → Fin 408 :=
  ![19, 70, 121, 172, 242, 243, 344, 345]

theorem g32p_row20_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup15_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 19 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 19 g32p_row20_supplierClass
    g32p_row20_supplierClass_isConj g32p_supplierGroup15_support g32p_row20_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row20_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup15_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row20_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 19 c false (g32p_row20_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 19 c true (g32p_row20_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 19 c false (g32p_row20_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 19 c true (g32p_row20_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 19 c false (g32p_row20_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 19 c false (g32p_row20_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 19 c true (g32p_row20_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 19 c true (g32p_row20_coinduced_zero c hc true) 3

theorem g32p_row20_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup15_support →
      g32p_literalTraceValue (g32p_row20_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row20_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup15_support) :
    g32p_literalTraceValue (g32p_row20_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup15_support →
    g32p_literalTraceValue (g32p_row20_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row20_zeroTrace_block_00 r k
  · exact g32p_row20_zeroTrace_block_01 r k
  · exact g32p_row20_zeroTrace_block_02 r k
  · exact g32p_row20_zeroTrace_block_03 r k
  · exact g32p_row20_zeroTrace_block_04 r k
  · exact g32p_row20_zeroTrace_block_05 r k
  · exact g32p_row20_zeroTrace_block_06 r k

theorem g32p_row20_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup15_support) :
    (g32p_recordedInductionGenerators (g32p_row20_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row20_generatorIndex k) c) := by
  rw [g32p_row20_recordedGenerator_zero c hc k, g32p_row20_zeroTrace_arithmetic c k hc]
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

def g32p_row20_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [3888, 3888, 3888])) else (if i.val < 4 then [432, 432, 432] else (if i.val < 5 then [] else [1152, 1152]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [-144, 144, 144] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else [0, 0, 288, 288]))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [0, 0, 288, 288])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [432, 432, 432] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [-144, 144, 144])) else (if i.val < 29 then [3888, 3888, 3888] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [1152, 1152] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [0, 0, 288, 288] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else [0, 0, 288, 288]) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [432, 432, 432] else (if i.val < 53 then [1152, 1152] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [-144, 144, 144] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [-144, 144, 144] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [0, 0, 288, 288] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [-144, 144, 144] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [3888, 3888, 3888] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [-144, 144, 144] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [432, 432, 432] else (if i.val < 81 then [0, 0, 288, 288] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [1152, 1152] else [])) else (if i.val < 87 then (if i.val < 86 then [432, 432, 432] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [432, 432, 432] else (if i.val < 91 then [1152, 1152] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [3888, 3888, 3888] else [1152, 1152]))) else (if i.val < 98 then (if i.val < 96 then [3888, 3888, 3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [3888, 3888, 3888] else [])))))))

theorem g32p_row20_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup15_support) :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) c) (g32p_literalTraceValue 19 c)
      [1, -1, 1] (g32p_row20_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row20_tracePolynomial_000
  · exact g32p_row20_tracePolynomial_001
  · exact g32p_row20_tracePolynomial_002
  · exact g32p_row20_tracePolynomial_003
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_007
  · exact g32p_row20_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_017
  · exact g32p_row20_tracePolynomial_018
  · exact g32p_row20_tracePolynomial_019
  · exact g32p_row20_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_027
  · exact g32p_row20_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_044
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_051
  · exact g32p_row20_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_055
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_058
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_063
  · exact g32p_row20_tracePolynomial_064
  · exact g32p_row20_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_076
  · exact g32p_row20_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_079
  · exact g32p_row20_tracePolynomial_080
  · exact g32p_row20_tracePolynomial_081
  · exact g32p_row20_tracePolynomial_082
  · exact g32p_row20_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_085
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_087
  · exact g32p_row20_tracePolynomial_088
  · exact g32p_row20_tracePolynomial_089
  · exact g32p_row20_tracePolynomial_090
  · exact g32p_row20_tracePolynomial_091
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup15_support) hc)
  · exact g32p_row20_tracePolynomial_093
  · exact g32p_row20_tracePolynomial_094
  · exact g32p_row20_tracePolynomial_095
  · exact g32p_row20_tracePolynomial_096
  · exact g32p_row20_tracePolynomial_097
  · exact g32p_row20_tracePolynomial_098
  · exact g32p_row20_tracePolynomial_099
  · exact g32p_row20_tracePolynomial_100
  · exact g32p_row20_tracePolynomial_101

theorem g32p_row20_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 19 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 19 c) := by
  by_cases hc : c ∈ g32p_supplierGroup15_support
  · have hclass (j : Fin 144) :
        IsConj (g32p_literalRepresentative c) (g32p_row20_groupEquiv j : g32p_G) ↔
          g32p_row20_supplierClassifier j = c := by
      simpa only [g32p_row20_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row20_supplierClass_iff (g32p_row20_groupEquiv j) c
    have hχ (j : Fin 144) :
        (g32p_recordedSupplierCharacters 19 (g32p_row20_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row20_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 19 (show (g32p_recordedSuppliers 19).H from g32p_row20_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row20_characterValues (g32p_row20_groupEquiv.symm (g32p_row20_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 19).H (g32p_recordedSupplierCharacters 19)
      (g32p_literalRepresentative c) g32p_row20_groupEquiv g32p_row20_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row20_characterValues j)).val) c 6 144
      (g32p_literalCentralizer c) (g32p_literalTraceValue 19 c) [1, -1, 1]
      (g32p_row20_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row20_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 19)))
      (g32p_row20_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row20_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row20_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
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

theorem g32p_row20_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
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

theorem g32p_row20_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
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

theorem g32p_row20_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row20_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row20_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 19 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
