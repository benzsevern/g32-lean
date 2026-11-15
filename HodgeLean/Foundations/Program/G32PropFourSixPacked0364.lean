import HodgeLean.Foundations.Program.G32PropFourSixPacked0363
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

theorem g32p_supplierGroup09_matrix_000 : ∀ r : Fin 16,
    g32p_row14_groupNodes (g32p_finBlockIndex 24 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup09_source (g32p_finBlockIndex 24 0 r)).1 (g32p_supplierGroup09_source (g32p_finBlockIndex 24 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup09_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup09_source (g32p_finBlockIndex 24 0 r)).1 (g32p_supplierGroup09_source (g32p_finBlockIndex 24 0 r)).2 =
      g32p_supplierGroup09_classify (g32p_finBlockIndex 24 0 r) := by
  decide +kernel

theorem g32p_supplierGroup09_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup09_classify (g32p_finBlockIndex 24 0 r) ∈ g32p_supplierGroup09_support := by
  decide +kernel

theorem g32p_supplierGroup09_matrix_001 : ∀ r : Fin 16,
    g32p_row14_groupNodes (g32p_finBlockIndex 24 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup09_source (g32p_finBlockIndex 24 1 r)).1 (g32p_supplierGroup09_source (g32p_finBlockIndex 24 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup09_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup09_source (g32p_finBlockIndex 24 1 r)).1 (g32p_supplierGroup09_source (g32p_finBlockIndex 24 1 r)).2 =
      g32p_supplierGroup09_classify (g32p_finBlockIndex 24 1 r) := by
  decide +kernel

theorem g32p_supplierGroup09_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup09_classify (g32p_finBlockIndex 24 1 r) ∈ g32p_supplierGroup09_support := by
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

theorem g32p_supplierGroup09_matrix (i : Fin 24) :
    g32p_row14_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup09_source i).1 (g32p_supplierGroup09_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row14_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup09_source i).1 (g32p_supplierGroup09_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup09_matrix_000 r
  · exact g32p_supplierGroup09_matrix_001 r

theorem g32p_supplierGroup09_class (i : Fin 24) :
    g32p_supplierForest_classes (g32p_supplierGroup09_source i).1 (g32p_supplierGroup09_source i).2 =
      g32p_supplierGroup09_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup09_source i).1 (g32p_supplierGroup09_source i).2 =
      g32p_supplierGroup09_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup09_class_000 r
  · exact g32p_supplierGroup09_class_001 r

theorem g32p_supplierGroup09_support_mem (i : Fin 24) :
    g32p_supplierGroup09_classify i ∈ g32p_supplierGroup09_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup09_classify i ∈ g32p_supplierGroup09_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup09_support_000 r
  · exact g32p_supplierGroup09_support_001 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row14_supplierClassifier : Fin 24 → Fin 102 := g32p_supplierGroup09_classify

theorem g32p_row14_groupEquiv_isConj (i : Fin 24) :
    IsConj (g32p_row14_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row14_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup09_source i).1 (g32p_supplierGroup09_source i).2
  rw [g32p_supplierGroup09_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row14_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup09_matrix i)

def g32p_row14_supplierClass (h : (g32p_recordedSuppliers 13).H) : Fin 102 :=
  g32p_row14_supplierClassifier (g32p_row14_groupEquiv.symm h)

theorem g32p_row14_supplierClass_isConj (h : (g32p_recordedSuppliers 13).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row14_supplierClass h)) := by
  have he : (g32p_row14_groupEquiv (g32p_row14_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 13).H => (a : g32p_G))
      (g32p_row14_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row14_supplierClassifier (g32p_row14_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row14_groupEquiv_isConj (g32p_row14_groupEquiv.symm h)

theorem g32p_row14_supplierClass_iff (h : (g32p_recordedSuppliers 13).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row14_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row14_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row14_supplierClass_isConj h).symm

theorem g32p_row14_supplierClass_mem_support (h : (g32p_recordedSuppliers 13).H) :
    g32p_row14_supplierClass h ∈ g32p_supplierGroup09_support :=
  g32p_supplierGroup09_support_mem (g32p_row14_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row14_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 0) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 0) (g32p_literalTraceValue 13 0)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row14_traceCoefficients_000]
  decide +kernel

theorem g32p_row14_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 5 = [0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 5) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 5) (g32p_literalTraceValue 13 5)
      [1, 0, -1, 0, 1] [0, 0, 0, 288, 0, 288] = true := by
  rw [g32p_row14_traceCoefficients_005]
  decide +kernel

theorem g32p_row14_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 17 = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 17) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 17) (g32p_literalTraceValue 13 17)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 0, 72, 0, 72] = true := by
  rw [g32p_row14_traceCoefficients_017]
  decide +kernel

theorem g32p_row14_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 18 = [1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 18) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 18) (g32p_literalTraceValue 13 18)
      [1, 0, -1, 0, 1] [1728, 0, 1728] = true := by
  rw [g32p_row14_traceCoefficients_018]
  decide +kernel

theorem g32p_row14_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 27 = [0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 27) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 27) (g32p_literalTraceValue 13 27)
      [1, 0, -1, 0, 1] [0, 72, 0, 72] = true := by
  rw [g32p_row14_traceCoefficients_027]
  decide +kernel

theorem g32p_row14_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 28 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 28) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 28) (g32p_literalTraceValue 13 28)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 3888, 0, 3888] = true := by
  rw [g32p_row14_traceCoefficients_028]
  decide +kernel

theorem g32p_row14_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 51 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 51) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 51) (g32p_literalTraceValue 13 51)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 432, 0, 432] = true := by
  rw [g32p_row14_traceCoefficients_051]
  decide +kernel

theorem g32p_row14_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 55 = [0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 55) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 55) (g32p_literalTraceValue 13 55)
      [1, 0, -1, 0, 1] [0, 72, 0, 72] = true := by
  rw [g32p_row14_traceCoefficients_055]
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

theorem g32p_row14_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 61 = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 61) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 61) (g32p_literalTraceValue 13 61)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 0, 72, 0, 72] = true := by
  rw [g32p_row14_traceCoefficients_061]
  decide +kernel

theorem g32p_row14_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 64 = [0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 64) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 64) (g32p_literalTraceValue 13 64)
      [1, 0, -1, 0, 1] [432, 0, 432, 0, 432] = true := by
  rw [g32p_row14_traceCoefficients_064]
  decide +kernel

theorem g32p_row14_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 85 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 85) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 85) (g32p_literalTraceValue 13 85)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row14_traceCoefficients_085]
  decide +kernel

theorem g32p_row14_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 87 = [0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 87) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 87) (g32p_literalTraceValue 13 87)
      [1, 0, -1, 0, 1] [3888, 0, 3888, 0, 3888] = true := by
  rw [g32p_row14_traceCoefficients_087]
  decide +kernel

theorem g32p_row14_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 88 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 88) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 88) (g32p_literalTraceValue 13 88)
      [1, 0, -1, 0, 1] [-3888] = true := by
  rw [g32p_row14_traceCoefficients_088]
  decide +kernel

theorem g32p_row14_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 91 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 91) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 91) (g32p_literalTraceValue 13 91)
      [1, 0, -1, 0, 1] [-432] = true := by
  rw [g32p_row14_traceCoefficients_091]
  decide +kernel

theorem g32p_row14_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 94 = [0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 94) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 94) (g32p_literalTraceValue 13 94)
      [1, 0, -1, 0, 1] [0, 0, 0, 288, 0, 288] = true := by
  rw [g32p_row14_traceCoefficients_094]
  decide +kernel

theorem g32p_row14_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 99 = [0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 99) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 99) (g32p_literalTraceValue 13 99)
      [1, 0, -1, 0, 1] [155520, 0, 155520] = true := by
  rw [g32p_row14_traceCoefficients_099]
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

theorem g32p_row14_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 100 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row14_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer 100) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) 100) (g32p_literalTraceValue 13 100)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row14_traceCoefficients_100]
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

def g32p_row14_generatorIndex : Fin 8 → Fin 408 :=
  ![13, 64, 115, 166, 230, 231, 332, 333]

theorem g32p_row14_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup09_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 13 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 13 g32p_row14_supplierClass
    g32p_row14_supplierClass_isConj g32p_supplierGroup09_support g32p_row14_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row14_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup09_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row14_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 13 c false (g32p_row14_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 13 c true (g32p_row14_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 13 c false (g32p_row14_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 13 c true (g32p_row14_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 13 c false (g32p_row14_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 13 c false (g32p_row14_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 13 c true (g32p_row14_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 13 c true (g32p_row14_coinduced_zero c hc true) 3

theorem g32p_row14_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup09_support →
      g32p_literalTraceValue (g32p_row14_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row14_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup09_support) :
    g32p_literalTraceValue (g32p_row14_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup09_support →
    g32p_literalTraceValue (g32p_row14_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row14_zeroTrace_block_00 r k
  · exact g32p_row14_zeroTrace_block_01 r k
  · exact g32p_row14_zeroTrace_block_02 r k
  · exact g32p_row14_zeroTrace_block_03 r k
  · exact g32p_row14_zeroTrace_block_04 r k
  · exact g32p_row14_zeroTrace_block_05 r k
  · exact g32p_row14_zeroTrace_block_06 r k

theorem g32p_row14_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup09_support) :
    (g32p_recordedInductionGenerators (g32p_row14_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row14_generatorIndex k) c) := by
  rw [g32p_row14_recordedGenerator_zero c hc k, g32p_row14_zeroTrace_arithmetic c k hc]
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

def g32p_row14_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else [0, 0, 0, 288, 0, 288]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else [0, 0, 0, 0, 0, 72, 0, 72]))) else (if i.val < 21 then (if i.val < 19 then [1728, 0, 1728] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [0, 72, 0, 72])) else (if i.val < 29 then [0, 0, 0, 0, 3888, 0, 3888] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [0, 0, 0, 0, 432, 0, 432] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [0, 72, 0, 72] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [0, 0, 0, 0, 0, 72, 0, 72] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [432, 0, 432, 0, 432] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [3888, 0, 3888, 0, 3888] else [-3888])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [-432])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [0, 0, 0, 288, 0, 288]))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else [155520, 0, 155520]) else (if i.val < 101 then [] else [])))))))

theorem g32p_row14_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup09_support) :
    g32p_supplierTracePolynomialCheck 24 (g32p_literalCentralizer c) 12
      (g32p_supplierTraceCoefficients g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) c) (g32p_literalTraceValue 13 c)
      [1, 0, -1, 0, 1] (g32p_row14_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row14_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_017
  · exact g32p_row14_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_027
  · exact g32p_row14_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_051
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_055
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_064
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_085
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_087
  · exact g32p_row14_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_091
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup09_support) hc)
  · exact g32p_row14_tracePolynomial_099
  · exact g32p_row14_tracePolynomial_100
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_supplierGroup09_support) hc)

theorem g32p_row14_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 13 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 13 c) := by
  by_cases hc : c ∈ g32p_supplierGroup09_support
  · have hclass (j : Fin 24) :
        IsConj (g32p_literalRepresentative c) (g32p_row14_groupEquiv j : g32p_G) ↔
          g32p_row14_supplierClassifier j = c := by
      simpa only [g32p_row14_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row14_supplierClass_iff (g32p_row14_groupEquiv j) c
    have hχ (j : Fin 24) :
        (g32p_recordedSupplierCharacters 13 (g32p_row14_groupEquiv j) : ℂ) =
          g32p_root 12 ^ (Multiplicative.toAdd (g32p_row14_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 13 (show (g32p_recordedSuppliers 13).H from g32p_row14_groupEquiv j)]
      change g32p_root 12 ^ (Multiplicative.toAdd
        (g32p_row14_characterValues (g32p_row14_groupEquiv.symm (g32p_row14_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 13).H (g32p_recordedSupplierCharacters 13)
      (g32p_literalRepresentative c) g32p_row14_groupEquiv g32p_row14_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row14_characterValues j)).val) c 12 24
      (g32p_literalCentralizer c) (g32p_literalTraceValue 13 c) [1, 0, -1, 0, 1]
      (g32p_row14_traceQuotient c) (g32p_root 12) (by decide)
      g32p_row14_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_twelve
        (g32p_root_primitive (g32p_recordedSuppliers 13)))
      (g32p_row14_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 12 (by decide)] at h
    exact h
  · exact g32p_row14_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row14_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row14_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
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

theorem g32p_row14_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_0 r
  · exact g32p_row14_variantArithmetic_01_0 r
  · exact g32p_row14_variantArithmetic_02_0 r
  · exact g32p_row14_variantArithmetic_03_0 r
  · exact g32p_row14_variantArithmetic_04_0 r
  · exact g32p_row14_variantArithmetic_05_0 r
  · exact g32p_row14_variantArithmetic_06_0 r

theorem g32p_row14_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_1 r
  · exact g32p_row14_variantArithmetic_01_1 r
  · exact g32p_row14_variantArithmetic_02_1 r
  · exact g32p_row14_variantArithmetic_03_1 r
  · exact g32p_row14_variantArithmetic_04_1 r
  · exact g32p_row14_variantArithmetic_05_1 r
  · exact g32p_row14_variantArithmetic_06_1 r

theorem g32p_row14_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_2 r
  · exact g32p_row14_variantArithmetic_01_2 r
  · exact g32p_row14_variantArithmetic_02_2 r
  · exact g32p_row14_variantArithmetic_03_2 r
  · exact g32p_row14_variantArithmetic_04_2 r
  · exact g32p_row14_variantArithmetic_05_2 r
  · exact g32p_row14_variantArithmetic_06_2 r

theorem g32p_row14_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_3 r
  · exact g32p_row14_variantArithmetic_01_3 r
  · exact g32p_row14_variantArithmetic_02_3 r
  · exact g32p_row14_variantArithmetic_03_3 r
  · exact g32p_row14_variantArithmetic_04_3 r
  · exact g32p_row14_variantArithmetic_05_3 r
  · exact g32p_row14_variantArithmetic_06_3 r

theorem g32p_row14_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_4 r
  · exact g32p_row14_variantArithmetic_01_4 r
  · exact g32p_row14_variantArithmetic_02_4 r
  · exact g32p_row14_variantArithmetic_03_4 r
  · exact g32p_row14_variantArithmetic_04_4 r
  · exact g32p_row14_variantArithmetic_05_4 r
  · exact g32p_row14_variantArithmetic_06_4 r

theorem g32p_row14_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_5 r
  · exact g32p_row14_variantArithmetic_01_5 r
  · exact g32p_row14_variantArithmetic_02_5 r
  · exact g32p_row14_variantArithmetic_03_5 r
  · exact g32p_row14_variantArithmetic_04_5 r
  · exact g32p_row14_variantArithmetic_05_5 r
  · exact g32p_row14_variantArithmetic_06_5 r

theorem g32p_row14_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_6 r
  · exact g32p_row14_variantArithmetic_01_6 r
  · exact g32p_row14_variantArithmetic_02_6 r
  · exact g32p_row14_variantArithmetic_03_6 r
  · exact g32p_row14_variantArithmetic_04_6 r
  · exact g32p_row14_variantArithmetic_05_6 r
  · exact g32p_row14_variantArithmetic_06_6 r

theorem g32p_row14_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row14_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 13 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row14_variantArithmetic_00_7 r
  · exact g32p_row14_variantArithmetic_01_7 r
  · exact g32p_row14_variantArithmetic_02_7 r
  · exact g32p_row14_variantArithmetic_03_7 r
  · exact g32p_row14_variantArithmetic_04_7 r
  · exact g32p_row14_variantArithmetic_05_7 r
  · exact g32p_row14_variantArithmetic_06_7 r

theorem g32p_row14_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row14_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row14_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 13 c _ (g32p_row14_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row14_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end
