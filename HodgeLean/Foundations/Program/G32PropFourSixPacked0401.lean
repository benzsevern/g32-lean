import HodgeLean.Foundations.Program.G32PropFourSixPacked0400
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row26_supplierClassifier : Fin 576 → Fin 102 := g32p_supplierGroup20_classify

theorem g32p_row26_groupEquiv_isConj (i : Fin 576) :
    IsConj (g32p_row26_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row26_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup20_source i).1 (g32p_supplierGroup20_source i).2
  rw [g32p_supplierGroup20_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row26_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup20_matrix i)

def g32p_row26_supplierClass (h : (g32p_recordedSuppliers 25).H) : Fin 102 :=
  g32p_row26_supplierClassifier (g32p_row26_groupEquiv.symm h)

theorem g32p_row26_supplierClass_isConj (h : (g32p_recordedSuppliers 25).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row26_supplierClass h)) := by
  have he : (g32p_row26_groupEquiv (g32p_row26_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 25).H => (a : g32p_G))
      (g32p_row26_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row26_supplierClassifier (g32p_row26_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row26_groupEquiv_isConj (g32p_row26_groupEquiv.symm h)

theorem g32p_row26_supplierClass_iff (h : (g32p_recordedSuppliers 25).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row26_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row26_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row26_supplierClass_isConj h).symm

theorem g32p_row26_supplierClass_mem_support (h : (g32p_recordedSuppliers 25).H) :
    g32p_row26_supplierClass h ∈ g32p_supplierGroup20_support :=
  g32p_supplierGroup20_support_mem (g32p_row26_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_000 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 0 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_000_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 0 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 0 9 9, g32p_row26_traceSegment_000_0000_0009, g32p_row26_traceSegment_000_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 18 9 9, g32p_row26_traceSegment_000_0018_0009, g32p_row26_traceSegment_000_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 0 18 18, g32p_row26_traceSegment_000_0000_0018, g32p_row26_traceSegment_000_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 36 9 9, g32p_row26_traceSegment_000_0036_0009, g32p_row26_traceSegment_000_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 54 9 9, g32p_row26_traceSegment_000_0054_0009, g32p_row26_traceSegment_000_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 36 18 18, g32p_row26_traceSegment_000_0036_0018, g32p_row26_traceSegment_000_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 0 36 36, g32p_row26_traceSegment_000_0000_0036, g32p_row26_traceSegment_000_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 72 9 9, g32p_row26_traceSegment_000_0072_0009, g32p_row26_traceSegment_000_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 90 9 9, g32p_row26_traceSegment_000_0090_0009, g32p_row26_traceSegment_000_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 72 18 18, g32p_row26_traceSegment_000_0072_0018, g32p_row26_traceSegment_000_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 108 9 9, g32p_row26_traceSegment_000_0108_0009, g32p_row26_traceSegment_000_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 126 9 9, g32p_row26_traceSegment_000_0126_0009, g32p_row26_traceSegment_000_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 108 18 18, g32p_row26_traceSegment_000_0108_0018, g32p_row26_traceSegment_000_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 72 36 36, g32p_row26_traceSegment_000_0072_0036, g32p_row26_traceSegment_000_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_000 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 0 72 72, g32p_row26_traceSegment_000_0000_0072, g32p_row26_traceSegment_000_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 144 9 9, g32p_row26_traceSegment_000_0144_0009, g32p_row26_traceSegment_000_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 162 9 9, g32p_row26_traceSegment_000_0162_0009, g32p_row26_traceSegment_000_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 144 18 18, g32p_row26_traceSegment_000_0144_0018, g32p_row26_traceSegment_000_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 180 9 9, g32p_row26_traceSegment_000_0180_0009, g32p_row26_traceSegment_000_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 198 9 9, g32p_row26_traceSegment_000_0198_0009, g32p_row26_traceSegment_000_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 180 18 18, g32p_row26_traceSegment_000_0180_0018, g32p_row26_traceSegment_000_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 144 36 36, g32p_row26_traceSegment_000_0144_0036, g32p_row26_traceSegment_000_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 216 9 9, g32p_row26_traceSegment_000_0216_0009, g32p_row26_traceSegment_000_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 234 9 9, g32p_row26_traceSegment_000_0234_0009, g32p_row26_traceSegment_000_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 216 18 18, g32p_row26_traceSegment_000_0216_0018, g32p_row26_traceSegment_000_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 252 9 9, g32p_row26_traceSegment_000_0252_0009, g32p_row26_traceSegment_000_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 270 9 9, g32p_row26_traceSegment_000_0270_0009, g32p_row26_traceSegment_000_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 252 18 18, g32p_row26_traceSegment_000_0252_0018, g32p_row26_traceSegment_000_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 216 36 36, g32p_row26_traceSegment_000_0216_0036, g32p_row26_traceSegment_000_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_000 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 144 72 72, g32p_row26_traceSegment_000_0144_0072, g32p_row26_traceSegment_000_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_000 0 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 0 144 144, g32p_row26_traceSegment_000_0000_0144, g32p_row26_traceSegment_000_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 288 9 9, g32p_row26_traceSegment_000_0288_0009, g32p_row26_traceSegment_000_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 306 9 9, g32p_row26_traceSegment_000_0306_0009, g32p_row26_traceSegment_000_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 288 18 18, g32p_row26_traceSegment_000_0288_0018, g32p_row26_traceSegment_000_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 324 9 9, g32p_row26_traceSegment_000_0324_0009, g32p_row26_traceSegment_000_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 342 9 9, g32p_row26_traceSegment_000_0342_0009, g32p_row26_traceSegment_000_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 324 18 18, g32p_row26_traceSegment_000_0324_0018, g32p_row26_traceSegment_000_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 288 36 36, g32p_row26_traceSegment_000_0288_0036, g32p_row26_traceSegment_000_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 360 9 9, g32p_row26_traceSegment_000_0360_0009, g32p_row26_traceSegment_000_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 378 9 9, g32p_row26_traceSegment_000_0378_0009, g32p_row26_traceSegment_000_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 360 18 18, g32p_row26_traceSegment_000_0360_0018, g32p_row26_traceSegment_000_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 396 9 9, g32p_row26_traceSegment_000_0396_0009, g32p_row26_traceSegment_000_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 414 9 9, g32p_row26_traceSegment_000_0414_0009, g32p_row26_traceSegment_000_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 396 18 18, g32p_row26_traceSegment_000_0396_0018, g32p_row26_traceSegment_000_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 360 36 36, g32p_row26_traceSegment_000_0360_0036, g32p_row26_traceSegment_000_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_000 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 288 72 72, g32p_row26_traceSegment_000_0288_0072, g32p_row26_traceSegment_000_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 432 9 9, g32p_row26_traceSegment_000_0432_0009, g32p_row26_traceSegment_000_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 450 9 9, g32p_row26_traceSegment_000_0450_0009, g32p_row26_traceSegment_000_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 432 18 18, g32p_row26_traceSegment_000_0432_0018, g32p_row26_traceSegment_000_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 468 9 9, g32p_row26_traceSegment_000_0468_0009, g32p_row26_traceSegment_000_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 486 9 9, g32p_row26_traceSegment_000_0486_0009, g32p_row26_traceSegment_000_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 468 18 18, g32p_row26_traceSegment_000_0468_0018, g32p_row26_traceSegment_000_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 432 36 36, g32p_row26_traceSegment_000_0432_0036, g32p_row26_traceSegment_000_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 504 9 9, g32p_row26_traceSegment_000_0504_0009, g32p_row26_traceSegment_000_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 522 9 9, g32p_row26_traceSegment_000_0522_0009, g32p_row26_traceSegment_000_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 504 18 18, g32p_row26_traceSegment_000_0504_0018, g32p_row26_traceSegment_000_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 540 9 9, g32p_row26_traceSegment_000_0540_0009, g32p_row26_traceSegment_000_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_000 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_000_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_000 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 558 9 9, g32p_row26_traceSegment_000_0558_0009, g32p_row26_traceSegment_000_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_000 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 540 18 18, g32p_row26_traceSegment_000_0540_0018, g32p_row26_traceSegment_000_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_000 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 504 36 36, g32p_row26_traceSegment_000_0504_0036, g32p_row26_traceSegment_000_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_000 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 432 72 72, g32p_row26_traceSegment_000_0432_0072, g32p_row26_traceSegment_000_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_000 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 288 144 144, g32p_row26_traceSegment_000_0288_0144, g32p_row26_traceSegment_000_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_000_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_000 0 576 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_000 0 288 288, g32p_row26_traceSegment_000_0000_0288, g32p_row26_traceSegment_000_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 0 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_000_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_001 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 1 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_001_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 0 9 9, g32p_row26_traceSegment_001_0000_0009, g32p_row26_traceSegment_001_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 18 9 9, g32p_row26_traceSegment_001_0018_0009, g32p_row26_traceSegment_001_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 0 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 0 18 18, g32p_row26_traceSegment_001_0000_0018, g32p_row26_traceSegment_001_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 36 9 9, g32p_row26_traceSegment_001_0036_0009, g32p_row26_traceSegment_001_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 54 9 9, g32p_row26_traceSegment_001_0054_0009, g32p_row26_traceSegment_001_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 36 18 18, g32p_row26_traceSegment_001_0036_0018, g32p_row26_traceSegment_001_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 0 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 0 36 36, g32p_row26_traceSegment_001_0000_0036, g32p_row26_traceSegment_001_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 72 9 9, g32p_row26_traceSegment_001_0072_0009, g32p_row26_traceSegment_001_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 90 9 9, g32p_row26_traceSegment_001_0090_0009, g32p_row26_traceSegment_001_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 72 18 18, g32p_row26_traceSegment_001_0072_0018, g32p_row26_traceSegment_001_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 108 9 9, g32p_row26_traceSegment_001_0108_0009, g32p_row26_traceSegment_001_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 126 9 9, g32p_row26_traceSegment_001_0126_0009, g32p_row26_traceSegment_001_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 108 18 18, g32p_row26_traceSegment_001_0108_0018, g32p_row26_traceSegment_001_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 72 36 36, g32p_row26_traceSegment_001_0072_0036, g32p_row26_traceSegment_001_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_001 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 0 72 72, g32p_row26_traceSegment_001_0000_0072, g32p_row26_traceSegment_001_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 144 9 9, g32p_row26_traceSegment_001_0144_0009, g32p_row26_traceSegment_001_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 162 9 9, g32p_row26_traceSegment_001_0162_0009, g32p_row26_traceSegment_001_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 144 18 18, g32p_row26_traceSegment_001_0144_0018, g32p_row26_traceSegment_001_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 180 9 9, g32p_row26_traceSegment_001_0180_0009, g32p_row26_traceSegment_001_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 198 9 9, g32p_row26_traceSegment_001_0198_0009, g32p_row26_traceSegment_001_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 180 18 18, g32p_row26_traceSegment_001_0180_0018, g32p_row26_traceSegment_001_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 144 36 36, g32p_row26_traceSegment_001_0144_0036, g32p_row26_traceSegment_001_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 216 9 9, g32p_row26_traceSegment_001_0216_0009, g32p_row26_traceSegment_001_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 234 9 9, g32p_row26_traceSegment_001_0234_0009, g32p_row26_traceSegment_001_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 216 18 18, g32p_row26_traceSegment_001_0216_0018, g32p_row26_traceSegment_001_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 252 9 9, g32p_row26_traceSegment_001_0252_0009, g32p_row26_traceSegment_001_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 270 9 9, g32p_row26_traceSegment_001_0270_0009, g32p_row26_traceSegment_001_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 252 18 18, g32p_row26_traceSegment_001_0252_0018, g32p_row26_traceSegment_001_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 216 36 36, g32p_row26_traceSegment_001_0216_0036, g32p_row26_traceSegment_001_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_001 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 144 72 72, g32p_row26_traceSegment_001_0144_0072, g32p_row26_traceSegment_001_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_001 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 0 144 144, g32p_row26_traceSegment_001_0000_0144, g32p_row26_traceSegment_001_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 288 9 9, g32p_row26_traceSegment_001_0288_0009, g32p_row26_traceSegment_001_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 306 9 9, g32p_row26_traceSegment_001_0306_0009, g32p_row26_traceSegment_001_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 288 18 18, g32p_row26_traceSegment_001_0288_0018, g32p_row26_traceSegment_001_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 324 9 9, g32p_row26_traceSegment_001_0324_0009, g32p_row26_traceSegment_001_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 342 9 9, g32p_row26_traceSegment_001_0342_0009, g32p_row26_traceSegment_001_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 324 18 18, g32p_row26_traceSegment_001_0324_0018, g32p_row26_traceSegment_001_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 288 36 36, g32p_row26_traceSegment_001_0288_0036, g32p_row26_traceSegment_001_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 360 9 9, g32p_row26_traceSegment_001_0360_0009, g32p_row26_traceSegment_001_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 378 9 9, g32p_row26_traceSegment_001_0378_0009, g32p_row26_traceSegment_001_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 360 18 18, g32p_row26_traceSegment_001_0360_0018, g32p_row26_traceSegment_001_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 396 9 9, g32p_row26_traceSegment_001_0396_0009, g32p_row26_traceSegment_001_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 414 9 9, g32p_row26_traceSegment_001_0414_0009, g32p_row26_traceSegment_001_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 396 18 18, g32p_row26_traceSegment_001_0396_0018, g32p_row26_traceSegment_001_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 360 36 36, g32p_row26_traceSegment_001_0360_0036, g32p_row26_traceSegment_001_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_001 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 288 72 72, g32p_row26_traceSegment_001_0288_0072, g32p_row26_traceSegment_001_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 432 9 9, g32p_row26_traceSegment_001_0432_0009, g32p_row26_traceSegment_001_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 459 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 450 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 450 9 9, g32p_row26_traceSegment_001_0450_0009, g32p_row26_traceSegment_001_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 432 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 432 18 18, g32p_row26_traceSegment_001_0432_0018, g32p_row26_traceSegment_001_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 468 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 468 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 468 9 9, g32p_row26_traceSegment_001_0468_0009, g32p_row26_traceSegment_001_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 495 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 486 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 486 9 9, g32p_row26_traceSegment_001_0486_0009, g32p_row26_traceSegment_001_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 468 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 468 18 18, g32p_row26_traceSegment_001_0468_0018, g32p_row26_traceSegment_001_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 432 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 432 36 36, g32p_row26_traceSegment_001_0432_0036, g32p_row26_traceSegment_001_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 504 9 9, g32p_row26_traceSegment_001_0504_0009, g32p_row26_traceSegment_001_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 522 9 9, g32p_row26_traceSegment_001_0522_0009, g32p_row26_traceSegment_001_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 504 18 18, g32p_row26_traceSegment_001_0504_0018, g32p_row26_traceSegment_001_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 540 9 9, g32p_row26_traceSegment_001_0540_0009, g32p_row26_traceSegment_001_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_001 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_001_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_001 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 558 9 9, g32p_row26_traceSegment_001_0558_0009, g32p_row26_traceSegment_001_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_001 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 540 18 18, g32p_row26_traceSegment_001_0540_0018, g32p_row26_traceSegment_001_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_001 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 504 36 36, g32p_row26_traceSegment_001_0504_0036, g32p_row26_traceSegment_001_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_001 432 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 432 72 72, g32p_row26_traceSegment_001_0432_0072, g32p_row26_traceSegment_001_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_001 288 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 288 144 144, g32p_row26_traceSegment_001_0288_0144, g32p_row26_traceSegment_001_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_001_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_001 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_001 0 288 288, g32p_row26_traceSegment_001_0000_0288, g32p_row26_traceSegment_001_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 1 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_001_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_002 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 2 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_002_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 0 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 0 9 9, g32p_row26_traceSegment_002_0000_0009, g32p_row26_traceSegment_002_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 18 9 9, g32p_row26_traceSegment_002_0018_0009, g32p_row26_traceSegment_002_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 0 18 18, g32p_row26_traceSegment_002_0000_0018, g32p_row26_traceSegment_002_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 36 9 9, g32p_row26_traceSegment_002_0036_0009, g32p_row26_traceSegment_002_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 63 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 54 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 54 9 9, g32p_row26_traceSegment_002_0054_0009, g32p_row26_traceSegment_002_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 36 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 36 18 18, g32p_row26_traceSegment_002_0036_0018, g32p_row26_traceSegment_002_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 0 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 0 36 36, g32p_row26_traceSegment_002_0000_0036, g32p_row26_traceSegment_002_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 72 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 72 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 72 9 9, g32p_row26_traceSegment_002_0072_0009, g32p_row26_traceSegment_002_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 90 9 9, g32p_row26_traceSegment_002_0090_0009, g32p_row26_traceSegment_002_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 72 18 18, g32p_row26_traceSegment_002_0072_0018, g32p_row26_traceSegment_002_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 108 9 9, g32p_row26_traceSegment_002_0108_0009, g32p_row26_traceSegment_002_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 126 9 9, g32p_row26_traceSegment_002_0126_0009, g32p_row26_traceSegment_002_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 108 18 18, g32p_row26_traceSegment_002_0108_0018, g32p_row26_traceSegment_002_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 72 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 72 36 36, g32p_row26_traceSegment_002_0072_0036, g32p_row26_traceSegment_002_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_002 0 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 0 72 72, g32p_row26_traceSegment_002_0000_0072, g32p_row26_traceSegment_002_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 144 9 9, g32p_row26_traceSegment_002_0144_0009, g32p_row26_traceSegment_002_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 162 9 9, g32p_row26_traceSegment_002_0162_0009, g32p_row26_traceSegment_002_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 144 18 18, g32p_row26_traceSegment_002_0144_0018, g32p_row26_traceSegment_002_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 180 9 9, g32p_row26_traceSegment_002_0180_0009, g32p_row26_traceSegment_002_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 198 9 9, g32p_row26_traceSegment_002_0198_0009, g32p_row26_traceSegment_002_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 180 18 18, g32p_row26_traceSegment_002_0180_0018, g32p_row26_traceSegment_002_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 144 36 36, g32p_row26_traceSegment_002_0144_0036, g32p_row26_traceSegment_002_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 216 9 9, g32p_row26_traceSegment_002_0216_0009, g32p_row26_traceSegment_002_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 234 9 9, g32p_row26_traceSegment_002_0234_0009, g32p_row26_traceSegment_002_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 216 18 18, g32p_row26_traceSegment_002_0216_0018, g32p_row26_traceSegment_002_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 252 9 9, g32p_row26_traceSegment_002_0252_0009, g32p_row26_traceSegment_002_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 270 9 9, g32p_row26_traceSegment_002_0270_0009, g32p_row26_traceSegment_002_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 252 18 18, g32p_row26_traceSegment_002_0252_0018, g32p_row26_traceSegment_002_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 216 36 36, g32p_row26_traceSegment_002_0216_0036, g32p_row26_traceSegment_002_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_002 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 144 72 72, g32p_row26_traceSegment_002_0144_0072, g32p_row26_traceSegment_002_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_002 0 288 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 0 144 144, g32p_row26_traceSegment_002_0000_0144, g32p_row26_traceSegment_002_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 288 9 9, g32p_row26_traceSegment_002_0288_0009, g32p_row26_traceSegment_002_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 315 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 306 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 306 9 9, g32p_row26_traceSegment_002_0306_0009, g32p_row26_traceSegment_002_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 288 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 288 18 18, g32p_row26_traceSegment_002_0288_0018, g32p_row26_traceSegment_002_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 324 9 9, g32p_row26_traceSegment_002_0324_0009, g32p_row26_traceSegment_002_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 342 9 9, g32p_row26_traceSegment_002_0342_0009, g32p_row26_traceSegment_002_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 324 18 18, g32p_row26_traceSegment_002_0324_0018, g32p_row26_traceSegment_002_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 288 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 288 36 36, g32p_row26_traceSegment_002_0288_0036, g32p_row26_traceSegment_002_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 360 9 9, g32p_row26_traceSegment_002_0360_0009, g32p_row26_traceSegment_002_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 378 9 9, g32p_row26_traceSegment_002_0378_0009, g32p_row26_traceSegment_002_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 360 18 18, g32p_row26_traceSegment_002_0360_0018, g32p_row26_traceSegment_002_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 396 9 9, g32p_row26_traceSegment_002_0396_0009, g32p_row26_traceSegment_002_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 414 9 9, g32p_row26_traceSegment_002_0414_0009, g32p_row26_traceSegment_002_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 396 18 18, g32p_row26_traceSegment_002_0396_0018, g32p_row26_traceSegment_002_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 360 36 36, g32p_row26_traceSegment_002_0360_0036, g32p_row26_traceSegment_002_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_002 288 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 288 72 72, g32p_row26_traceSegment_002_0288_0072, g32p_row26_traceSegment_002_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 432 9 9, g32p_row26_traceSegment_002_0432_0009, g32p_row26_traceSegment_002_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 450 9 9, g32p_row26_traceSegment_002_0450_0009, g32p_row26_traceSegment_002_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 432 18 18, g32p_row26_traceSegment_002_0432_0018, g32p_row26_traceSegment_002_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 468 9 9, g32p_row26_traceSegment_002_0468_0009, g32p_row26_traceSegment_002_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 486 9 9, g32p_row26_traceSegment_002_0486_0009, g32p_row26_traceSegment_002_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 468 18 18, g32p_row26_traceSegment_002_0468_0018, g32p_row26_traceSegment_002_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 432 36 36, g32p_row26_traceSegment_002_0432_0036, g32p_row26_traceSegment_002_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 504 9 9, g32p_row26_traceSegment_002_0504_0009, g32p_row26_traceSegment_002_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 522 9 9, g32p_row26_traceSegment_002_0522_0009, g32p_row26_traceSegment_002_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 504 18 18, g32p_row26_traceSegment_002_0504_0018, g32p_row26_traceSegment_002_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 540 9 9, g32p_row26_traceSegment_002_0540_0009, g32p_row26_traceSegment_002_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_002 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_002_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_002 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 558 9 9, g32p_row26_traceSegment_002_0558_0009, g32p_row26_traceSegment_002_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_002 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 540 18 18, g32p_row26_traceSegment_002_0540_0018, g32p_row26_traceSegment_002_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_002 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 504 36 36, g32p_row26_traceSegment_002_0504_0036, g32p_row26_traceSegment_002_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_002 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 432 72 72, g32p_row26_traceSegment_002_0432_0072, g32p_row26_traceSegment_002_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_002 288 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 288 144 144, g32p_row26_traceSegment_002_0288_0144, g32p_row26_traceSegment_002_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_002_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_002 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_002 0 288 288, g32p_row26_traceSegment_002_0000_0288, g32p_row26_traceSegment_002_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 2 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_002_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_003 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 3 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_003_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 0 9 9, g32p_row26_traceSegment_003_0000_0009, g32p_row26_traceSegment_003_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 18 9 9, g32p_row26_traceSegment_003_0018_0009, g32p_row26_traceSegment_003_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 0 18 18, g32p_row26_traceSegment_003_0000_0018, g32p_row26_traceSegment_003_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 36 9 9, g32p_row26_traceSegment_003_0036_0009, g32p_row26_traceSegment_003_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 54 9 9, g32p_row26_traceSegment_003_0054_0009, g32p_row26_traceSegment_003_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 36 18 18, g32p_row26_traceSegment_003_0036_0018, g32p_row26_traceSegment_003_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 0 36 36, g32p_row26_traceSegment_003_0000_0036, g32p_row26_traceSegment_003_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 72 9 9, g32p_row26_traceSegment_003_0072_0009, g32p_row26_traceSegment_003_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 90 9 9, g32p_row26_traceSegment_003_0090_0009, g32p_row26_traceSegment_003_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 72 18 18, g32p_row26_traceSegment_003_0072_0018, g32p_row26_traceSegment_003_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 108 9 9, g32p_row26_traceSegment_003_0108_0009, g32p_row26_traceSegment_003_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 126 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 126 9 9, g32p_row26_traceSegment_003_0126_0009, g32p_row26_traceSegment_003_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 108 18 18, g32p_row26_traceSegment_003_0108_0018, g32p_row26_traceSegment_003_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 72 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 72 36 36, g32p_row26_traceSegment_003_0072_0036, g32p_row26_traceSegment_003_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_003 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 0 72 72, g32p_row26_traceSegment_003_0000_0072, g32p_row26_traceSegment_003_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 144 9 9, g32p_row26_traceSegment_003_0144_0009, g32p_row26_traceSegment_003_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 162 9 9, g32p_row26_traceSegment_003_0162_0009, g32p_row26_traceSegment_003_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 144 18 18, g32p_row26_traceSegment_003_0144_0018, g32p_row26_traceSegment_003_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 180 9 9, g32p_row26_traceSegment_003_0180_0009, g32p_row26_traceSegment_003_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 198 9 9, g32p_row26_traceSegment_003_0198_0009, g32p_row26_traceSegment_003_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 180 18 18, g32p_row26_traceSegment_003_0180_0018, g32p_row26_traceSegment_003_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 144 36 36, g32p_row26_traceSegment_003_0144_0036, g32p_row26_traceSegment_003_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 216 9 9, g32p_row26_traceSegment_003_0216_0009, g32p_row26_traceSegment_003_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 234 9 9, g32p_row26_traceSegment_003_0234_0009, g32p_row26_traceSegment_003_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 216 18 18, g32p_row26_traceSegment_003_0216_0018, g32p_row26_traceSegment_003_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 252 9 9, g32p_row26_traceSegment_003_0252_0009, g32p_row26_traceSegment_003_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 270 9 9, g32p_row26_traceSegment_003_0270_0009, g32p_row26_traceSegment_003_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 252 18 18, g32p_row26_traceSegment_003_0252_0018, g32p_row26_traceSegment_003_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 216 36 36, g32p_row26_traceSegment_003_0216_0036, g32p_row26_traceSegment_003_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_003 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 144 72 72, g32p_row26_traceSegment_003_0144_0072, g32p_row26_traceSegment_003_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_003 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 0 144 144, g32p_row26_traceSegment_003_0000_0144, g32p_row26_traceSegment_003_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 288 9 9, g32p_row26_traceSegment_003_0288_0009, g32p_row26_traceSegment_003_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 306 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 306 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 306 9 9, g32p_row26_traceSegment_003_0306_0009, g32p_row26_traceSegment_003_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 288 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 288 18 18, g32p_row26_traceSegment_003_0288_0018, g32p_row26_traceSegment_003_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 324 9 9, g32p_row26_traceSegment_003_0324_0009, g32p_row26_traceSegment_003_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 351 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 342 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 342 9 9, g32p_row26_traceSegment_003_0342_0009, g32p_row26_traceSegment_003_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 324 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 324 18 18, g32p_row26_traceSegment_003_0324_0018, g32p_row26_traceSegment_003_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 288 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 288 36 36, g32p_row26_traceSegment_003_0288_0036, g32p_row26_traceSegment_003_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 360 9 9, g32p_row26_traceSegment_003_0360_0009, g32p_row26_traceSegment_003_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 378 9 9, g32p_row26_traceSegment_003_0378_0009, g32p_row26_traceSegment_003_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 360 18 18, g32p_row26_traceSegment_003_0360_0018, g32p_row26_traceSegment_003_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 405 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 396 9 9, g32p_row26_traceSegment_003_0396_0009, g32p_row26_traceSegment_003_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 414 9 9, g32p_row26_traceSegment_003_0414_0009, g32p_row26_traceSegment_003_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 396 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 396 18 18, g32p_row26_traceSegment_003_0396_0018, g32p_row26_traceSegment_003_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 360 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 360 36 36, g32p_row26_traceSegment_003_0360_0036, g32p_row26_traceSegment_003_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_003 288 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 288 72 72, g32p_row26_traceSegment_003_0288_0072, g32p_row26_traceSegment_003_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 432 9 9, g32p_row26_traceSegment_003_0432_0009, g32p_row26_traceSegment_003_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 450 9 9, g32p_row26_traceSegment_003_0450_0009, g32p_row26_traceSegment_003_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 432 18 18, g32p_row26_traceSegment_003_0432_0018, g32p_row26_traceSegment_003_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 468 9 9, g32p_row26_traceSegment_003_0468_0009, g32p_row26_traceSegment_003_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 486 9 9, g32p_row26_traceSegment_003_0486_0009, g32p_row26_traceSegment_003_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 468 18 18, g32p_row26_traceSegment_003_0468_0018, g32p_row26_traceSegment_003_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 432 36 36, g32p_row26_traceSegment_003_0432_0036, g32p_row26_traceSegment_003_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 504 9 9, g32p_row26_traceSegment_003_0504_0009, g32p_row26_traceSegment_003_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 522 9 9, g32p_row26_traceSegment_003_0522_0009, g32p_row26_traceSegment_003_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 504 18 18, g32p_row26_traceSegment_003_0504_0018, g32p_row26_traceSegment_003_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 540 9 9, g32p_row26_traceSegment_003_0540_0009, g32p_row26_traceSegment_003_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_003 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_003_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_003 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 558 9 9, g32p_row26_traceSegment_003_0558_0009, g32p_row26_traceSegment_003_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_003 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 540 18 18, g32p_row26_traceSegment_003_0540_0018, g32p_row26_traceSegment_003_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_003 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 504 36 36, g32p_row26_traceSegment_003_0504_0036, g32p_row26_traceSegment_003_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_003 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 432 72 72, g32p_row26_traceSegment_003_0432_0072, g32p_row26_traceSegment_003_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_003 288 288 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 288 144 144, g32p_row26_traceSegment_003_0288_0144, g32p_row26_traceSegment_003_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_003_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_003 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_003 0 288 288, g32p_row26_traceSegment_003_0000_0288, g32p_row26_traceSegment_003_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 3 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_003_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_005 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 5 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_005_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 0 9 9, g32p_row26_traceSegment_005_0000_0009, g32p_row26_traceSegment_005_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 18 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 18 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 18 9 9, g32p_row26_traceSegment_005_0018_0009, g32p_row26_traceSegment_005_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 0 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 0 18 18, g32p_row26_traceSegment_005_0000_0018, g32p_row26_traceSegment_005_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 36 9 9, g32p_row26_traceSegment_005_0036_0009, g32p_row26_traceSegment_005_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 54 9 9, g32p_row26_traceSegment_005_0054_0009, g32p_row26_traceSegment_005_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 36 18 18, g32p_row26_traceSegment_005_0036_0018, g32p_row26_traceSegment_005_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 0 72 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 0 36 36, g32p_row26_traceSegment_005_0000_0036, g32p_row26_traceSegment_005_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 72 9 9, g32p_row26_traceSegment_005_0072_0009, g32p_row26_traceSegment_005_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 99 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 90 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 90 9 9, g32p_row26_traceSegment_005_0090_0009, g32p_row26_traceSegment_005_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 72 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 72 18 18, g32p_row26_traceSegment_005_0072_0018, g32p_row26_traceSegment_005_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 117 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 108 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 108 9 9, g32p_row26_traceSegment_005_0108_0009, g32p_row26_traceSegment_005_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 126 9 9, g32p_row26_traceSegment_005_0126_0009, g32p_row26_traceSegment_005_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 108 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 108 18 18, g32p_row26_traceSegment_005_0108_0018, g32p_row26_traceSegment_005_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 72 72 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 72 36 36, g32p_row26_traceSegment_005_0072_0036, g32p_row26_traceSegment_005_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_005 0 144 = [3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 0 72 72, g32p_row26_traceSegment_005_0000_0072, g32p_row26_traceSegment_005_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 144 9 9, g32p_row26_traceSegment_005_0144_0009, g32p_row26_traceSegment_005_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 162 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 162 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 162 9 9, g32p_row26_traceSegment_005_0162_0009, g32p_row26_traceSegment_005_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 144 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 144 18 18, g32p_row26_traceSegment_005_0144_0018, g32p_row26_traceSegment_005_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 180 9 9, g32p_row26_traceSegment_005_0180_0009, g32p_row26_traceSegment_005_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 198 9 9, g32p_row26_traceSegment_005_0198_0009, g32p_row26_traceSegment_005_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 180 18 18, g32p_row26_traceSegment_005_0180_0018, g32p_row26_traceSegment_005_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 144 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 144 36 36, g32p_row26_traceSegment_005_0144_0036, g32p_row26_traceSegment_005_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 216 9 9, g32p_row26_traceSegment_005_0216_0009, g32p_row26_traceSegment_005_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 234 9 9, g32p_row26_traceSegment_005_0234_0009, g32p_row26_traceSegment_005_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 216 18 18, g32p_row26_traceSegment_005_0216_0018, g32p_row26_traceSegment_005_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 261 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 252 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 252 9 9, g32p_row26_traceSegment_005_0252_0009, g32p_row26_traceSegment_005_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 270 9 9, g32p_row26_traceSegment_005_0270_0009, g32p_row26_traceSegment_005_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 252 18 18, g32p_row26_traceSegment_005_0252_0018, g32p_row26_traceSegment_005_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 216 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 216 36 36, g32p_row26_traceSegment_005_0216_0036, g32p_row26_traceSegment_005_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_005 144 144 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 144 72 72, g32p_row26_traceSegment_005_0144_0072, g32p_row26_traceSegment_005_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_005 0 288 = [4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 0 144 144, g32p_row26_traceSegment_005_0000_0144, g32p_row26_traceSegment_005_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 297 9 = [2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 288 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 288 9 9, g32p_row26_traceSegment_005_0288_0009, g32p_row26_traceSegment_005_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 306 9 9, g32p_row26_traceSegment_005_0306_0009, g32p_row26_traceSegment_005_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 288 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 288 18 18, g32p_row26_traceSegment_005_0288_0018, g32p_row26_traceSegment_005_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 324 9 9, g32p_row26_traceSegment_005_0324_0009, g32p_row26_traceSegment_005_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 342 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 351 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 342 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 342 9 9, g32p_row26_traceSegment_005_0342_0009, g32p_row26_traceSegment_005_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 324 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 324 18 18, g32p_row26_traceSegment_005_0324_0018, g32p_row26_traceSegment_005_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 288 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 288 36 36, g32p_row26_traceSegment_005_0288_0036, g32p_row26_traceSegment_005_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 360 9 9, g32p_row26_traceSegment_005_0360_0009, g32p_row26_traceSegment_005_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 378 9 9, g32p_row26_traceSegment_005_0378_0009, g32p_row26_traceSegment_005_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 360 18 18, g32p_row26_traceSegment_005_0360_0018, g32p_row26_traceSegment_005_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 396 9 9, g32p_row26_traceSegment_005_0396_0009, g32p_row26_traceSegment_005_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 414 9 9, g32p_row26_traceSegment_005_0414_0009, g32p_row26_traceSegment_005_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 396 18 18, g32p_row26_traceSegment_005_0396_0018, g32p_row26_traceSegment_005_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 360 36 36, g32p_row26_traceSegment_005_0360_0036, g32p_row26_traceSegment_005_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_005 288 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 288 72 72, g32p_row26_traceSegment_005_0288_0072, g32p_row26_traceSegment_005_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 432 9 9, g32p_row26_traceSegment_005_0432_0009, g32p_row26_traceSegment_005_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 450 9 9, g32p_row26_traceSegment_005_0450_0009, g32p_row26_traceSegment_005_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 432 18 18, g32p_row26_traceSegment_005_0432_0018, g32p_row26_traceSegment_005_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 468 9 9, g32p_row26_traceSegment_005_0468_0009, g32p_row26_traceSegment_005_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 486 9 9, g32p_row26_traceSegment_005_0486_0009, g32p_row26_traceSegment_005_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 468 18 18, g32p_row26_traceSegment_005_0468_0018, g32p_row26_traceSegment_005_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 432 36 36, g32p_row26_traceSegment_005_0432_0036, g32p_row26_traceSegment_005_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 504 9 9, g32p_row26_traceSegment_005_0504_0009, g32p_row26_traceSegment_005_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 522 9 9, g32p_row26_traceSegment_005_0522_0009, g32p_row26_traceSegment_005_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 504 18 18, g32p_row26_traceSegment_005_0504_0018, g32p_row26_traceSegment_005_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 540 9 9, g32p_row26_traceSegment_005_0540_0009, g32p_row26_traceSegment_005_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_005 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_005_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_005 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 558 9 9, g32p_row26_traceSegment_005_0558_0009, g32p_row26_traceSegment_005_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_005 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 540 18 18, g32p_row26_traceSegment_005_0540_0018, g32p_row26_traceSegment_005_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_005 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 504 36 36, g32p_row26_traceSegment_005_0504_0036, g32p_row26_traceSegment_005_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_005 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 432 72 72, g32p_row26_traceSegment_005_0432_0072, g32p_row26_traceSegment_005_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_005 288 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 288 144 144, g32p_row26_traceSegment_005_0288_0144, g32p_row26_traceSegment_005_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_005_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_005 0 576 = [8, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_005 0 288 288, g32p_row26_traceSegment_005_0000_0288, g32p_row26_traceSegment_005_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 5 = [8, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_005_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_007 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 7 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_007_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 0 9 9, g32p_row26_traceSegment_007_0000_0009, g32p_row26_traceSegment_007_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 18 9 9, g32p_row26_traceSegment_007_0018_0009, g32p_row26_traceSegment_007_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 0 18 18, g32p_row26_traceSegment_007_0000_0018, g32p_row26_traceSegment_007_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 36 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 45 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 36 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 36 9 9, g32p_row26_traceSegment_007_0036_0009, g32p_row26_traceSegment_007_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 63 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 54 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 54 9 9, g32p_row26_traceSegment_007_0054_0009, g32p_row26_traceSegment_007_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 36 36 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 36 18 18, g32p_row26_traceSegment_007_0036_0018, g32p_row26_traceSegment_007_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 0 72 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 0 36 36, g32p_row26_traceSegment_007_0000_0036, g32p_row26_traceSegment_007_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 72 9 9, g32p_row26_traceSegment_007_0072_0009, g32p_row26_traceSegment_007_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 90 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 90 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 90 9 9, g32p_row26_traceSegment_007_0090_0009, g32p_row26_traceSegment_007_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 72 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 72 18 18, g32p_row26_traceSegment_007_0072_0018, g32p_row26_traceSegment_007_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 108 9 9, g32p_row26_traceSegment_007_0108_0009, g32p_row26_traceSegment_007_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 126 9 9, g32p_row26_traceSegment_007_0126_0009, g32p_row26_traceSegment_007_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 108 18 18, g32p_row26_traceSegment_007_0108_0018, g32p_row26_traceSegment_007_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 72 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 72 36 36, g32p_row26_traceSegment_007_0072_0036, g32p_row26_traceSegment_007_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_007 0 144 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 0 72 72, g32p_row26_traceSegment_007_0000_0072, g32p_row26_traceSegment_007_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 144 9 9, g32p_row26_traceSegment_007_0144_0009, g32p_row26_traceSegment_007_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 171 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 162 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 162 9 9, g32p_row26_traceSegment_007_0162_0009, g32p_row26_traceSegment_007_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 144 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 144 18 18, g32p_row26_traceSegment_007_0144_0018, g32p_row26_traceSegment_007_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 180 9 9, g32p_row26_traceSegment_007_0180_0009, g32p_row26_traceSegment_007_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 198 9 9, g32p_row26_traceSegment_007_0198_0009, g32p_row26_traceSegment_007_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 180 18 18, g32p_row26_traceSegment_007_0180_0018, g32p_row26_traceSegment_007_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 144 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 144 36 36, g32p_row26_traceSegment_007_0144_0036, g32p_row26_traceSegment_007_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 216 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 225 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 216 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 216 9 9, g32p_row26_traceSegment_007_0216_0009, g32p_row26_traceSegment_007_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 234 9 9, g32p_row26_traceSegment_007_0234_0009, g32p_row26_traceSegment_007_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 216 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 216 18 18, g32p_row26_traceSegment_007_0216_0018, g32p_row26_traceSegment_007_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 261 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 252 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 252 9 9, g32p_row26_traceSegment_007_0252_0009, g32p_row26_traceSegment_007_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 270 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 279 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 270 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 270 9 9, g32p_row26_traceSegment_007_0270_0009, g32p_row26_traceSegment_007_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 252 36 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 252 18 18, g32p_row26_traceSegment_007_0252_0018, g32p_row26_traceSegment_007_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 216 72 = [0, 5, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 216 36 36, g32p_row26_traceSegment_007_0216_0036, g32p_row26_traceSegment_007_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_007 144 144 = [0, 7, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 144 72 72, g32p_row26_traceSegment_007_0144_0072, g32p_row26_traceSegment_007_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_007 0 288 = [0, 10, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 0 144 144, g32p_row26_traceSegment_007_0000_0144, g32p_row26_traceSegment_007_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 288 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 288 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 288 9 9, g32p_row26_traceSegment_007_0288_0009, g32p_row26_traceSegment_007_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 306 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 306 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 306 9 9, g32p_row26_traceSegment_007_0306_0009, g32p_row26_traceSegment_007_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 288 36 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 288 18 18, g32p_row26_traceSegment_007_0288_0018, g32p_row26_traceSegment_007_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 333 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 324 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 324 9 9, g32p_row26_traceSegment_007_0324_0009, g32p_row26_traceSegment_007_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 342 9 9, g32p_row26_traceSegment_007_0342_0009, g32p_row26_traceSegment_007_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 324 18 18, g32p_row26_traceSegment_007_0324_0018, g32p_row26_traceSegment_007_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 288 72 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 288 36 36, g32p_row26_traceSegment_007_0288_0036, g32p_row26_traceSegment_007_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 360 9 9, g32p_row26_traceSegment_007_0360_0009, g32p_row26_traceSegment_007_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 378 9 9, g32p_row26_traceSegment_007_0378_0009, g32p_row26_traceSegment_007_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 360 18 18, g32p_row26_traceSegment_007_0360_0018, g32p_row26_traceSegment_007_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 396 9 9, g32p_row26_traceSegment_007_0396_0009, g32p_row26_traceSegment_007_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 414 9 9, g32p_row26_traceSegment_007_0414_0009, g32p_row26_traceSegment_007_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 396 18 18, g32p_row26_traceSegment_007_0396_0018, g32p_row26_traceSegment_007_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 360 36 36, g32p_row26_traceSegment_007_0360_0036, g32p_row26_traceSegment_007_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_007 288 144 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 288 72 72, g32p_row26_traceSegment_007_0288_0072, g32p_row26_traceSegment_007_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 432 9 9, g32p_row26_traceSegment_007_0432_0009, g32p_row26_traceSegment_007_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 459 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 450 9 9, g32p_row26_traceSegment_007_0450_0009, g32p_row26_traceSegment_007_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 432 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 432 18 18, g32p_row26_traceSegment_007_0432_0018, g32p_row26_traceSegment_007_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 468 9 9, g32p_row26_traceSegment_007_0468_0009, g32p_row26_traceSegment_007_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 495 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 486 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 486 9 9, g32p_row26_traceSegment_007_0486_0009, g32p_row26_traceSegment_007_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 468 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 468 18 18, g32p_row26_traceSegment_007_0468_0018, g32p_row26_traceSegment_007_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 432 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 432 36 36, g32p_row26_traceSegment_007_0432_0036, g32p_row26_traceSegment_007_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 504 9 9, g32p_row26_traceSegment_007_0504_0009, g32p_row26_traceSegment_007_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 531 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 522 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 522 9 9, g32p_row26_traceSegment_007_0522_0009, g32p_row26_traceSegment_007_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 504 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 504 18 18, g32p_row26_traceSegment_007_0504_0018, g32p_row26_traceSegment_007_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 540 9 9, g32p_row26_traceSegment_007_0540_0009, g32p_row26_traceSegment_007_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 558 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_007 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_007_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_007 558 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 558 9 9, g32p_row26_traceSegment_007_0558_0009, g32p_row26_traceSegment_007_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_007 540 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 540 18 18, g32p_row26_traceSegment_007_0540_0018, g32p_row26_traceSegment_007_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_007 504 72 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 504 36 36, g32p_row26_traceSegment_007_0504_0036, g32p_row26_traceSegment_007_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_007 432 144 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 432 72 72, g32p_row26_traceSegment_007_0432_0072, g32p_row26_traceSegment_007_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_007 288 288 = [0, 6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 288 144 144, g32p_row26_traceSegment_007_0288_0144, g32p_row26_traceSegment_007_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_007_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_007 0 576 = [0, 16, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_007 0 288 288, g32p_row26_traceSegment_007_0000_0288, g32p_row26_traceSegment_007_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 7 = [0, 16, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_007_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_008 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 8 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_008_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 0 9 9, g32p_row26_traceSegment_008_0000_0009, g32p_row26_traceSegment_008_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 18 9 9, g32p_row26_traceSegment_008_0018_0009, g32p_row26_traceSegment_008_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 0 18 18, g32p_row26_traceSegment_008_0000_0018, g32p_row26_traceSegment_008_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 36 9 9, g32p_row26_traceSegment_008_0036_0009, g32p_row26_traceSegment_008_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 54 9 9, g32p_row26_traceSegment_008_0054_0009, g32p_row26_traceSegment_008_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 36 18 18, g32p_row26_traceSegment_008_0036_0018, g32p_row26_traceSegment_008_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 0 36 36, g32p_row26_traceSegment_008_0000_0036, g32p_row26_traceSegment_008_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 72 9 9, g32p_row26_traceSegment_008_0072_0009, g32p_row26_traceSegment_008_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 90 9 9, g32p_row26_traceSegment_008_0090_0009, g32p_row26_traceSegment_008_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 72 18 18, g32p_row26_traceSegment_008_0072_0018, g32p_row26_traceSegment_008_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 108 9 9, g32p_row26_traceSegment_008_0108_0009, g32p_row26_traceSegment_008_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 126 9 9, g32p_row26_traceSegment_008_0126_0009, g32p_row26_traceSegment_008_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 108 18 18, g32p_row26_traceSegment_008_0108_0018, g32p_row26_traceSegment_008_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 72 36 36, g32p_row26_traceSegment_008_0072_0036, g32p_row26_traceSegment_008_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_008 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 0 72 72, g32p_row26_traceSegment_008_0000_0072, g32p_row26_traceSegment_008_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 144 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 144 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 144 9 9, g32p_row26_traceSegment_008_0144_0009, g32p_row26_traceSegment_008_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 162 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 162 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 162 9 9, g32p_row26_traceSegment_008_0162_0009, g32p_row26_traceSegment_008_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 144 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 144 18 18, g32p_row26_traceSegment_008_0144_0018, g32p_row26_traceSegment_008_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 180 9 9, g32p_row26_traceSegment_008_0180_0009, g32p_row26_traceSegment_008_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 198 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 198 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 198 9 9, g32p_row26_traceSegment_008_0198_0009, g32p_row26_traceSegment_008_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 180 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 180 18 18, g32p_row26_traceSegment_008_0180_0018, g32p_row26_traceSegment_008_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 144 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 144 36 36, g32p_row26_traceSegment_008_0144_0036, g32p_row26_traceSegment_008_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 216 9 9, g32p_row26_traceSegment_008_0216_0009, g32p_row26_traceSegment_008_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 234 9 9, g32p_row26_traceSegment_008_0234_0009, g32p_row26_traceSegment_008_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 216 18 18, g32p_row26_traceSegment_008_0216_0018, g32p_row26_traceSegment_008_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 252 9 9, g32p_row26_traceSegment_008_0252_0009, g32p_row26_traceSegment_008_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 270 9 9, g32p_row26_traceSegment_008_0270_0009, g32p_row26_traceSegment_008_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 252 18 18, g32p_row26_traceSegment_008_0252_0018, g32p_row26_traceSegment_008_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 216 36 36, g32p_row26_traceSegment_008_0216_0036, g32p_row26_traceSegment_008_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_008 144 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 144 72 72, g32p_row26_traceSegment_008_0144_0072, g32p_row26_traceSegment_008_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_008 0 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 0 144 144, g32p_row26_traceSegment_008_0000_0144, g32p_row26_traceSegment_008_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 288 9 9, g32p_row26_traceSegment_008_0288_0009, g32p_row26_traceSegment_008_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 306 9 9, g32p_row26_traceSegment_008_0306_0009, g32p_row26_traceSegment_008_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 288 18 18, g32p_row26_traceSegment_008_0288_0018, g32p_row26_traceSegment_008_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 324 9 9, g32p_row26_traceSegment_008_0324_0009, g32p_row26_traceSegment_008_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 342 9 9, g32p_row26_traceSegment_008_0342_0009, g32p_row26_traceSegment_008_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 324 18 18, g32p_row26_traceSegment_008_0324_0018, g32p_row26_traceSegment_008_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 288 36 36, g32p_row26_traceSegment_008_0288_0036, g32p_row26_traceSegment_008_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 360 9 9, g32p_row26_traceSegment_008_0360_0009, g32p_row26_traceSegment_008_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 378 9 9, g32p_row26_traceSegment_008_0378_0009, g32p_row26_traceSegment_008_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 360 18 18, g32p_row26_traceSegment_008_0360_0018, g32p_row26_traceSegment_008_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 396 9 9, g32p_row26_traceSegment_008_0396_0009, g32p_row26_traceSegment_008_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 414 9 9, g32p_row26_traceSegment_008_0414_0009, g32p_row26_traceSegment_008_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 396 18 18, g32p_row26_traceSegment_008_0396_0018, g32p_row26_traceSegment_008_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 360 36 36, g32p_row26_traceSegment_008_0360_0036, g32p_row26_traceSegment_008_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_008 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 288 72 72, g32p_row26_traceSegment_008_0288_0072, g32p_row26_traceSegment_008_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 432 9 9, g32p_row26_traceSegment_008_0432_0009, g32p_row26_traceSegment_008_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 450 9 9, g32p_row26_traceSegment_008_0450_0009, g32p_row26_traceSegment_008_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 432 18 18, g32p_row26_traceSegment_008_0432_0018, g32p_row26_traceSegment_008_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 468 9 9, g32p_row26_traceSegment_008_0468_0009, g32p_row26_traceSegment_008_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 486 9 9, g32p_row26_traceSegment_008_0486_0009, g32p_row26_traceSegment_008_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 468 18 18, g32p_row26_traceSegment_008_0468_0018, g32p_row26_traceSegment_008_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 432 36 36, g32p_row26_traceSegment_008_0432_0036, g32p_row26_traceSegment_008_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 504 9 9, g32p_row26_traceSegment_008_0504_0009, g32p_row26_traceSegment_008_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 522 9 9, g32p_row26_traceSegment_008_0522_0009, g32p_row26_traceSegment_008_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 504 18 18, g32p_row26_traceSegment_008_0504_0018, g32p_row26_traceSegment_008_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 540 9 9, g32p_row26_traceSegment_008_0540_0009, g32p_row26_traceSegment_008_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_008 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_008_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_008 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 558 9 9, g32p_row26_traceSegment_008_0558_0009, g32p_row26_traceSegment_008_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_008 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 540 18 18, g32p_row26_traceSegment_008_0540_0018, g32p_row26_traceSegment_008_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_008 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 504 36 36, g32p_row26_traceSegment_008_0504_0036, g32p_row26_traceSegment_008_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_008 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 432 72 72, g32p_row26_traceSegment_008_0432_0072, g32p_row26_traceSegment_008_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_008 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 288 144 144, g32p_row26_traceSegment_008_0288_0144, g32p_row26_traceSegment_008_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_008_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_008 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_008 0 288 288, g32p_row26_traceSegment_008_0000_0288, g32p_row26_traceSegment_008_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 8 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_008_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_013_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 0 9 9, g32p_row26_traceSegment_013_0000_0009, g32p_row26_traceSegment_013_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 18 9 9, g32p_row26_traceSegment_013_0018_0009, g32p_row26_traceSegment_013_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 0 18 18, g32p_row26_traceSegment_013_0000_0018, g32p_row26_traceSegment_013_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 36 9 9, g32p_row26_traceSegment_013_0036_0009, g32p_row26_traceSegment_013_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 54 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 54 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 54 9 9, g32p_row26_traceSegment_013_0054_0009, g32p_row26_traceSegment_013_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 36 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 36 18 18, g32p_row26_traceSegment_013_0036_0018, g32p_row26_traceSegment_013_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 0 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 0 36 36, g32p_row26_traceSegment_013_0000_0036, g32p_row26_traceSegment_013_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 72 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 72 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 72 9 9, g32p_row26_traceSegment_013_0072_0009, g32p_row26_traceSegment_013_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 90 9 9, g32p_row26_traceSegment_013_0090_0009, g32p_row26_traceSegment_013_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 72 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 72 18 18, g32p_row26_traceSegment_013_0072_0018, g32p_row26_traceSegment_013_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 108 9 9, g32p_row26_traceSegment_013_0108_0009, g32p_row26_traceSegment_013_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 135 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 126 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 126 9 9, g32p_row26_traceSegment_013_0126_0009, g32p_row26_traceSegment_013_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 108 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 108 18 18, g32p_row26_traceSegment_013_0108_0018, g32p_row26_traceSegment_013_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 72 72 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 72 36 36, g32p_row26_traceSegment_013_0072_0036, g32p_row26_traceSegment_013_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_013 0 144 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 0 72 72, g32p_row26_traceSegment_013_0000_0072, g32p_row26_traceSegment_013_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 144 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 144 9 9, g32p_row26_traceSegment_013_0144_0009, g32p_row26_traceSegment_013_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 171 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 162 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 162 9 9, g32p_row26_traceSegment_013_0162_0009, g32p_row26_traceSegment_013_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 144 36 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 144 18 18, g32p_row26_traceSegment_013_0144_0018, g32p_row26_traceSegment_013_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 180 9 9, g32p_row26_traceSegment_013_0180_0009, g32p_row26_traceSegment_013_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 198 9 9, g32p_row26_traceSegment_013_0198_0009, g32p_row26_traceSegment_013_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 180 18 18, g32p_row26_traceSegment_013_0180_0018, g32p_row26_traceSegment_013_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 144 72 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 144 36 36, g32p_row26_traceSegment_013_0144_0036, g32p_row26_traceSegment_013_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 216 9 9, g32p_row26_traceSegment_013_0216_0009, g32p_row26_traceSegment_013_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 234 9 9, g32p_row26_traceSegment_013_0234_0009, g32p_row26_traceSegment_013_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 216 18 18, g32p_row26_traceSegment_013_0216_0018, g32p_row26_traceSegment_013_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 261 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 252 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 252 9 9, g32p_row26_traceSegment_013_0252_0009, g32p_row26_traceSegment_013_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 270 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 270 9 9, g32p_row26_traceSegment_013_0270_0009, g32p_row26_traceSegment_013_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 252 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 252 18 18, g32p_row26_traceSegment_013_0252_0018, g32p_row26_traceSegment_013_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 216 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 216 36 36, g32p_row26_traceSegment_013_0216_0036, g32p_row26_traceSegment_013_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_013 144 144 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 144 72 72, g32p_row26_traceSegment_013_0144_0072, g32p_row26_traceSegment_013_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_013 0 288 = [0, 0, 4, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 0 144 144, g32p_row26_traceSegment_013_0000_0144, g32p_row26_traceSegment_013_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 297 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 288 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 288 9 9, g32p_row26_traceSegment_013_0288_0009, g32p_row26_traceSegment_013_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 306 9 9, g32p_row26_traceSegment_013_0306_0009, g32p_row26_traceSegment_013_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 288 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 288 18 18, g32p_row26_traceSegment_013_0288_0018, g32p_row26_traceSegment_013_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 324 9 9, g32p_row26_traceSegment_013_0324_0009, g32p_row26_traceSegment_013_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 342 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 342 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 342 9 9, g32p_row26_traceSegment_013_0342_0009, g32p_row26_traceSegment_013_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 324 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 324 18 18, g32p_row26_traceSegment_013_0324_0018, g32p_row26_traceSegment_013_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 288 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 288 36 36, g32p_row26_traceSegment_013_0288_0036, g32p_row26_traceSegment_013_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 360 9 9, g32p_row26_traceSegment_013_0360_0009, g32p_row26_traceSegment_013_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 378 9 9, g32p_row26_traceSegment_013_0378_0009, g32p_row26_traceSegment_013_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 360 18 18, g32p_row26_traceSegment_013_0360_0018, g32p_row26_traceSegment_013_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 396 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 396 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 396 9 9, g32p_row26_traceSegment_013_0396_0009, g32p_row26_traceSegment_013_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 414 9 9, g32p_row26_traceSegment_013_0414_0009, g32p_row26_traceSegment_013_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 396 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 396 18 18, g32p_row26_traceSegment_013_0396_0018, g32p_row26_traceSegment_013_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 360 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 360 36 36, g32p_row26_traceSegment_013_0360_0036, g32p_row26_traceSegment_013_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_013 288 144 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 288 72 72, g32p_row26_traceSegment_013_0288_0072, g32p_row26_traceSegment_013_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 432 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 441 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 432 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 432 9 9, g32p_row26_traceSegment_013_0432_0009, g32p_row26_traceSegment_013_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 450 9 9, g32p_row26_traceSegment_013_0450_0009, g32p_row26_traceSegment_013_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 432 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 432 18 18, g32p_row26_traceSegment_013_0432_0018, g32p_row26_traceSegment_013_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 477 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 468 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 468 9 9, g32p_row26_traceSegment_013_0468_0009, g32p_row26_traceSegment_013_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 486 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 495 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 486 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 486 9 9, g32p_row26_traceSegment_013_0486_0009, g32p_row26_traceSegment_013_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 468 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 468 18 18, g32p_row26_traceSegment_013_0468_0018, g32p_row26_traceSegment_013_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 432 72 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 432 36 36, g32p_row26_traceSegment_013_0432_0036, g32p_row26_traceSegment_013_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 504 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 504 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 504 9 9, g32p_row26_traceSegment_013_0504_0009, g32p_row26_traceSegment_013_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 531 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 522 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 522 9 9, g32p_row26_traceSegment_013_0522_0009, g32p_row26_traceSegment_013_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 504 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 504 18 18, g32p_row26_traceSegment_013_0504_0018, g32p_row26_traceSegment_013_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 540 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 549 9 = [0, 0, 2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 540 18 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 540 9 9, g32p_row26_traceSegment_013_0540_0009, g32p_row26_traceSegment_013_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 558 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_013 567 9 = [0, 0, 4, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_013_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_013 558 18 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 558 9 9, g32p_row26_traceSegment_013_0558_0009, g32p_row26_traceSegment_013_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_013 540 36 = [0, 0, 8, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 540 18 18, g32p_row26_traceSegment_013_0540_0018, g32p_row26_traceSegment_013_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_013 504 72 = [0, 0, 8, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 504 36 36, g32p_row26_traceSegment_013_0504_0036, g32p_row26_traceSegment_013_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_013 432 144 = [0, 0, 8, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 432 72 72, g32p_row26_traceSegment_013_0432_0072, g32p_row26_traceSegment_013_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_013 288 288 = [0, 0, 8, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 288 144 144, g32p_row26_traceSegment_013_0288_0144, g32p_row26_traceSegment_013_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_013_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_013 0 576 = [0, 0, 12, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_013 0 288 288, g32p_row26_traceSegment_013_0000_0288, g32p_row26_traceSegment_013_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 13 = [0, 0, 12, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_013_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 0) (g32p_literalTraceValue 25 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_000]
  decide +kernel

theorem g32p_row26_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 1) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 1) (g32p_literalTraceValue 25 1)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row26_traceCoefficients_001]
  decide +kernel

theorem g32p_row26_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 2) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 2) (g32p_literalTraceValue 25 2)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_002]
  decide +kernel

theorem g32p_row26_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 3) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 3) (g32p_literalTraceValue 25 3)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_003]
  decide +kernel

theorem g32p_row26_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 5) (g32p_literalTraceValue 25 5)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_005]
  decide +kernel

theorem g32p_row26_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 7) (g32p_literalTraceValue 25 7)
      [1, -1, 1] [-576, 576, 576] = true := by
  rw [g32p_row26_traceCoefficients_007]
  decide +kernel

theorem g32p_row26_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 8) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 8) (g32p_literalTraceValue 25 8)
      [1, -1, 1] [1728, 1728, 1728] = true := by
  rw [g32p_row26_traceCoefficients_008]
  decide +kernel

theorem g32p_row26_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 13) (g32p_literalTraceValue 25 13)
      [1, -1, 1] [0, 0, 6912, 6912] = true := by
  rw [g32p_row26_traceCoefficients_013]
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

private def g32p_row26_traceSegment_017 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 17 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_017_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 0 9 9, g32p_row26_traceSegment_017_0000_0009, g32p_row26_traceSegment_017_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 18 9 9, g32p_row26_traceSegment_017_0018_0009, g32p_row26_traceSegment_017_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 0 18 18, g32p_row26_traceSegment_017_0000_0018, g32p_row26_traceSegment_017_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 45 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 36 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 36 9 9, g32p_row26_traceSegment_017_0036_0009, g32p_row26_traceSegment_017_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 54 9 9, g32p_row26_traceSegment_017_0054_0009, g32p_row26_traceSegment_017_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 36 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 36 18 18, g32p_row26_traceSegment_017_0036_0018, g32p_row26_traceSegment_017_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 0 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 0 36 36, g32p_row26_traceSegment_017_0000_0036, g32p_row26_traceSegment_017_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 72 9 9, g32p_row26_traceSegment_017_0072_0009, g32p_row26_traceSegment_017_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 90 9 9, g32p_row26_traceSegment_017_0090_0009, g32p_row26_traceSegment_017_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 72 18 18, g32p_row26_traceSegment_017_0072_0018, g32p_row26_traceSegment_017_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 108 9 9, g32p_row26_traceSegment_017_0108_0009, g32p_row26_traceSegment_017_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 126 9 9, g32p_row26_traceSegment_017_0126_0009, g32p_row26_traceSegment_017_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 108 18 18, g32p_row26_traceSegment_017_0108_0018, g32p_row26_traceSegment_017_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 72 36 36, g32p_row26_traceSegment_017_0072_0036, g32p_row26_traceSegment_017_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_017 0 144 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 0 72 72, g32p_row26_traceSegment_017_0000_0072, g32p_row26_traceSegment_017_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 144 9 9, g32p_row26_traceSegment_017_0144_0009, g32p_row26_traceSegment_017_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 162 9 9, g32p_row26_traceSegment_017_0162_0009, g32p_row26_traceSegment_017_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 144 18 18, g32p_row26_traceSegment_017_0144_0018, g32p_row26_traceSegment_017_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 189 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 180 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 180 9 9, g32p_row26_traceSegment_017_0180_0009, g32p_row26_traceSegment_017_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 198 9 9, g32p_row26_traceSegment_017_0198_0009, g32p_row26_traceSegment_017_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 180 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 180 18 18, g32p_row26_traceSegment_017_0180_0018, g32p_row26_traceSegment_017_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 144 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 144 36 36, g32p_row26_traceSegment_017_0144_0036, g32p_row26_traceSegment_017_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 225 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 216 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 216 9 9, g32p_row26_traceSegment_017_0216_0009, g32p_row26_traceSegment_017_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 234 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 243 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 234 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 234 9 9, g32p_row26_traceSegment_017_0234_0009, g32p_row26_traceSegment_017_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 216 36 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 216 18 18, g32p_row26_traceSegment_017_0216_0018, g32p_row26_traceSegment_017_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 252 9 9, g32p_row26_traceSegment_017_0252_0009, g32p_row26_traceSegment_017_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 270 9 9, g32p_row26_traceSegment_017_0270_0009, g32p_row26_traceSegment_017_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 252 18 18, g32p_row26_traceSegment_017_0252_0018, g32p_row26_traceSegment_017_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 216 72 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 216 36 36, g32p_row26_traceSegment_017_0216_0036, g32p_row26_traceSegment_017_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_017 144 144 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 144 72 72, g32p_row26_traceSegment_017_0144_0072, g32p_row26_traceSegment_017_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_017 0 288 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 0 144 144, g32p_row26_traceSegment_017_0000_0144, g32p_row26_traceSegment_017_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 297 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 288 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 288 9 9, g32p_row26_traceSegment_017_0288_0009, g32p_row26_traceSegment_017_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 315 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 306 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 306 9 9, g32p_row26_traceSegment_017_0306_0009, g32p_row26_traceSegment_017_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 288 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 288 18 18, g32p_row26_traceSegment_017_0288_0018, g32p_row26_traceSegment_017_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 324 9 9, g32p_row26_traceSegment_017_0324_0009, g32p_row26_traceSegment_017_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 342 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 342 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 342 9 9, g32p_row26_traceSegment_017_0342_0009, g32p_row26_traceSegment_017_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 324 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 324 18 18, g32p_row26_traceSegment_017_0324_0018, g32p_row26_traceSegment_017_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 288 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 288 36 36, g32p_row26_traceSegment_017_0288_0036, g32p_row26_traceSegment_017_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 360 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 369 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 360 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 360 9 9, g32p_row26_traceSegment_017_0360_0009, g32p_row26_traceSegment_017_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 378 9 9, g32p_row26_traceSegment_017_0378_0009, g32p_row26_traceSegment_017_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 360 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 360 18 18, g32p_row26_traceSegment_017_0360_0018, g32p_row26_traceSegment_017_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 396 9 9, g32p_row26_traceSegment_017_0396_0009, g32p_row26_traceSegment_017_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 414 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 423 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 414 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 414 9 9, g32p_row26_traceSegment_017_0414_0009, g32p_row26_traceSegment_017_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 396 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 396 18 18, g32p_row26_traceSegment_017_0396_0018, g32p_row26_traceSegment_017_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 360 72 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 360 36 36, g32p_row26_traceSegment_017_0360_0036, g32p_row26_traceSegment_017_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_017 288 144 = [2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 288 72 72, g32p_row26_traceSegment_017_0288_0072, g32p_row26_traceSegment_017_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 432 9 = [2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 441 9 = [2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 432 18 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 432 9 9, g32p_row26_traceSegment_017_0432_0009, g32p_row26_traceSegment_017_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 450 9 9, g32p_row26_traceSegment_017_0450_0009, g32p_row26_traceSegment_017_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 432 36 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 432 18 18, g32p_row26_traceSegment_017_0432_0018, g32p_row26_traceSegment_017_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 468 9 9, g32p_row26_traceSegment_017_0468_0009, g32p_row26_traceSegment_017_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 495 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 486 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 486 9 9, g32p_row26_traceSegment_017_0486_0009, g32p_row26_traceSegment_017_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 468 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 468 18 18, g32p_row26_traceSegment_017_0468_0018, g32p_row26_traceSegment_017_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 432 72 = [4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 432 36 36, g32p_row26_traceSegment_017_0432_0036, g32p_row26_traceSegment_017_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 504 9 9, g32p_row26_traceSegment_017_0504_0009, g32p_row26_traceSegment_017_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 522 9 9, g32p_row26_traceSegment_017_0522_0009, g32p_row26_traceSegment_017_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 504 18 18, g32p_row26_traceSegment_017_0504_0018, g32p_row26_traceSegment_017_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 540 9 9, g32p_row26_traceSegment_017_0540_0009, g32p_row26_traceSegment_017_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 558 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_017 567 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_017_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_017 558 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 558 9 9, g32p_row26_traceSegment_017_0558_0009, g32p_row26_traceSegment_017_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_017 540 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 540 18 18, g32p_row26_traceSegment_017_0540_0018, g32p_row26_traceSegment_017_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_017 504 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 504 36 36, g32p_row26_traceSegment_017_0504_0036, g32p_row26_traceSegment_017_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_017 432 144 = [4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 432 72 72, g32p_row26_traceSegment_017_0432_0072, g32p_row26_traceSegment_017_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_017 288 288 = [6, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 288 144 144, g32p_row26_traceSegment_017_0288_0144, g32p_row26_traceSegment_017_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_017_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_017 0 576 = [8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_017 0 288 288, g32p_row26_traceSegment_017_0000_0288, g32p_row26_traceSegment_017_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 17 = [8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_017_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_018_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 9 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 0 9 9, g32p_row26_traceSegment_018_0000_0009, g32p_row26_traceSegment_018_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 18 9 9, g32p_row26_traceSegment_018_0018_0009, g32p_row26_traceSegment_018_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 0 18 18, g32p_row26_traceSegment_018_0000_0018, g32p_row26_traceSegment_018_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 45 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 36 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 36 9 9, g32p_row26_traceSegment_018_0036_0009, g32p_row26_traceSegment_018_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 54 9 9, g32p_row26_traceSegment_018_0054_0009, g32p_row26_traceSegment_018_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 36 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 36 18 18, g32p_row26_traceSegment_018_0036_0018, g32p_row26_traceSegment_018_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 0 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 0 36 36, g32p_row26_traceSegment_018_0000_0036, g32p_row26_traceSegment_018_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 72 9 9, g32p_row26_traceSegment_018_0072_0009, g32p_row26_traceSegment_018_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 90 9 9, g32p_row26_traceSegment_018_0090_0009, g32p_row26_traceSegment_018_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 72 18 18, g32p_row26_traceSegment_018_0072_0018, g32p_row26_traceSegment_018_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 108 9 9, g32p_row26_traceSegment_018_0108_0009, g32p_row26_traceSegment_018_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 126 9 9, g32p_row26_traceSegment_018_0126_0009, g32p_row26_traceSegment_018_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 108 18 18, g32p_row26_traceSegment_018_0108_0018, g32p_row26_traceSegment_018_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 72 36 36, g32p_row26_traceSegment_018_0072_0036, g32p_row26_traceSegment_018_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_018 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 0 72 72, g32p_row26_traceSegment_018_0000_0072, g32p_row26_traceSegment_018_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 144 9 9, g32p_row26_traceSegment_018_0144_0009, g32p_row26_traceSegment_018_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 162 9 9, g32p_row26_traceSegment_018_0162_0009, g32p_row26_traceSegment_018_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 144 18 18, g32p_row26_traceSegment_018_0144_0018, g32p_row26_traceSegment_018_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 180 9 9, g32p_row26_traceSegment_018_0180_0009, g32p_row26_traceSegment_018_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 198 9 9, g32p_row26_traceSegment_018_0198_0009, g32p_row26_traceSegment_018_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 180 18 18, g32p_row26_traceSegment_018_0180_0018, g32p_row26_traceSegment_018_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 144 36 36, g32p_row26_traceSegment_018_0144_0036, g32p_row26_traceSegment_018_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 216 9 9, g32p_row26_traceSegment_018_0216_0009, g32p_row26_traceSegment_018_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 234 9 9, g32p_row26_traceSegment_018_0234_0009, g32p_row26_traceSegment_018_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 216 18 18, g32p_row26_traceSegment_018_0216_0018, g32p_row26_traceSegment_018_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 252 9 9, g32p_row26_traceSegment_018_0252_0009, g32p_row26_traceSegment_018_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 270 9 9, g32p_row26_traceSegment_018_0270_0009, g32p_row26_traceSegment_018_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 252 18 18, g32p_row26_traceSegment_018_0252_0018, g32p_row26_traceSegment_018_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 216 36 36, g32p_row26_traceSegment_018_0216_0036, g32p_row26_traceSegment_018_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_018 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 144 72 72, g32p_row26_traceSegment_018_0144_0072, g32p_row26_traceSegment_018_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_018 0 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 0 144 144, g32p_row26_traceSegment_018_0000_0144, g32p_row26_traceSegment_018_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 288 9 9, g32p_row26_traceSegment_018_0288_0009, g32p_row26_traceSegment_018_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 306 9 9, g32p_row26_traceSegment_018_0306_0009, g32p_row26_traceSegment_018_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 288 18 18, g32p_row26_traceSegment_018_0288_0018, g32p_row26_traceSegment_018_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 324 9 9, g32p_row26_traceSegment_018_0324_0009, g32p_row26_traceSegment_018_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 342 9 9, g32p_row26_traceSegment_018_0342_0009, g32p_row26_traceSegment_018_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 324 18 18, g32p_row26_traceSegment_018_0324_0018, g32p_row26_traceSegment_018_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 288 36 36, g32p_row26_traceSegment_018_0288_0036, g32p_row26_traceSegment_018_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 360 9 9, g32p_row26_traceSegment_018_0360_0009, g32p_row26_traceSegment_018_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 378 9 9, g32p_row26_traceSegment_018_0378_0009, g32p_row26_traceSegment_018_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 360 18 18, g32p_row26_traceSegment_018_0360_0018, g32p_row26_traceSegment_018_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 396 9 9, g32p_row26_traceSegment_018_0396_0009, g32p_row26_traceSegment_018_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 414 9 9, g32p_row26_traceSegment_018_0414_0009, g32p_row26_traceSegment_018_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 396 18 18, g32p_row26_traceSegment_018_0396_0018, g32p_row26_traceSegment_018_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 360 36 36, g32p_row26_traceSegment_018_0360_0036, g32p_row26_traceSegment_018_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_018 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 288 72 72, g32p_row26_traceSegment_018_0288_0072, g32p_row26_traceSegment_018_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 432 9 9, g32p_row26_traceSegment_018_0432_0009, g32p_row26_traceSegment_018_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 450 9 9, g32p_row26_traceSegment_018_0450_0009, g32p_row26_traceSegment_018_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 432 18 18, g32p_row26_traceSegment_018_0432_0018, g32p_row26_traceSegment_018_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 468 9 9, g32p_row26_traceSegment_018_0468_0009, g32p_row26_traceSegment_018_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 486 9 9, g32p_row26_traceSegment_018_0486_0009, g32p_row26_traceSegment_018_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 468 18 18, g32p_row26_traceSegment_018_0468_0018, g32p_row26_traceSegment_018_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 432 36 36, g32p_row26_traceSegment_018_0432_0036, g32p_row26_traceSegment_018_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 504 9 9, g32p_row26_traceSegment_018_0504_0009, g32p_row26_traceSegment_018_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 522 9 9, g32p_row26_traceSegment_018_0522_0009, g32p_row26_traceSegment_018_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 504 18 18, g32p_row26_traceSegment_018_0504_0018, g32p_row26_traceSegment_018_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 540 9 9, g32p_row26_traceSegment_018_0540_0009, g32p_row26_traceSegment_018_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_018 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_018_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_018 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 558 9 9, g32p_row26_traceSegment_018_0558_0009, g32p_row26_traceSegment_018_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_018 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 540 18 18, g32p_row26_traceSegment_018_0540_0018, g32p_row26_traceSegment_018_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_018 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 504 36 36, g32p_row26_traceSegment_018_0504_0036, g32p_row26_traceSegment_018_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_018 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 432 72 72, g32p_row26_traceSegment_018_0432_0072, g32p_row26_traceSegment_018_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_018 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 288 144 144, g32p_row26_traceSegment_018_0288_0144, g32p_row26_traceSegment_018_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_018_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_018 0 576 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_018 0 288 288, g32p_row26_traceSegment_018_0000_0288, g32p_row26_traceSegment_018_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 18 = [2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_018_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_019 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 19 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_019_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 0 9 9, g32p_row26_traceSegment_019_0000_0009, g32p_row26_traceSegment_019_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 18 9 9, g32p_row26_traceSegment_019_0018_0009, g32p_row26_traceSegment_019_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 0 18 18, g32p_row26_traceSegment_019_0000_0018, g32p_row26_traceSegment_019_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 36 9 9, g32p_row26_traceSegment_019_0036_0009, g32p_row26_traceSegment_019_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 54 9 9, g32p_row26_traceSegment_019_0054_0009, g32p_row26_traceSegment_019_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 36 18 18, g32p_row26_traceSegment_019_0036_0018, g32p_row26_traceSegment_019_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 0 36 36, g32p_row26_traceSegment_019_0000_0036, g32p_row26_traceSegment_019_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 72 9 9, g32p_row26_traceSegment_019_0072_0009, g32p_row26_traceSegment_019_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 90 9 9, g32p_row26_traceSegment_019_0090_0009, g32p_row26_traceSegment_019_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 72 18 18, g32p_row26_traceSegment_019_0072_0018, g32p_row26_traceSegment_019_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 108 9 9, g32p_row26_traceSegment_019_0108_0009, g32p_row26_traceSegment_019_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 126 9 9, g32p_row26_traceSegment_019_0126_0009, g32p_row26_traceSegment_019_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 108 18 18, g32p_row26_traceSegment_019_0108_0018, g32p_row26_traceSegment_019_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 72 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 72 36 36, g32p_row26_traceSegment_019_0072_0036, g32p_row26_traceSegment_019_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_019 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 0 72 72, g32p_row26_traceSegment_019_0000_0072, g32p_row26_traceSegment_019_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 144 9 9, g32p_row26_traceSegment_019_0144_0009, g32p_row26_traceSegment_019_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 162 9 9, g32p_row26_traceSegment_019_0162_0009, g32p_row26_traceSegment_019_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 144 18 18, g32p_row26_traceSegment_019_0144_0018, g32p_row26_traceSegment_019_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 189 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 180 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 180 9 9, g32p_row26_traceSegment_019_0180_0009, g32p_row26_traceSegment_019_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 198 9 9, g32p_row26_traceSegment_019_0198_0009, g32p_row26_traceSegment_019_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 180 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 180 18 18, g32p_row26_traceSegment_019_0180_0018, g32p_row26_traceSegment_019_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 144 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 144 36 36, g32p_row26_traceSegment_019_0144_0036, g32p_row26_traceSegment_019_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 216 9 9, g32p_row26_traceSegment_019_0216_0009, g32p_row26_traceSegment_019_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 243 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 234 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 234 9 9, g32p_row26_traceSegment_019_0234_0009, g32p_row26_traceSegment_019_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 216 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 216 18 18, g32p_row26_traceSegment_019_0216_0018, g32p_row26_traceSegment_019_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 252 9 9, g32p_row26_traceSegment_019_0252_0009, g32p_row26_traceSegment_019_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 270 9 9, g32p_row26_traceSegment_019_0270_0009, g32p_row26_traceSegment_019_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 252 18 18, g32p_row26_traceSegment_019_0252_0018, g32p_row26_traceSegment_019_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 216 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 216 36 36, g32p_row26_traceSegment_019_0216_0036, g32p_row26_traceSegment_019_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_019 144 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 144 72 72, g32p_row26_traceSegment_019_0144_0072, g32p_row26_traceSegment_019_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_019 0 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 0 144 144, g32p_row26_traceSegment_019_0000_0144, g32p_row26_traceSegment_019_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 288 9 9, g32p_row26_traceSegment_019_0288_0009, g32p_row26_traceSegment_019_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 306 9 9, g32p_row26_traceSegment_019_0306_0009, g32p_row26_traceSegment_019_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 288 18 18, g32p_row26_traceSegment_019_0288_0018, g32p_row26_traceSegment_019_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 324 9 9, g32p_row26_traceSegment_019_0324_0009, g32p_row26_traceSegment_019_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 342 9 9, g32p_row26_traceSegment_019_0342_0009, g32p_row26_traceSegment_019_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 324 18 18, g32p_row26_traceSegment_019_0324_0018, g32p_row26_traceSegment_019_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 288 36 36, g32p_row26_traceSegment_019_0288_0036, g32p_row26_traceSegment_019_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 360 9 9, g32p_row26_traceSegment_019_0360_0009, g32p_row26_traceSegment_019_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 378 9 9, g32p_row26_traceSegment_019_0378_0009, g32p_row26_traceSegment_019_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 360 18 18, g32p_row26_traceSegment_019_0360_0018, g32p_row26_traceSegment_019_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 396 9 9, g32p_row26_traceSegment_019_0396_0009, g32p_row26_traceSegment_019_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 414 9 9, g32p_row26_traceSegment_019_0414_0009, g32p_row26_traceSegment_019_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 396 18 18, g32p_row26_traceSegment_019_0396_0018, g32p_row26_traceSegment_019_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 360 36 36, g32p_row26_traceSegment_019_0360_0036, g32p_row26_traceSegment_019_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_019 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 288 72 72, g32p_row26_traceSegment_019_0288_0072, g32p_row26_traceSegment_019_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 432 9 9, g32p_row26_traceSegment_019_0432_0009, g32p_row26_traceSegment_019_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 450 9 9, g32p_row26_traceSegment_019_0450_0009, g32p_row26_traceSegment_019_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 432 18 18, g32p_row26_traceSegment_019_0432_0018, g32p_row26_traceSegment_019_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 468 9 9, g32p_row26_traceSegment_019_0468_0009, g32p_row26_traceSegment_019_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 486 9 9, g32p_row26_traceSegment_019_0486_0009, g32p_row26_traceSegment_019_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 468 18 18, g32p_row26_traceSegment_019_0468_0018, g32p_row26_traceSegment_019_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 432 36 36, g32p_row26_traceSegment_019_0432_0036, g32p_row26_traceSegment_019_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 504 9 9, g32p_row26_traceSegment_019_0504_0009, g32p_row26_traceSegment_019_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 522 9 9, g32p_row26_traceSegment_019_0522_0009, g32p_row26_traceSegment_019_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 504 18 18, g32p_row26_traceSegment_019_0504_0018, g32p_row26_traceSegment_019_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 540 9 9, g32p_row26_traceSegment_019_0540_0009, g32p_row26_traceSegment_019_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_019 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_019_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_019 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 558 9 9, g32p_row26_traceSegment_019_0558_0009, g32p_row26_traceSegment_019_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_019 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 540 18 18, g32p_row26_traceSegment_019_0540_0018, g32p_row26_traceSegment_019_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_019 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 504 36 36, g32p_row26_traceSegment_019_0504_0036, g32p_row26_traceSegment_019_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_019 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 432 72 72, g32p_row26_traceSegment_019_0432_0072, g32p_row26_traceSegment_019_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_019 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 288 144 144, g32p_row26_traceSegment_019_0288_0144, g32p_row26_traceSegment_019_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_019_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_019 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_019 0 288 288, g32p_row26_traceSegment_019_0000_0288, g32p_row26_traceSegment_019_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 19 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_019_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_020 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 20 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_020_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 0 9 9, g32p_row26_traceSegment_020_0000_0009, g32p_row26_traceSegment_020_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 18 9 9, g32p_row26_traceSegment_020_0018_0009, g32p_row26_traceSegment_020_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 0 18 18, g32p_row26_traceSegment_020_0000_0018, g32p_row26_traceSegment_020_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 36 9 9, g32p_row26_traceSegment_020_0036_0009, g32p_row26_traceSegment_020_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 54 9 9, g32p_row26_traceSegment_020_0054_0009, g32p_row26_traceSegment_020_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 36 18 18, g32p_row26_traceSegment_020_0036_0018, g32p_row26_traceSegment_020_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 0 36 36, g32p_row26_traceSegment_020_0000_0036, g32p_row26_traceSegment_020_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 72 9 9, g32p_row26_traceSegment_020_0072_0009, g32p_row26_traceSegment_020_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 90 9 9, g32p_row26_traceSegment_020_0090_0009, g32p_row26_traceSegment_020_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 72 18 18, g32p_row26_traceSegment_020_0072_0018, g32p_row26_traceSegment_020_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 108 9 9, g32p_row26_traceSegment_020_0108_0009, g32p_row26_traceSegment_020_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 126 9 9, g32p_row26_traceSegment_020_0126_0009, g32p_row26_traceSegment_020_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 108 18 18, g32p_row26_traceSegment_020_0108_0018, g32p_row26_traceSegment_020_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 72 36 36, g32p_row26_traceSegment_020_0072_0036, g32p_row26_traceSegment_020_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_020 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 0 72 72, g32p_row26_traceSegment_020_0000_0072, g32p_row26_traceSegment_020_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 153 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 144 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 144 9 9, g32p_row26_traceSegment_020_0144_0009, g32p_row26_traceSegment_020_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 162 9 9, g32p_row26_traceSegment_020_0162_0009, g32p_row26_traceSegment_020_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 144 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 144 18 18, g32p_row26_traceSegment_020_0144_0018, g32p_row26_traceSegment_020_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 180 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 180 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 180 9 9, g32p_row26_traceSegment_020_0180_0009, g32p_row26_traceSegment_020_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 198 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 198 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 198 9 9, g32p_row26_traceSegment_020_0198_0009, g32p_row26_traceSegment_020_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 180 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 180 18 18, g32p_row26_traceSegment_020_0180_0018, g32p_row26_traceSegment_020_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 144 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 144 36 36, g32p_row26_traceSegment_020_0144_0036, g32p_row26_traceSegment_020_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 216 9 9, g32p_row26_traceSegment_020_0216_0009, g32p_row26_traceSegment_020_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 243 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 234 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 234 9 9, g32p_row26_traceSegment_020_0234_0009, g32p_row26_traceSegment_020_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 216 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 216 18 18, g32p_row26_traceSegment_020_0216_0018, g32p_row26_traceSegment_020_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 252 9 9, g32p_row26_traceSegment_020_0252_0009, g32p_row26_traceSegment_020_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 270 9 9, g32p_row26_traceSegment_020_0270_0009, g32p_row26_traceSegment_020_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 252 18 18, g32p_row26_traceSegment_020_0252_0018, g32p_row26_traceSegment_020_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 216 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 216 36 36, g32p_row26_traceSegment_020_0216_0036, g32p_row26_traceSegment_020_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_020 144 144 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 144 72 72, g32p_row26_traceSegment_020_0144_0072, g32p_row26_traceSegment_020_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_020 0 288 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 0 144 144, g32p_row26_traceSegment_020_0000_0144, g32p_row26_traceSegment_020_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 288 9 9, g32p_row26_traceSegment_020_0288_0009, g32p_row26_traceSegment_020_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 306 9 9, g32p_row26_traceSegment_020_0306_0009, g32p_row26_traceSegment_020_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 288 18 18, g32p_row26_traceSegment_020_0288_0018, g32p_row26_traceSegment_020_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 324 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 333 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 324 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 324 9 9, g32p_row26_traceSegment_020_0324_0009, g32p_row26_traceSegment_020_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 342 9 9, g32p_row26_traceSegment_020_0342_0009, g32p_row26_traceSegment_020_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 324 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 324 18 18, g32p_row26_traceSegment_020_0324_0018, g32p_row26_traceSegment_020_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 288 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 288 36 36, g32p_row26_traceSegment_020_0288_0036, g32p_row26_traceSegment_020_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 360 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 369 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 360 18 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 360 9 9, g32p_row26_traceSegment_020_0360_0009, g32p_row26_traceSegment_020_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 378 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 387 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 378 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 378 9 9, g32p_row26_traceSegment_020_0378_0009, g32p_row26_traceSegment_020_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 360 36 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 360 18 18, g32p_row26_traceSegment_020_0360_0018, g32p_row26_traceSegment_020_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 396 9 9, g32p_row26_traceSegment_020_0396_0009, g32p_row26_traceSegment_020_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 423 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 414 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 414 9 9, g32p_row26_traceSegment_020_0414_0009, g32p_row26_traceSegment_020_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 396 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 396 18 18, g32p_row26_traceSegment_020_0396_0018, g32p_row26_traceSegment_020_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 360 72 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 360 36 36, g32p_row26_traceSegment_020_0360_0036, g32p_row26_traceSegment_020_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_020 288 144 = [0, 0, 4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 288 72 72, g32p_row26_traceSegment_020_0288_0072, g32p_row26_traceSegment_020_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 432 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 441 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 432 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 432 9 9, g32p_row26_traceSegment_020_0432_0009, g32p_row26_traceSegment_020_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 450 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 459 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 450 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 450 9 9, g32p_row26_traceSegment_020_0450_0009, g32p_row26_traceSegment_020_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 432 36 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 432 18 18, g32p_row26_traceSegment_020_0432_0018, g32p_row26_traceSegment_020_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 477 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 468 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 468 9 9, g32p_row26_traceSegment_020_0468_0009, g32p_row26_traceSegment_020_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 486 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 486 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 486 9 9, g32p_row26_traceSegment_020_0486_0009, g32p_row26_traceSegment_020_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 468 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 468 18 18, g32p_row26_traceSegment_020_0468_0018, g32p_row26_traceSegment_020_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 432 72 = [0, 0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 432 36 36, g32p_row26_traceSegment_020_0432_0036, g32p_row26_traceSegment_020_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 504 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 504 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 504 9 9, g32p_row26_traceSegment_020_0504_0009, g32p_row26_traceSegment_020_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 522 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 522 9 9, g32p_row26_traceSegment_020_0522_0009, g32p_row26_traceSegment_020_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 504 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 504 18 18, g32p_row26_traceSegment_020_0504_0018, g32p_row26_traceSegment_020_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 540 9 9, g32p_row26_traceSegment_020_0540_0009, g32p_row26_traceSegment_020_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_020 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_020_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_020 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 558 9 9, g32p_row26_traceSegment_020_0558_0009, g32p_row26_traceSegment_020_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_020 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 540 18 18, g32p_row26_traceSegment_020_0540_0018, g32p_row26_traceSegment_020_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_020 504 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 504 36 36, g32p_row26_traceSegment_020_0504_0036, g32p_row26_traceSegment_020_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_020 432 144 = [0, 0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 432 72 72, g32p_row26_traceSegment_020_0432_0072, g32p_row26_traceSegment_020_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_020 288 288 = [0, 0, 8, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 288 144 144, g32p_row26_traceSegment_020_0288_0144, g32p_row26_traceSegment_020_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_020_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_020 0 576 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_020 0 288 288, g32p_row26_traceSegment_020_0000_0288, g32p_row26_traceSegment_020_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 20 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_020_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_023 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 23 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_023_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 0 9 9, g32p_row26_traceSegment_023_0000_0009, g32p_row26_traceSegment_023_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 18 9 9, g32p_row26_traceSegment_023_0018_0009, g32p_row26_traceSegment_023_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 0 18 18, g32p_row26_traceSegment_023_0000_0018, g32p_row26_traceSegment_023_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 36 9 9, g32p_row26_traceSegment_023_0036_0009, g32p_row26_traceSegment_023_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 54 9 9, g32p_row26_traceSegment_023_0054_0009, g32p_row26_traceSegment_023_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 36 18 18, g32p_row26_traceSegment_023_0036_0018, g32p_row26_traceSegment_023_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 0 36 36, g32p_row26_traceSegment_023_0000_0036, g32p_row26_traceSegment_023_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 72 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 72 9 9, g32p_row26_traceSegment_023_0072_0009, g32p_row26_traceSegment_023_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 90 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 90 9 9, g32p_row26_traceSegment_023_0090_0009, g32p_row26_traceSegment_023_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 72 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 72 18 18, g32p_row26_traceSegment_023_0072_0018, g32p_row26_traceSegment_023_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 108 9 9, g32p_row26_traceSegment_023_0108_0009, g32p_row26_traceSegment_023_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 126 9 9, g32p_row26_traceSegment_023_0126_0009, g32p_row26_traceSegment_023_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 108 18 18, g32p_row26_traceSegment_023_0108_0018, g32p_row26_traceSegment_023_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 72 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 72 36 36, g32p_row26_traceSegment_023_0072_0036, g32p_row26_traceSegment_023_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_023 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 0 72 72, g32p_row26_traceSegment_023_0000_0072, g32p_row26_traceSegment_023_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 144 9 9, g32p_row26_traceSegment_023_0144_0009, g32p_row26_traceSegment_023_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 162 9 9, g32p_row26_traceSegment_023_0162_0009, g32p_row26_traceSegment_023_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 144 18 18, g32p_row26_traceSegment_023_0144_0018, g32p_row26_traceSegment_023_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 180 9 9, g32p_row26_traceSegment_023_0180_0009, g32p_row26_traceSegment_023_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 198 9 9, g32p_row26_traceSegment_023_0198_0009, g32p_row26_traceSegment_023_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 180 18 18, g32p_row26_traceSegment_023_0180_0018, g32p_row26_traceSegment_023_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 144 36 36, g32p_row26_traceSegment_023_0144_0036, g32p_row26_traceSegment_023_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 216 9 9, g32p_row26_traceSegment_023_0216_0009, g32p_row26_traceSegment_023_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 234 9 9, g32p_row26_traceSegment_023_0234_0009, g32p_row26_traceSegment_023_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 216 18 18, g32p_row26_traceSegment_023_0216_0018, g32p_row26_traceSegment_023_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 252 9 9, g32p_row26_traceSegment_023_0252_0009, g32p_row26_traceSegment_023_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 270 9 9, g32p_row26_traceSegment_023_0270_0009, g32p_row26_traceSegment_023_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 252 18 18, g32p_row26_traceSegment_023_0252_0018, g32p_row26_traceSegment_023_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 216 36 36, g32p_row26_traceSegment_023_0216_0036, g32p_row26_traceSegment_023_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_023 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 144 72 72, g32p_row26_traceSegment_023_0144_0072, g32p_row26_traceSegment_023_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_023 0 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 0 144 144, g32p_row26_traceSegment_023_0000_0144, g32p_row26_traceSegment_023_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 288 9 9, g32p_row26_traceSegment_023_0288_0009, g32p_row26_traceSegment_023_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 306 9 9, g32p_row26_traceSegment_023_0306_0009, g32p_row26_traceSegment_023_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 288 18 18, g32p_row26_traceSegment_023_0288_0018, g32p_row26_traceSegment_023_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 324 9 9, g32p_row26_traceSegment_023_0324_0009, g32p_row26_traceSegment_023_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 342 9 9, g32p_row26_traceSegment_023_0342_0009, g32p_row26_traceSegment_023_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 324 18 18, g32p_row26_traceSegment_023_0324_0018, g32p_row26_traceSegment_023_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 288 36 36, g32p_row26_traceSegment_023_0288_0036, g32p_row26_traceSegment_023_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 360 9 9, g32p_row26_traceSegment_023_0360_0009, g32p_row26_traceSegment_023_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 378 9 9, g32p_row26_traceSegment_023_0378_0009, g32p_row26_traceSegment_023_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 360 18 18, g32p_row26_traceSegment_023_0360_0018, g32p_row26_traceSegment_023_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 405 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 396 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 396 9 9, g32p_row26_traceSegment_023_0396_0009, g32p_row26_traceSegment_023_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 414 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 414 9 9, g32p_row26_traceSegment_023_0414_0009, g32p_row26_traceSegment_023_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 396 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 396 18 18, g32p_row26_traceSegment_023_0396_0018, g32p_row26_traceSegment_023_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 360 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 360 36 36, g32p_row26_traceSegment_023_0360_0036, g32p_row26_traceSegment_023_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_023 288 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 288 72 72, g32p_row26_traceSegment_023_0288_0072, g32p_row26_traceSegment_023_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 432 9 9, g32p_row26_traceSegment_023_0432_0009, g32p_row26_traceSegment_023_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 450 9 9, g32p_row26_traceSegment_023_0450_0009, g32p_row26_traceSegment_023_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 432 18 18, g32p_row26_traceSegment_023_0432_0018, g32p_row26_traceSegment_023_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 468 9 9, g32p_row26_traceSegment_023_0468_0009, g32p_row26_traceSegment_023_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 486 9 9, g32p_row26_traceSegment_023_0486_0009, g32p_row26_traceSegment_023_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 468 18 18, g32p_row26_traceSegment_023_0468_0018, g32p_row26_traceSegment_023_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 432 36 36, g32p_row26_traceSegment_023_0432_0036, g32p_row26_traceSegment_023_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 504 9 9, g32p_row26_traceSegment_023_0504_0009, g32p_row26_traceSegment_023_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 522 9 9, g32p_row26_traceSegment_023_0522_0009, g32p_row26_traceSegment_023_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 504 18 18, g32p_row26_traceSegment_023_0504_0018, g32p_row26_traceSegment_023_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 540 9 9, g32p_row26_traceSegment_023_0540_0009, g32p_row26_traceSegment_023_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_023 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_023_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_023 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 558 9 9, g32p_row26_traceSegment_023_0558_0009, g32p_row26_traceSegment_023_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_023 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 540 18 18, g32p_row26_traceSegment_023_0540_0018, g32p_row26_traceSegment_023_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_023 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 504 36 36, g32p_row26_traceSegment_023_0504_0036, g32p_row26_traceSegment_023_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_023 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 432 72 72, g32p_row26_traceSegment_023_0432_0072, g32p_row26_traceSegment_023_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_023 288 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 288 144 144, g32p_row26_traceSegment_023_0288_0144, g32p_row26_traceSegment_023_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_023_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_023 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_023 0 288 288, g32p_row26_traceSegment_023_0000_0288, g32p_row26_traceSegment_023_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 23 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_023_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_027 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 27 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_027_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 0 9 9, g32p_row26_traceSegment_027_0000_0009, g32p_row26_traceSegment_027_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 18 9 9, g32p_row26_traceSegment_027_0018_0009, g32p_row26_traceSegment_027_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 0 18 18, g32p_row26_traceSegment_027_0000_0018, g32p_row26_traceSegment_027_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 36 9 9, g32p_row26_traceSegment_027_0036_0009, g32p_row26_traceSegment_027_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 54 9 9, g32p_row26_traceSegment_027_0054_0009, g32p_row26_traceSegment_027_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 36 18 18, g32p_row26_traceSegment_027_0036_0018, g32p_row26_traceSegment_027_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 0 36 36, g32p_row26_traceSegment_027_0000_0036, g32p_row26_traceSegment_027_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 72 9 9, g32p_row26_traceSegment_027_0072_0009, g32p_row26_traceSegment_027_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 90 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 99 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 90 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 90 9 9, g32p_row26_traceSegment_027_0090_0009, g32p_row26_traceSegment_027_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 72 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 72 18 18, g32p_row26_traceSegment_027_0072_0018, g32p_row26_traceSegment_027_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 108 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 108 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 108 9 9, g32p_row26_traceSegment_027_0108_0009, g32p_row26_traceSegment_027_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 126 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 126 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 126 9 9, g32p_row26_traceSegment_027_0126_0009, g32p_row26_traceSegment_027_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 108 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 108 18 18, g32p_row26_traceSegment_027_0108_0018, g32p_row26_traceSegment_027_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 72 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 72 36 36, g32p_row26_traceSegment_027_0072_0036, g32p_row26_traceSegment_027_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_027 0 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 0 72 72, g32p_row26_traceSegment_027_0000_0072, g32p_row26_traceSegment_027_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 144 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 153 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 144 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 144 9 9, g32p_row26_traceSegment_027_0144_0009, g32p_row26_traceSegment_027_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 162 9 9, g32p_row26_traceSegment_027_0162_0009, g32p_row26_traceSegment_027_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 144 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 144 18 18, g32p_row26_traceSegment_027_0144_0018, g32p_row26_traceSegment_027_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 180 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 189 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 180 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 180 9 9, g32p_row26_traceSegment_027_0180_0009, g32p_row26_traceSegment_027_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 198 9 9, g32p_row26_traceSegment_027_0198_0009, g32p_row26_traceSegment_027_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 180 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 180 18 18, g32p_row26_traceSegment_027_0180_0018, g32p_row26_traceSegment_027_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 144 72 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 144 36 36, g32p_row26_traceSegment_027_0144_0036, g32p_row26_traceSegment_027_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 216 9 9, g32p_row26_traceSegment_027_0216_0009, g32p_row26_traceSegment_027_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 234 9 9, g32p_row26_traceSegment_027_0234_0009, g32p_row26_traceSegment_027_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 216 18 18, g32p_row26_traceSegment_027_0216_0018, g32p_row26_traceSegment_027_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 252 9 9, g32p_row26_traceSegment_027_0252_0009, g32p_row26_traceSegment_027_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 270 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 270 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 270 9 9, g32p_row26_traceSegment_027_0270_0009, g32p_row26_traceSegment_027_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 252 18 18, g32p_row26_traceSegment_027_0252_0018, g32p_row26_traceSegment_027_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 216 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 216 36 36, g32p_row26_traceSegment_027_0216_0036, g32p_row26_traceSegment_027_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_027 144 144 = [4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 144 72 72, g32p_row26_traceSegment_027_0144_0072, g32p_row26_traceSegment_027_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_027 0 288 = [4, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 0 144 144, g32p_row26_traceSegment_027_0000_0144, g32p_row26_traceSegment_027_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 288 9 9, g32p_row26_traceSegment_027_0288_0009, g32p_row26_traceSegment_027_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 306 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 306 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 306 9 9, g32p_row26_traceSegment_027_0306_0009, g32p_row26_traceSegment_027_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 288 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 288 18 18, g32p_row26_traceSegment_027_0288_0018, g32p_row26_traceSegment_027_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 333 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 324 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 324 9 9, g32p_row26_traceSegment_027_0324_0009, g32p_row26_traceSegment_027_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 351 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 342 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 342 9 9, g32p_row26_traceSegment_027_0342_0009, g32p_row26_traceSegment_027_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 324 36 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 324 18 18, g32p_row26_traceSegment_027_0324_0018, g32p_row26_traceSegment_027_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 288 72 = [3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 288 36 36, g32p_row26_traceSegment_027_0288_0036, g32p_row26_traceSegment_027_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 360 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 360 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 360 9 9, g32p_row26_traceSegment_027_0360_0009, g32p_row26_traceSegment_027_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 387 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 378 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 378 9 9, g32p_row26_traceSegment_027_0378_0009, g32p_row26_traceSegment_027_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 360 36 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 360 18 18, g32p_row26_traceSegment_027_0360_0018, g32p_row26_traceSegment_027_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 396 9 9, g32p_row26_traceSegment_027_0396_0009, g32p_row26_traceSegment_027_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 414 9 9, g32p_row26_traceSegment_027_0414_0009, g32p_row26_traceSegment_027_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 396 18 18, g32p_row26_traceSegment_027_0396_0018, g32p_row26_traceSegment_027_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 360 72 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 360 36 36, g32p_row26_traceSegment_027_0360_0036, g32p_row26_traceSegment_027_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_027 288 144 = [4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 288 72 72, g32p_row26_traceSegment_027_0288_0072, g32p_row26_traceSegment_027_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 432 9 9, g32p_row26_traceSegment_027_0432_0009, g32p_row26_traceSegment_027_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 450 9 9, g32p_row26_traceSegment_027_0450_0009, g32p_row26_traceSegment_027_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 432 18 18, g32p_row26_traceSegment_027_0432_0018, g32p_row26_traceSegment_027_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 468 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 468 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 468 9 9, g32p_row26_traceSegment_027_0468_0009, g32p_row26_traceSegment_027_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 486 9 9, g32p_row26_traceSegment_027_0486_0009, g32p_row26_traceSegment_027_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 468 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 468 18 18, g32p_row26_traceSegment_027_0468_0018, g32p_row26_traceSegment_027_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 432 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 432 36 36, g32p_row26_traceSegment_027_0432_0036, g32p_row26_traceSegment_027_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 504 9 9, g32p_row26_traceSegment_027_0504_0009, g32p_row26_traceSegment_027_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 531 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 522 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 522 9 9, g32p_row26_traceSegment_027_0522_0009, g32p_row26_traceSegment_027_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 504 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 504 18 18, g32p_row26_traceSegment_027_0504_0018, g32p_row26_traceSegment_027_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 540 9 9, g32p_row26_traceSegment_027_0540_0009, g32p_row26_traceSegment_027_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_027 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_027_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_027 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 558 9 9, g32p_row26_traceSegment_027_0558_0009, g32p_row26_traceSegment_027_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_027 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 540 18 18, g32p_row26_traceSegment_027_0540_0018, g32p_row26_traceSegment_027_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_027 504 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 504 36 36, g32p_row26_traceSegment_027_0504_0036, g32p_row26_traceSegment_027_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_027 432 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 432 72 72, g32p_row26_traceSegment_027_0432_0072, g32p_row26_traceSegment_027_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_027 288 288 = [4, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 288 144 144, g32p_row26_traceSegment_027_0288_0144, g32p_row26_traceSegment_027_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_027_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_027 0 576 = [8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_027 0 288 288, g32p_row26_traceSegment_027_0000_0288, g32p_row26_traceSegment_027_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 27 = [8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_027_0000_0576

end HodgeLean.Foundations.Program

end
end
