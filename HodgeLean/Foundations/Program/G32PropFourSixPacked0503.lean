import HodgeLean.Foundations.Program.G32PropFourSixPacked0501
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0502
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0365
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0004

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row15_restrictionCount_24 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 24)).card = g32p_row15_restrictionSizes 24 := by
  decide +kernel

theorem g32p_row15_restrictionCount_25 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 25)).card = g32p_row15_restrictionSizes 25 := by
  decide +kernel

theorem g32p_row15_restrictionCount_26 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 26)).card = g32p_row15_restrictionSizes 26 := by
  decide +kernel

theorem g32p_row15_restrictionCount_27 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 27)).card = g32p_row15_restrictionSizes 27 := by
  decide +kernel

theorem g32p_row15_restrictionCount_28 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 28)).card = g32p_row15_restrictionSizes 28 := by
  decide +kernel

theorem g32p_row15_restrictionCount_29 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 29)).card = g32p_row15_restrictionSizes 29 := by
  decide +kernel

theorem g32p_row15_restrictionCount_30 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 30)).card = g32p_row15_restrictionSizes 30 := by
  decide +kernel

theorem g32p_row15_restrictionCount_31 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 31)).card = g32p_row15_restrictionSizes 31 := by
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

theorem g32p_row15_restrictionCount_32 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 32)).card = g32p_row15_restrictionSizes 32 := by
  decide +kernel

theorem g32p_row15_restrictionCount_33 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 33)).card = g32p_row15_restrictionSizes 33 := by
  decide +kernel

theorem g32p_row15_restrictionCount_34 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 34)).card = g32p_row15_restrictionSizes 34 := by
  decide +kernel

theorem g32p_row15_restrictionCount_35 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 35)).card = g32p_row15_restrictionSizes 35 := by
  decide +kernel

theorem g32p_row15_restrictionCount_36 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 36)).card = g32p_row15_restrictionSizes 36 := by
  decide +kernel

theorem g32p_row15_restrictionCount_37 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 37)).card = g32p_row15_restrictionSizes 37 := by
  decide +kernel

theorem g32p_row15_restrictionCount_38 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 38)).card = g32p_row15_restrictionSizes 38 := by
  decide +kernel

theorem g32p_row15_restrictionCount_39 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 39)).card = g32p_row15_restrictionSizes 39 := by
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

theorem g32p_row15_restrictionCount_40 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 40)).card = g32p_row15_restrictionSizes 40 := by
  decide +kernel

theorem g32p_row15_restrictionCount_41 :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = 41)).card = g32p_row15_restrictionSizes 41 := by
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

theorem g32p_row15_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row15_characterValues (g32p_finBlockIndex 96 0 r))⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 0 r)) := by
  decide +kernel

theorem g32p_row15_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row15_characterValues (g32p_finBlockIndex 96 1 r))⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 1 r)) := by
  decide +kernel

theorem g32p_row15_restrictionExponent_2 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row15_characterValues (g32p_finBlockIndex 96 2 r))⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 2 r)) := by
  decide +kernel

theorem g32p_row15_restrictionExponent_3 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row15_characterValues (g32p_finBlockIndex 96 3 r))⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 3 r)) := by
  decide +kernel

theorem g32p_row15_restrictionExponent_4 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row15_characterValues (g32p_finBlockIndex 96 4 r))⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 4 r)) := by
  decide +kernel

theorem g32p_row15_restrictionExponent_5 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row15_characterValues (g32p_finBlockIndex 96 5 r))⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 5 r)) := by
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

theorem g32p_row15_restrictionCounts (a : Fin 42) :
    (Finset.univ.filter (fun i => g32p_row15_restrictionBucket i = a)).card = g32p_row15_restrictionSizes a := by
  fin_cases a
  · exact g32p_row15_restrictionCount_0
  · exact g32p_row15_restrictionCount_1
  · exact g32p_row15_restrictionCount_2
  · exact g32p_row15_restrictionCount_3
  · exact g32p_row15_restrictionCount_4
  · exact g32p_row15_restrictionCount_5
  · exact g32p_row15_restrictionCount_6
  · exact g32p_row15_restrictionCount_7
  · exact g32p_row15_restrictionCount_8
  · exact g32p_row15_restrictionCount_9
  · exact g32p_row15_restrictionCount_10
  · exact g32p_row15_restrictionCount_11
  · exact g32p_row15_restrictionCount_12
  · exact g32p_row15_restrictionCount_13
  · exact g32p_row15_restrictionCount_14
  · exact g32p_row15_restrictionCount_15
  · exact g32p_row15_restrictionCount_16
  · exact g32p_row15_restrictionCount_17
  · exact g32p_row15_restrictionCount_18
  · exact g32p_row15_restrictionCount_19
  · exact g32p_row15_restrictionCount_20
  · exact g32p_row15_restrictionCount_21
  · exact g32p_row15_restrictionCount_22
  · exact g32p_row15_restrictionCount_23
  · exact g32p_row15_restrictionCount_24
  · exact g32p_row15_restrictionCount_25
  · exact g32p_row15_restrictionCount_26
  · exact g32p_row15_restrictionCount_27
  · exact g32p_row15_restrictionCount_28
  · exact g32p_row15_restrictionCount_29
  · exact g32p_row15_restrictionCount_30
  · exact g32p_row15_restrictionCount_31
  · exact g32p_row15_restrictionCount_32
  · exact g32p_row15_restrictionCount_33
  · exact g32p_row15_restrictionCount_34
  · exact g32p_row15_restrictionCount_35
  · exact g32p_row15_restrictionCount_36
  · exact g32p_row15_restrictionCount_37
  · exact g32p_row15_restrictionCount_38
  · exact g32p_row15_restrictionCount_39
  · exact g32p_row15_restrictionCount_40
  · exact g32p_row15_restrictionCount_41

theorem g32p_row15_restrictionExponent (i : Fin 96) :
    (Multiplicative.toAdd (g32p_row15_characterValues i)⁻¹).val =
      g32p_row15_restrictionExponents (g32p_row15_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row15_restrictionExponent_0
  · exact g32p_row15_restrictionExponent_1
  · exact g32p_row15_restrictionExponent_2
  · exact g32p_row15_restrictionExponent_3
  · exact g32p_row15_restrictionExponent_4
  · exact g32p_row15_restrictionExponent_5

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row15_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 96),
      g32p_restrictionTrace τ τbar θ j (g32p_row15_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row15_restrictionCoefficients j (g32p_row15_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 15 ∧
      papersA τ τbar θ g32p_row15_finiteSupplier.H (g32p_complexCharacter g32p_row15_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row15_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row15_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row15_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 12 ^ (12 / 3)) x.2.1 *
          g32p_root 12 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row15_finiteSupplier
      g32p_row15_groupEquiv g32p_row15_characterValues g32p_row15_finiteSupplier_value
      g32p_row15_restrictionBucket g32p_row15_restrictionSizes g32p_row15_restrictionExponents
      g32p_row15_restrictionCounts g32p_row15_restrictionExponent
      τ τbar θ g32p_row15_pairingTerms g32p_row15_restrictionCoefficients
      g32p_row15_restrictionLabels (g32p_restriction_root_omega 12 (by decide)) htrace
      g32p_row15_restrictionDecode g32p_row15_restrictionTerms j
  apply g32p_row15_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row15_finiteSupplier)
    (g32p_root 12) (g32p_root_primitive g32p_row15_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row15_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row15_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row15_groupEquiv i) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 15 ∧
      papersA τ τbar θ g32p_row15_finiteSupplier.H
        (g32p_complexCharacter g32p_row15_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row15_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row15_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row15_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 15 ∧ r.m = g32p_row15_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row15_finiteSupplier.H ∧
      (g32p_exponents g32p_row15_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 96),
      g32p_restrictionTrace τ τbar θ j (g32p_row15_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row15_restrictionCoefficients j (g32p_row15_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 15 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 15 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row15_finiteSupplier, g32p_complexCharacter g32p_row15_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row15_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row15_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row15_supplierClassifier (g32p_finBlockIndex 96 0 r) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 0 r)) := by
  decide +kernel

theorem g32p_row15_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row15_supplierClassifier (g32p_finBlockIndex 96 1 r) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 1 r)) := by
  decide +kernel

theorem g32p_row15_integrationClasses_002 : ∀ r : Fin 16,
    g32p_row15_supplierClassifier (g32p_finBlockIndex 96 2 r) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 2 r)) := by
  decide +kernel

theorem g32p_row15_integrationClasses_003 : ∀ r : Fin 16,
    g32p_row15_supplierClassifier (g32p_finBlockIndex 96 3 r) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 3 r)) := by
  decide +kernel

theorem g32p_row15_integrationClasses_004 : ∀ r : Fin 16,
    g32p_row15_supplierClassifier (g32p_finBlockIndex 96 4 r) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 4 r)) := by
  decide +kernel

theorem g32p_row15_integrationClasses_005 : ∀ r : Fin 16,
    g32p_row15_supplierClassifier (g32p_finBlockIndex 96 5 r) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket (g32p_finBlockIndex 96 5 r)) := by
  decide +kernel

theorem g32p_row15_integrationClasses (i : Fin 96) :
    g32p_integrationLabel (g32p_row15_groupEquiv i) =
      g32p_row15_restrictionClasses (g32p_row15_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row15_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row15_supplierClassifier i =
    g32p_row15_restrictionClasses (g32p_row15_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row15_integrationClasses_000 r
  · exact g32p_row15_integrationClasses_001 r
  · exact g32p_row15_integrationClasses_002 r
  · exact g32p_row15_integrationClasses_003 r
  · exact g32p_row15_integrationClasses_004 r
  · exact g32p_row15_integrationClasses_005 r

theorem g32p_row15_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 15 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 14).H
        (g32p_recordedSupplierCharacters 14) = g32SparseVec v.coords := by
  exact g32p_row15_restriction_from_family g32p_integrationLabel g32p_row15_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row15_integrationRestriction

theorem g32p_row15_integrationNode (j : Fin 48) (i : Fin 96) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row15_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row15_restrictionCoefficients j (g32p_row15_restrictionBucket i)) := by
  rw [g32p_row15_integrationClasses, g32p_row15_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row16_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row16_terms_0, g32p_row16_terms_1, g32p_row16_terms_2, g32p_row16_terms_3, g32p_row16_terms_4, g32p_row16_terms_5, g32p_row16_terms_6, g32p_row16_terms_7, g32p_row16_terms_8, g32p_row16_terms_9, g32p_row16_terms_10, g32p_row16_terms_11, g32p_row16_terms_12, g32p_row16_terms_13, g32p_row16_terms_14, g32p_row16_terms_15, g32p_row16_terms_16, g32p_row16_terms_17, g32p_row16_terms_18, g32p_row16_terms_19, g32p_row16_terms_20, g32p_row16_terms_21, g32p_row16_terms_22, g32p_row16_terms_23, g32p_row16_terms_24, g32p_row16_terms_25, g32p_row16_terms_26, g32p_row16_terms_27, g32p_row16_terms_28, g32p_row16_terms_29, g32p_row16_terms_30, g32p_row16_terms_31, g32p_row16_terms_32, g32p_row16_terms_33, g32p_row16_terms_34, g32p_row16_terms_35, g32p_row16_terms_36, g32p_row16_terms_37, g32p_row16_terms_38, g32p_row16_terms_39, g32p_row16_terms_40, g32p_row16_terms_41, g32p_row16_terms_42, g32p_row16_terms_43, g32p_row16_terms_44, g32p_row16_terms_45, g32p_row16_terms_46, g32p_row16_terms_47]

def g32p_row16_pairingQuotients : Fin 48 → List ℤ :=
  ![[0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2], [], [-15, -16, -15, 0, 0, 10, 9, 10, 0, 0, 0, 2], [-15, -16, -15, 0, 0, 10, 9, 10, 0, 0, 0, 2], [], [-15, -15, -15, 0, 0, 10, 10, 10], [-15, -15, -15, 0, 0, 10, 10, 10], [-15, -14, -15, 0, 0, 10, 11, 10, 0, 0, 0, -2], [], [-30, -30, -30, 0, 0, 20, 20, 20], [-30, -30, -30, 0, 0, 20, 20, 20], [-45, -45, -45, 0, 0, 30, 30, 30], [-45, -45, -45, 0, 0, 30, 30, 30], [], [], [-60, -60, -60, 0, 0, 40, 40, 40], [-60, -60, -60, 0, 0, 40, 40, 40], [-60, -60, -60, 0, 0, 40, 40, 40], [-60, -60, -60, 0, 0, 40, 40, 40], [-60, -60, -60, 0, 0, 40, 40, 40], [-60, -60, -60, 0, 0, 40, 40, 40], [-75, -76, -75, 0, 0, 50, 49, 50, 0, 0, 0, 2], [], [-90, -90, -90, 0, 0, 60, 60, 60], [-90, -90, -90, 0, 0, 60, 60, 60], [-90, -90, -90, 0, 0, 60, 60, 60], [], [-105, -104, -105, 0, 0, 70, 71, 70, 0, 0, 0, -2], [-105, -104, -105, 0, 0, 70, 71, 70, 0, 0, 0, -2], [], [-120, -120, -120, 0, 0, 80, 80, 80], [-120, -120, -120, 0, 0, 80, 80, 80], [], [-135, -135, -135, 0, 0, 90, 90, 90], [-135, -135, -135, 0, 0, 90, 90, 90], [], [-180, -180, -180, 0, 0, 120, 120, 120], [-180, -180, -180, 0, 0, 120, 120, 120], [-180, -180, -180, 0, 0, 120, 120, 120], [-180, -180, -180, 0, 0, 120, 120, 120], [-195, -196, -195, 0, 0, 130, 129, 130, 0, 0, 0, 2], [-195, -196, -195, 0, 0, 130, 129, 130, 0, 0, 0, 2], [-240, -240, -240, 0, 0, 160, 160, 160], [-240, -239, -240, 0, 0, 160, 161, 160, 0, 0, 0, -2], [20, 20, 20], [60, 60, 60], [64, 63, 62, -3, -3, -2, -1], [80, 80, 80]]

def g32p_row16_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 3, 3, 0, 0, 4, 4, 4, 4, 4, 4, 5, 0, 6, 6, 6, 0, 7, 7, 0, 8, 8, 0, 9, 9, 0, 12, 12, 12, 12, 13, 13, 16, 16]

def g32p_row16_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row16_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 15 (g32p_row16_freeCoordinates j)
      (g32p_pairingCoefficients 15 (g32p_row16_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 0, 1, -1, 1, 0, -1, 1] (g32p_row16_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row16_pairing_0
  · exact g32p_row16_pairing_1
  · exact g32p_row16_pairing_2
  · exact g32p_row16_pairing_3
  · exact g32p_row16_pairing_4
  · exact g32p_row16_pairing_5
  · exact g32p_row16_pairing_6
  · exact g32p_row16_pairing_7
  · exact g32p_row16_pairing_8
  · exact g32p_row16_pairing_9
  · exact g32p_row16_pairing_10
  · exact g32p_row16_pairing_11
  · exact g32p_row16_pairing_12
  · exact g32p_row16_pairing_13
  · exact g32p_row16_pairing_14
  · exact g32p_row16_pairing_15
  · exact g32p_row16_pairing_16
  · exact g32p_row16_pairing_17
  · exact g32p_row16_pairing_18
  · exact g32p_row16_pairing_19
  · exact g32p_row16_pairing_20
  · exact g32p_row16_pairing_21
  · exact g32p_row16_pairing_22
  · exact g32p_row16_pairing_23
  · exact g32p_row16_pairing_24
  · exact g32p_row16_pairing_25
  · exact g32p_row16_pairing_26
  · exact g32p_row16_pairing_27
  · exact g32p_row16_pairing_28
  · exact g32p_row16_pairing_29
  · exact g32p_row16_pairing_30
  · exact g32p_row16_pairing_31
  · exact g32p_row16_pairing_32
  · exact g32p_row16_pairing_33
  · exact g32p_row16_pairing_34
  · exact g32p_row16_pairing_35
  · exact g32p_row16_pairing_36
  · exact g32p_row16_pairing_37
  · exact g32p_row16_pairing_38
  · exact g32p_row16_pairing_39
  · exact g32p_row16_pairing_40
  · exact g32p_row16_pairing_41
  · exact g32p_row16_pairing_42
  · exact g32p_row16_pairing_43

theorem g32p_row16_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 15 (g32p_row16_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 15 (g32p_row16_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 0, 1, -1, 1, 0, -1, 1] (g32p_row16_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row16_pairing_44
  · exact g32p_row16_pairing_45
  · exact g32p_row16_pairing_46
  · exact g32p_row16_pairing_47

theorem g32p_row16_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 15) (horder : Fintype.card H = 15)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row16_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (15 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row16_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (15 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 16 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row16_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 15
    g32p_row16_freeCoordinates g32p_row16_quaternionicMultiplicities
    g32p_row16_pairingTerms [1, -1, 0, 1, -1, 1, 0, -1, 1] g32p_row16_pairingQuotients z
    (g32p_pairing_modulus_fifteen hz) hfree hquat
    (by rw [horder]; exact g32p_row16_pairingFree)
    (by rw [horder]; exact g32p_row16_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
