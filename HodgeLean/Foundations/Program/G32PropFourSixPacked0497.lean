import HodgeLean.Foundations.Program.G32PropFourSixPacked0495
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0496
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0362
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0003

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row13_characterValues (g32p_finBlockIndex 24 0 r))⁻¹).val =
      g32p_row13_restrictionExponents (g32p_row13_restrictionBucket (g32p_finBlockIndex 24 0 r)) := by
  decide +kernel

theorem g32p_row13_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row13_characterValues (g32p_finBlockIndex 24 1 r))⁻¹).val =
      g32p_row13_restrictionExponents (g32p_row13_restrictionBucket (g32p_finBlockIndex 24 1 r)) := by
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

theorem g32p_row13_restrictionCounts (a : Fin 24) :
    (Finset.univ.filter (fun i => g32p_row13_restrictionBucket i = a)).card = g32p_row13_restrictionSizes a := by
  fin_cases a
  · exact g32p_row13_restrictionCount_0
  · exact g32p_row13_restrictionCount_1
  · exact g32p_row13_restrictionCount_2
  · exact g32p_row13_restrictionCount_3
  · exact g32p_row13_restrictionCount_4
  · exact g32p_row13_restrictionCount_5
  · exact g32p_row13_restrictionCount_6
  · exact g32p_row13_restrictionCount_7
  · exact g32p_row13_restrictionCount_8
  · exact g32p_row13_restrictionCount_9
  · exact g32p_row13_restrictionCount_10
  · exact g32p_row13_restrictionCount_11
  · exact g32p_row13_restrictionCount_12
  · exact g32p_row13_restrictionCount_13
  · exact g32p_row13_restrictionCount_14
  · exact g32p_row13_restrictionCount_15
  · exact g32p_row13_restrictionCount_16
  · exact g32p_row13_restrictionCount_17
  · exact g32p_row13_restrictionCount_18
  · exact g32p_row13_restrictionCount_19
  · exact g32p_row13_restrictionCount_20
  · exact g32p_row13_restrictionCount_21
  · exact g32p_row13_restrictionCount_22
  · exact g32p_row13_restrictionCount_23

theorem g32p_row13_restrictionExponent (i : Fin 24) :
    (Multiplicative.toAdd (g32p_row13_characterValues i)⁻¹).val =
      g32p_row13_restrictionExponents (g32p_row13_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row13_restrictionExponent_0
  · exact g32p_row13_restrictionExponent_1

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row13_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 24),
      g32p_restrictionTrace τ τbar θ j (g32p_row13_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row13_restrictionCoefficients j (g32p_row13_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 13 ∧
      papersA τ τbar θ g32p_row13_finiteSupplier.H (g32p_complexCharacter g32p_row13_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row13_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row13_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row13_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 12 ^ (12 / 3)) x.2.1 *
          g32p_root 12 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row13_finiteSupplier
      g32p_row13_groupEquiv g32p_row13_characterValues g32p_row13_finiteSupplier_value
      g32p_row13_restrictionBucket g32p_row13_restrictionSizes g32p_row13_restrictionExponents
      g32p_row13_restrictionCounts g32p_row13_restrictionExponent
      τ τbar θ g32p_row13_pairingTerms g32p_row13_restrictionCoefficients
      g32p_row13_restrictionLabels (g32p_restriction_root_omega 12 (by decide)) htrace
      g32p_row13_restrictionDecode g32p_row13_restrictionTerms j
  apply g32p_row13_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row13_finiteSupplier)
    (g32p_root 12) (g32p_root_primitive g32p_row13_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row13_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row13_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row13_groupEquiv i) =
      g32p_row13_restrictionClasses (g32p_row13_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 13 ∧
      papersA τ τbar θ g32p_row13_finiteSupplier.H
        (g32p_complexCharacter g32p_row13_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row13_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row13_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row13_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 13 ∧ r.m = g32p_row13_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row13_finiteSupplier.H ∧
      (g32p_exponents g32p_row13_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 24),
      g32p_restrictionTrace τ τbar θ j (g32p_row13_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row13_restrictionCoefficients j (g32p_row13_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 13 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 13 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row13_finiteSupplier, g32p_complexCharacter g32p_row13_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row13_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row13_supplierClassifier (g32p_finBlockIndex 24 0 r) =
      g32p_row13_restrictionClasses (g32p_row13_restrictionBucket (g32p_finBlockIndex 24 0 r)) := by
  decide +kernel

theorem g32p_row13_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row13_supplierClassifier (g32p_finBlockIndex 24 1 r) =
      g32p_row13_restrictionClasses (g32p_row13_restrictionBucket (g32p_finBlockIndex 24 1 r)) := by
  decide +kernel

theorem g32p_row13_integrationClasses (i : Fin 24) :
    g32p_integrationLabel (g32p_row13_groupEquiv i) =
      g32p_row13_restrictionClasses (g32p_row13_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row13_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row13_supplierClassifier i =
    g32p_row13_restrictionClasses (g32p_row13_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row13_integrationClasses_000 r
  · exact g32p_row13_integrationClasses_001 r

theorem g32p_row13_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 13 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 12).H
        (g32p_recordedSupplierCharacters 12) = g32SparseVec v.coords := by
  exact g32p_row13_restriction_from_family g32p_integrationLabel g32p_row13_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row13_integrationRestriction

theorem g32p_row13_integrationNode (j : Fin 48) (i : Fin 24) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row13_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row13_restrictionCoefficients j (g32p_row13_restrictionBucket i)) := by
  rw [g32p_row13_integrationClasses, g32p_row13_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row14_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row14_terms_0, g32p_row14_terms_1, g32p_row14_terms_2, g32p_row14_terms_3, g32p_row14_terms_4, g32p_row14_terms_5, g32p_row14_terms_6, g32p_row14_terms_7, g32p_row14_terms_8, g32p_row14_terms_9, g32p_row14_terms_10, g32p_row14_terms_11, g32p_row14_terms_12, g32p_row14_terms_13, g32p_row14_terms_14, g32p_row14_terms_15, g32p_row14_terms_16, g32p_row14_terms_17, g32p_row14_terms_18, g32p_row14_terms_19, g32p_row14_terms_20, g32p_row14_terms_21, g32p_row14_terms_22, g32p_row14_terms_23, g32p_row14_terms_24, g32p_row14_terms_25, g32p_row14_terms_26, g32p_row14_terms_27, g32p_row14_terms_28, g32p_row14_terms_29, g32p_row14_terms_30, g32p_row14_terms_31, g32p_row14_terms_32, g32p_row14_terms_33, g32p_row14_terms_34, g32p_row14_terms_35, g32p_row14_terms_36, g32p_row14_terms_37, g32p_row14_terms_38, g32p_row14_terms_39, g32p_row14_terms_40, g32p_row14_terms_41, g32p_row14_terms_42, g32p_row14_terms_43, g32p_row14_terms_44, g32p_row14_terms_45, g32p_row14_terms_46, g32p_row14_terms_47]

def g32p_row14_pairingQuotients : Fin 48 → List ℤ :=
  ![[0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4], [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8], [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8], [], [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4], [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4], [], [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4], [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4], [], [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4], [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4], [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16], [], [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8], [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8], [-24, 0, -28, 0, -8, 0, 12, 0, 16, 0, 8], [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16], [], [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16], [], [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16], [0, -2, 10, -2, 0, -2, 10, -2, 0, 4, -20, 4], [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4], [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16], [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4], [72, 0, 84, 0, 24, 0, -36, 0, -48, 0, -24], [72, 0, 84, 0, 24, 0, -36, 0, -48, 0, -24], [], [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16], [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16], [], [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4], [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4], [], [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16], [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8], [], [-24, 0, -28, 0, -8, 0, 12, 0, 16, 0, 8], [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16], [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16], [48, 0, 56, 0, 16, 0, -24, 0, -32, 0, -16], [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16], [], [-28, 0, -24, 0, 0, 0, 4], [-60, 0, -60], [-80, 0, -72, 0, 0, 0, 8], [-64, 0, -72, 0, 0, 0, -8]]

def g32p_row14_freeCoordinates : Fin 44 → ℤ :=
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1, 0, 0, -2, 2, 0]

def g32p_row14_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![2, 5, 6, 6]

theorem g32p_row14_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 24 (g32p_row14_freeCoordinates j)
      (g32p_pairingCoefficients 12 (g32p_row14_pairingTerms ⟨j.val, by omega⟩))
      [1, 0, -1, 0, 1] (g32p_row14_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row14_pairing_0
  · exact g32p_row14_pairing_1
  · exact g32p_row14_pairing_2
  · exact g32p_row14_pairing_3
  · exact g32p_row14_pairing_4
  · exact g32p_row14_pairing_5
  · exact g32p_row14_pairing_6
  · exact g32p_row14_pairing_7
  · exact g32p_row14_pairing_8
  · exact g32p_row14_pairing_9
  · exact g32p_row14_pairing_10
  · exact g32p_row14_pairing_11
  · exact g32p_row14_pairing_12
  · exact g32p_row14_pairing_13
  · exact g32p_row14_pairing_14
  · exact g32p_row14_pairing_15
  · exact g32p_row14_pairing_16
  · exact g32p_row14_pairing_17
  · exact g32p_row14_pairing_18
  · exact g32p_row14_pairing_19
  · exact g32p_row14_pairing_20
  · exact g32p_row14_pairing_21
  · exact g32p_row14_pairing_22
  · exact g32p_row14_pairing_23
  · exact g32p_row14_pairing_24
  · exact g32p_row14_pairing_25
  · exact g32p_row14_pairing_26
  · exact g32p_row14_pairing_27
  · exact g32p_row14_pairing_28
  · exact g32p_row14_pairing_29
  · exact g32p_row14_pairing_30
  · exact g32p_row14_pairing_31
  · exact g32p_row14_pairing_32
  · exact g32p_row14_pairing_33
  · exact g32p_row14_pairing_34
  · exact g32p_row14_pairing_35
  · exact g32p_row14_pairing_36
  · exact g32p_row14_pairing_37
  · exact g32p_row14_pairing_38
  · exact g32p_row14_pairing_39
  · exact g32p_row14_pairing_40
  · exact g32p_row14_pairing_41
  · exact g32p_row14_pairing_42
  · exact g32p_row14_pairing_43

theorem g32p_row14_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 24 (g32p_row14_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 12 (g32p_row14_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, 0, -1, 0, 1] (g32p_row14_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row14_pairing_44
  · exact g32p_row14_pairing_45
  · exact g32p_row14_pairing_46
  · exact g32p_row14_pairing_47

theorem g32p_row14_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 12) (horder : Fintype.card H = 24)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row14_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (12 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row14_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (12 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 14 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row14_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 12
    g32p_row14_freeCoordinates g32p_row14_quaternionicMultiplicities
    g32p_row14_pairingTerms [1, 0, -1, 0, 1] g32p_row14_pairingQuotients z
    (g32p_pairing_modulus_twelve hz) hfree hquat
    (by rw [horder]; exact g32p_row14_pairingFree)
    (by rw [horder]; exact g32p_row14_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
