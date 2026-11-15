import HodgeLean.Foundations.Program.G32PropFourSixPacked0505
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0366
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

theorem g32p_row16_restrictionCounts (a : Fin 15) :
    (Finset.univ.filter (fun i => g32p_row16_restrictionBucket i = a)).card = g32p_row16_restrictionSizes a := by
  fin_cases a
  · exact g32p_row16_restrictionCount_0
  · exact g32p_row16_restrictionCount_1
  · exact g32p_row16_restrictionCount_2
  · exact g32p_row16_restrictionCount_3
  · exact g32p_row16_restrictionCount_4
  · exact g32p_row16_restrictionCount_5
  · exact g32p_row16_restrictionCount_6
  · exact g32p_row16_restrictionCount_7
  · exact g32p_row16_restrictionCount_8
  · exact g32p_row16_restrictionCount_9
  · exact g32p_row16_restrictionCount_10
  · exact g32p_row16_restrictionCount_11
  · exact g32p_row16_restrictionCount_12
  · exact g32p_row16_restrictionCount_13
  · exact g32p_row16_restrictionCount_14

theorem g32p_row16_restrictionExponent (i : Fin 15) :
    (Multiplicative.toAdd (g32p_row16_characterValues i)⁻¹).val =
      g32p_row16_restrictionExponents (g32p_row16_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row16_restrictionExponent_0

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row16_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 15),
      g32p_restrictionTrace τ τbar θ j (g32p_row16_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row16_restrictionCoefficients j (g32p_row16_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 16 ∧
      papersA τ τbar θ g32p_row16_finiteSupplier.H (g32p_complexCharacter g32p_row16_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row16_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row16_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row16_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 15 ^ (15 / 3)) x.2.1 *
          g32p_root 15 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row16_finiteSupplier
      g32p_row16_groupEquiv g32p_row16_characterValues g32p_row16_finiteSupplier_value
      g32p_row16_restrictionBucket g32p_row16_restrictionSizes g32p_row16_restrictionExponents
      g32p_row16_restrictionCounts g32p_row16_restrictionExponent
      τ τbar θ g32p_row16_pairingTerms g32p_row16_restrictionCoefficients
      g32p_row16_restrictionLabels (g32p_restriction_root_omega 15 (by decide)) htrace
      g32p_row16_restrictionDecode g32p_row16_restrictionTerms j
  apply g32p_row16_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row16_finiteSupplier)
    (g32p_root 15) (g32p_root_primitive g32p_row16_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row16_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row16_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row16_groupEquiv i) =
      g32p_row16_restrictionClasses (g32p_row16_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 16 ∧
      papersA τ τbar θ g32p_row16_finiteSupplier.H
        (g32p_complexCharacter g32p_row16_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row16_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row16_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row16_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 16 ∧ r.m = g32p_row16_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row16_finiteSupplier.H ∧
      (g32p_exponents g32p_row16_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 15),
      g32p_restrictionTrace τ τbar θ j (g32p_row16_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row16_restrictionCoefficients j (g32p_row16_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 16 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 16 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row16_finiteSupplier, g32p_complexCharacter g32p_row16_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row16_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row16_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row16_supplierClassifier (g32p_finBlockIndex 15 0 r) =
      g32p_row16_restrictionClasses (g32p_row16_restrictionBucket (g32p_finBlockIndex 15 0 r)) := by
  decide +kernel

theorem g32p_row16_integrationClasses (i : Fin 15) :
    g32p_integrationLabel (g32p_row16_groupEquiv i) =
      g32p_row16_restrictionClasses (g32p_row16_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row16_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row16_supplierClassifier i =
    g32p_row16_restrictionClasses (g32p_row16_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row16_integrationClasses_000 r

theorem g32p_row16_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 16 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 15).H
        (g32p_recordedSupplierCharacters 15) = g32SparseVec v.coords := by
  exact g32p_row16_restriction_from_family g32p_integrationLabel g32p_row16_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row16_integrationRestriction

theorem g32p_row16_integrationNode (j : Fin 48) (i : Fin 15) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row16_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row16_restrictionCoefficients j (g32p_row16_restrictionBucket i)) := by
  rw [g32p_row16_integrationClasses, g32p_row16_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row17_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row17_terms_0, g32p_row17_terms_1, g32p_row17_terms_2, g32p_row17_terms_3, g32p_row17_terms_4, g32p_row17_terms_5, g32p_row17_terms_6, g32p_row17_terms_7, g32p_row17_terms_8, g32p_row17_terms_9, g32p_row17_terms_10, g32p_row17_terms_11, g32p_row17_terms_12, g32p_row17_terms_13, g32p_row17_terms_14, g32p_row17_terms_15, g32p_row17_terms_16, g32p_row17_terms_17, g32p_row17_terms_18, g32p_row17_terms_19, g32p_row17_terms_20, g32p_row17_terms_21, g32p_row17_terms_22, g32p_row17_terms_23, g32p_row17_terms_24, g32p_row17_terms_25, g32p_row17_terms_26, g32p_row17_terms_27, g32p_row17_terms_28, g32p_row17_terms_29, g32p_row17_terms_30, g32p_row17_terms_31, g32p_row17_terms_32, g32p_row17_terms_33, g32p_row17_terms_34, g32p_row17_terms_35, g32p_row17_terms_36, g32p_row17_terms_37, g32p_row17_terms_38, g32p_row17_terms_39, g32p_row17_terms_40, g32p_row17_terms_41, g32p_row17_terms_42, g32p_row17_terms_43, g32p_row17_terms_44, g32p_row17_terms_45, g32p_row17_terms_46, g32p_row17_terms_47]

def g32p_row17_pairingQuotients : Fin 48 → List ℤ :=
  ![[0, 216, 0, 216, 0, -432], [], [], [], [], [], [], [], [], [], [], [0, 216, 0, 216, 0, -432], [-1296, -1512, -432, 648, 864, 432], [], [], [], [], [], [], [], [0, 216, 0, 216, 0, -432], [-1296, -1296, -432, 864, 864], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 216, 0, 216, 0, -432], [], [], [], [-1296, -1512, -432, 648, 864, 432], [], [], [], []]

def g32p_row17_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def g32p_row17_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row17_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 1296 (g32p_row17_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row17_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row17_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row17_pairing_0
  · exact g32p_row17_pairing_1
  · exact g32p_row17_pairing_2
  · exact g32p_row17_pairing_3
  · exact g32p_row17_pairing_4
  · exact g32p_row17_pairing_5
  · exact g32p_row17_pairing_6
  · exact g32p_row17_pairing_7
  · exact g32p_row17_pairing_8
  · exact g32p_row17_pairing_9
  · exact g32p_row17_pairing_10
  · exact g32p_row17_pairing_11
  · exact g32p_row17_pairing_12
  · exact g32p_row17_pairing_13
  · exact g32p_row17_pairing_14
  · exact g32p_row17_pairing_15
  · exact g32p_row17_pairing_16
  · exact g32p_row17_pairing_17
  · exact g32p_row17_pairing_18
  · exact g32p_row17_pairing_19
  · exact g32p_row17_pairing_20
  · exact g32p_row17_pairing_21
  · exact g32p_row17_pairing_22
  · exact g32p_row17_pairing_23
  · exact g32p_row17_pairing_24
  · exact g32p_row17_pairing_25
  · exact g32p_row17_pairing_26
  · exact g32p_row17_pairing_27
  · exact g32p_row17_pairing_28
  · exact g32p_row17_pairing_29
  · exact g32p_row17_pairing_30
  · exact g32p_row17_pairing_31
  · exact g32p_row17_pairing_32
  · exact g32p_row17_pairing_33
  · exact g32p_row17_pairing_34
  · exact g32p_row17_pairing_35
  · exact g32p_row17_pairing_36
  · exact g32p_row17_pairing_37
  · exact g32p_row17_pairing_38
  · exact g32p_row17_pairing_39
  · exact g32p_row17_pairing_40
  · exact g32p_row17_pairing_41
  · exact g32p_row17_pairing_42
  · exact g32p_row17_pairing_43

theorem g32p_row17_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 1296 (g32p_row17_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row17_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row17_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row17_pairing_44
  · exact g32p_row17_pairing_45
  · exact g32p_row17_pairing_46
  · exact g32p_row17_pairing_47

theorem g32p_row17_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 1296)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row17_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row17_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 17 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row17_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row17_freeCoordinates g32p_row17_quaternionicMultiplicities
    g32p_row17_pairingTerms [1, -1, 1] g32p_row17_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row17_pairingFree)
    (by rw [horder]; exact g32p_row17_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
