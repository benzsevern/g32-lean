import HodgeLean.Foundations.Program.G32PropFourSixPacked0512
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0513
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0375
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

theorem g32p_row18_restrictionCount_24 :
    (Finset.univ.filter (fun i => g32p_row18_restrictionBucket i = 24)).card = g32p_row18_restrictionSizes 24 := by
  decide +kernel

theorem g32p_row18_restrictionCount_25 :
    (Finset.univ.filter (fun i => g32p_row18_restrictionBucket i = 25)).card = g32p_row18_restrictionSizes 25 := by
  decide +kernel

theorem g32p_row18_restrictionCount_26 :
    (Finset.univ.filter (fun i => g32p_row18_restrictionBucket i = 26)).card = g32p_row18_restrictionSizes 26 := by
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

theorem g32p_row18_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row18_characterValues (g32p_finBlockIndex 36 0 r))⁻¹).val =
      g32p_row18_restrictionExponents (g32p_row18_restrictionBucket (g32p_finBlockIndex 36 0 r)) := by
  decide +kernel

theorem g32p_row18_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row18_characterValues (g32p_finBlockIndex 36 1 r))⁻¹).val =
      g32p_row18_restrictionExponents (g32p_row18_restrictionBucket (g32p_finBlockIndex 36 1 r)) := by
  decide +kernel

theorem g32p_row18_restrictionExponent_2 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row18_characterValues (g32p_finBlockIndex 36 2 r))⁻¹).val =
      g32p_row18_restrictionExponents (g32p_row18_restrictionBucket (g32p_finBlockIndex 36 2 r)) := by
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

theorem g32p_row18_restrictionCounts (a : Fin 27) :
    (Finset.univ.filter (fun i => g32p_row18_restrictionBucket i = a)).card = g32p_row18_restrictionSizes a := by
  fin_cases a
  · exact g32p_row18_restrictionCount_0
  · exact g32p_row18_restrictionCount_1
  · exact g32p_row18_restrictionCount_2
  · exact g32p_row18_restrictionCount_3
  · exact g32p_row18_restrictionCount_4
  · exact g32p_row18_restrictionCount_5
  · exact g32p_row18_restrictionCount_6
  · exact g32p_row18_restrictionCount_7
  · exact g32p_row18_restrictionCount_8
  · exact g32p_row18_restrictionCount_9
  · exact g32p_row18_restrictionCount_10
  · exact g32p_row18_restrictionCount_11
  · exact g32p_row18_restrictionCount_12
  · exact g32p_row18_restrictionCount_13
  · exact g32p_row18_restrictionCount_14
  · exact g32p_row18_restrictionCount_15
  · exact g32p_row18_restrictionCount_16
  · exact g32p_row18_restrictionCount_17
  · exact g32p_row18_restrictionCount_18
  · exact g32p_row18_restrictionCount_19
  · exact g32p_row18_restrictionCount_20
  · exact g32p_row18_restrictionCount_21
  · exact g32p_row18_restrictionCount_22
  · exact g32p_row18_restrictionCount_23
  · exact g32p_row18_restrictionCount_24
  · exact g32p_row18_restrictionCount_25
  · exact g32p_row18_restrictionCount_26

theorem g32p_row18_restrictionExponent (i : Fin 36) :
    (Multiplicative.toAdd (g32p_row18_characterValues i)⁻¹).val =
      g32p_row18_restrictionExponents (g32p_row18_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_restrictionExponent_0
  · exact g32p_row18_restrictionExponent_1
  · exact g32p_row18_restrictionExponent_2

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row18_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 36),
      g32p_restrictionTrace τ τbar θ j (g32p_row18_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row18_restrictionCoefficients j (g32p_row18_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 18 ∧
      papersA τ τbar θ g32p_row18_finiteSupplier.H (g32p_complexCharacter g32p_row18_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row18_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row18_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row18_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 6 ^ (6 / 3)) x.2.1 *
          g32p_root 6 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row18_finiteSupplier
      g32p_row18_groupEquiv g32p_row18_characterValues g32p_row18_finiteSupplier_value
      g32p_row18_restrictionBucket g32p_row18_restrictionSizes g32p_row18_restrictionExponents
      g32p_row18_restrictionCounts g32p_row18_restrictionExponent
      τ τbar θ g32p_row18_pairingTerms g32p_row18_restrictionCoefficients
      g32p_row18_restrictionLabels (g32p_restriction_root_omega 6 (by decide)) htrace
      g32p_row18_restrictionDecode g32p_row18_restrictionTerms j
  apply g32p_row18_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row18_finiteSupplier)
    (g32p_root 6) (g32p_root_primitive g32p_row18_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row18_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row18_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row18_groupEquiv i) =
      g32p_row18_restrictionClasses (g32p_row18_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 18 ∧
      papersA τ τbar θ g32p_row18_finiteSupplier.H
        (g32p_complexCharacter g32p_row18_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row18_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row18_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row18_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 18 ∧ r.m = g32p_row18_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row18_finiteSupplier.H ∧
      (g32p_exponents g32p_row18_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 36),
      g32p_restrictionTrace τ τbar θ j (g32p_row18_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row18_restrictionCoefficients j (g32p_row18_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 18 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 18 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row18_finiteSupplier, g32p_complexCharacter g32p_row18_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row18_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row18_supplierClassifier (g32p_finBlockIndex 36 0 r) =
      g32p_row18_restrictionClasses (g32p_row18_restrictionBucket (g32p_finBlockIndex 36 0 r)) := by
  decide +kernel

theorem g32p_row18_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row18_supplierClassifier (g32p_finBlockIndex 36 1 r) =
      g32p_row18_restrictionClasses (g32p_row18_restrictionBucket (g32p_finBlockIndex 36 1 r)) := by
  decide +kernel

theorem g32p_row18_integrationClasses_002 : ∀ r : Fin 16,
    g32p_row18_supplierClassifier (g32p_finBlockIndex 36 2 r) =
      g32p_row18_restrictionClasses (g32p_row18_restrictionBucket (g32p_finBlockIndex 36 2 r)) := by
  decide +kernel

theorem g32p_row18_integrationClasses (i : Fin 36) :
    g32p_integrationLabel (g32p_row18_groupEquiv i) =
      g32p_row18_restrictionClasses (g32p_row18_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row18_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row18_supplierClassifier i =
    g32p_row18_restrictionClasses (g32p_row18_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row18_integrationClasses_000 r
  · exact g32p_row18_integrationClasses_001 r
  · exact g32p_row18_integrationClasses_002 r

theorem g32p_row18_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 18 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 17).H
        (g32p_recordedSupplierCharacters 17) = g32SparseVec v.coords := by
  exact g32p_row18_restriction_from_family g32p_integrationLabel g32p_row18_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row18_integrationRestriction

theorem g32p_row18_integrationNode (j : Fin 48) (i : Fin 36) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row18_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row18_restrictionCoefficients j (g32p_row18_restrictionBucket i)) := by
  rw [g32p_row18_integrationClasses, g32p_row18_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row19_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row19_terms_0, g32p_row19_terms_1, g32p_row19_terms_2, g32p_row19_terms_3, g32p_row19_terms_4, g32p_row19_terms_5, g32p_row19_terms_6, g32p_row19_terms_7, g32p_row19_terms_8, g32p_row19_terms_9, g32p_row19_terms_10, g32p_row19_terms_11, g32p_row19_terms_12, g32p_row19_terms_13, g32p_row19_terms_14, g32p_row19_terms_15, g32p_row19_terms_16, g32p_row19_terms_17, g32p_row19_terms_18, g32p_row19_terms_19, g32p_row19_terms_20, g32p_row19_terms_21, g32p_row19_terms_22, g32p_row19_terms_23, g32p_row19_terms_24, g32p_row19_terms_25, g32p_row19_terms_26, g32p_row19_terms_27, g32p_row19_terms_28, g32p_row19_terms_29, g32p_row19_terms_30, g32p_row19_terms_31, g32p_row19_terms_32, g32p_row19_terms_33, g32p_row19_terms_34, g32p_row19_terms_35, g32p_row19_terms_36, g32p_row19_terms_37, g32p_row19_terms_38, g32p_row19_terms_39, g32p_row19_terms_40, g32p_row19_terms_41, g32p_row19_terms_42, g32p_row19_terms_43, g32p_row19_terms_44, g32p_row19_terms_45, g32p_row19_terms_46, g32p_row19_terms_47]

def g32p_row19_pairingQuotients : Fin 48 → List ℤ :=
  ![[], [], [], [], [], [], [-1152, -1344, -384, 576, 768, 384], [], [], [], [], [0, 192, 0, 192, 0, -384], [], [], [], [], [], [], [], [], [], [], [], [0, 192, 0, 192, 0, -384], [-1152, -1152, -384, 768, 768], [], [], [], [], [], [], [-1152, -1344, -384, 576, 768, 384], [], [], [], [], [], [], [], [-1152, -1152, -384, 768, 768], [], [], [], [], [], [], [], []]

def g32p_row19_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

def g32p_row19_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row19_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 1152 (g32p_row19_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row19_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row19_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row19_pairing_0
  · exact g32p_row19_pairing_1
  · exact g32p_row19_pairing_2
  · exact g32p_row19_pairing_3
  · exact g32p_row19_pairing_4
  · exact g32p_row19_pairing_5
  · exact g32p_row19_pairing_6
  · exact g32p_row19_pairing_7
  · exact g32p_row19_pairing_8
  · exact g32p_row19_pairing_9
  · exact g32p_row19_pairing_10
  · exact g32p_row19_pairing_11
  · exact g32p_row19_pairing_12
  · exact g32p_row19_pairing_13
  · exact g32p_row19_pairing_14
  · exact g32p_row19_pairing_15
  · exact g32p_row19_pairing_16
  · exact g32p_row19_pairing_17
  · exact g32p_row19_pairing_18
  · exact g32p_row19_pairing_19
  · exact g32p_row19_pairing_20
  · exact g32p_row19_pairing_21
  · exact g32p_row19_pairing_22
  · exact g32p_row19_pairing_23
  · exact g32p_row19_pairing_24
  · exact g32p_row19_pairing_25
  · exact g32p_row19_pairing_26
  · exact g32p_row19_pairing_27
  · exact g32p_row19_pairing_28
  · exact g32p_row19_pairing_29
  · exact g32p_row19_pairing_30
  · exact g32p_row19_pairing_31
  · exact g32p_row19_pairing_32
  · exact g32p_row19_pairing_33
  · exact g32p_row19_pairing_34
  · exact g32p_row19_pairing_35
  · exact g32p_row19_pairing_36
  · exact g32p_row19_pairing_37
  · exact g32p_row19_pairing_38
  · exact g32p_row19_pairing_39
  · exact g32p_row19_pairing_40
  · exact g32p_row19_pairing_41
  · exact g32p_row19_pairing_42
  · exact g32p_row19_pairing_43

theorem g32p_row19_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 1152 (g32p_row19_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row19_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row19_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row19_pairing_44
  · exact g32p_row19_pairing_45
  · exact g32p_row19_pairing_46
  · exact g32p_row19_pairing_47

theorem g32p_row19_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 1152)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row19_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row19_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 19 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row19_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row19_freeCoordinates g32p_row19_quaternionicMultiplicities
    g32p_row19_pairingTerms [1, -1, 1] g32p_row19_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row19_pairingFree)
    (by rw [horder]; exact g32p_row19_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
