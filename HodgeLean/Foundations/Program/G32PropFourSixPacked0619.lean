import HodgeLean.Foundations.Program.G32PropFourSixPacked0617
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0618
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0438
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0006

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row50_restrictionCount_24 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 24)).card = g32p_row50_restrictionSizes 24 := by
  decide +kernel

theorem g32p_row50_restrictionCount_25 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 25)).card = g32p_row50_restrictionSizes 25 := by
  decide +kernel

theorem g32p_row50_restrictionCount_26 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 26)).card = g32p_row50_restrictionSizes 26 := by
  decide +kernel

theorem g32p_row50_restrictionCount_27 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 27)).card = g32p_row50_restrictionSizes 27 := by
  decide +kernel

theorem g32p_row50_restrictionCount_28 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 28)).card = g32p_row50_restrictionSizes 28 := by
  decide +kernel

theorem g32p_row50_restrictionCount_29 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 29)).card = g32p_row50_restrictionSizes 29 := by
  decide +kernel

theorem g32p_row50_restrictionCount_30 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 30)).card = g32p_row50_restrictionSizes 30 := by
  decide +kernel

theorem g32p_row50_restrictionCount_31 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 31)).card = g32p_row50_restrictionSizes 31 := by
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

theorem g32p_row50_restrictionCount_32 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 32)).card = g32p_row50_restrictionSizes 32 := by
  decide +kernel

theorem g32p_row50_restrictionCount_33 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 33)).card = g32p_row50_restrictionSizes 33 := by
  decide +kernel

theorem g32p_row50_restrictionCount_34 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 34)).card = g32p_row50_restrictionSizes 34 := by
  decide +kernel

theorem g32p_row50_restrictionCount_35 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 35)).card = g32p_row50_restrictionSizes 35 := by
  decide +kernel

theorem g32p_row50_restrictionCount_36 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 36)).card = g32p_row50_restrictionSizes 36 := by
  decide +kernel

theorem g32p_row50_restrictionCount_37 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 37)).card = g32p_row50_restrictionSizes 37 := by
  decide +kernel

theorem g32p_row50_restrictionCount_38 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 38)).card = g32p_row50_restrictionSizes 38 := by
  decide +kernel

theorem g32p_row50_restrictionCount_39 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 39)).card = g32p_row50_restrictionSizes 39 := by
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

theorem g32p_row50_restrictionCount_40 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 40)).card = g32p_row50_restrictionSizes 40 := by
  decide +kernel

theorem g32p_row50_restrictionCount_41 :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = 41)).card = g32p_row50_restrictionSizes 41 := by
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

theorem g32p_row50_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 0 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 0 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 1 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 1 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_2 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 2 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 2 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_3 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 3 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 3 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_4 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 4 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 4 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_5 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 5 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 5 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_6 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 6 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 6 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_7 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 7 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 7 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_8 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 8 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 8 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_9 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 9 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 9 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_10 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 10 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 10 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_11 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 11 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 11 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_12 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 12 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 12 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_13 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 13 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 13 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_14 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 14 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 14 r)) := by
  decide +kernel

theorem g32p_row50_restrictionExponent_15 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row50_characterValues (g32p_finBlockIndex 243 15 r))⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 15 r)) := by
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

theorem g32p_row50_restrictionCounts (a : Fin 42) :
    (Finset.univ.filter (fun i => g32p_row50_restrictionBucket i = a)).card = g32p_row50_restrictionSizes a := by
  fin_cases a
  · exact g32p_row50_restrictionCount_0
  · exact g32p_row50_restrictionCount_1
  · exact g32p_row50_restrictionCount_2
  · exact g32p_row50_restrictionCount_3
  · exact g32p_row50_restrictionCount_4
  · exact g32p_row50_restrictionCount_5
  · exact g32p_row50_restrictionCount_6
  · exact g32p_row50_restrictionCount_7
  · exact g32p_row50_restrictionCount_8
  · exact g32p_row50_restrictionCount_9
  · exact g32p_row50_restrictionCount_10
  · exact g32p_row50_restrictionCount_11
  · exact g32p_row50_restrictionCount_12
  · exact g32p_row50_restrictionCount_13
  · exact g32p_row50_restrictionCount_14
  · exact g32p_row50_restrictionCount_15
  · exact g32p_row50_restrictionCount_16
  · exact g32p_row50_restrictionCount_17
  · exact g32p_row50_restrictionCount_18
  · exact g32p_row50_restrictionCount_19
  · exact g32p_row50_restrictionCount_20
  · exact g32p_row50_restrictionCount_21
  · exact g32p_row50_restrictionCount_22
  · exact g32p_row50_restrictionCount_23
  · exact g32p_row50_restrictionCount_24
  · exact g32p_row50_restrictionCount_25
  · exact g32p_row50_restrictionCount_26
  · exact g32p_row50_restrictionCount_27
  · exact g32p_row50_restrictionCount_28
  · exact g32p_row50_restrictionCount_29
  · exact g32p_row50_restrictionCount_30
  · exact g32p_row50_restrictionCount_31
  · exact g32p_row50_restrictionCount_32
  · exact g32p_row50_restrictionCount_33
  · exact g32p_row50_restrictionCount_34
  · exact g32p_row50_restrictionCount_35
  · exact g32p_row50_restrictionCount_36
  · exact g32p_row50_restrictionCount_37
  · exact g32p_row50_restrictionCount_38
  · exact g32p_row50_restrictionCount_39
  · exact g32p_row50_restrictionCount_40
  · exact g32p_row50_restrictionCount_41

theorem g32p_row50_restrictionExponent (i : Fin 243) :
    (Multiplicative.toAdd (g32p_row50_characterValues i)⁻¹).val =
      g32p_row50_restrictionExponents (g32p_row50_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_restrictionExponent_0
  · exact g32p_row50_restrictionExponent_1
  · exact g32p_row50_restrictionExponent_2
  · exact g32p_row50_restrictionExponent_3
  · exact g32p_row50_restrictionExponent_4
  · exact g32p_row50_restrictionExponent_5
  · exact g32p_row50_restrictionExponent_6
  · exact g32p_row50_restrictionExponent_7
  · exact g32p_row50_restrictionExponent_8
  · exact g32p_row50_restrictionExponent_9
  · exact g32p_row50_restrictionExponent_10
  · exact g32p_row50_restrictionExponent_11
  · exact g32p_row50_restrictionExponent_12
  · exact g32p_row50_restrictionExponent_13
  · exact g32p_row50_restrictionExponent_14
  · exact g32p_row50_restrictionExponent_15

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row50_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 243),
      g32p_restrictionTrace τ τbar θ j (g32p_row50_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row50_restrictionCoefficients j (g32p_row50_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 50 ∧
      papersA τ τbar θ g32p_row50_finiteSupplier.H (g32p_complexCharacter g32p_row50_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row50_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row50_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row50_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 3 ^ (3 / 3)) x.2.1 *
          g32p_root 3 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row50_finiteSupplier
      g32p_row50_groupEquiv g32p_row50_characterValues g32p_row50_finiteSupplier_value
      g32p_row50_restrictionBucket g32p_row50_restrictionSizes g32p_row50_restrictionExponents
      g32p_row50_restrictionCounts g32p_row50_restrictionExponent
      τ τbar θ g32p_row50_pairingTerms g32p_row50_restrictionCoefficients
      g32p_row50_restrictionLabels (g32p_restriction_root_omega 3 (by decide)) htrace
      g32p_row50_restrictionDecode g32p_row50_restrictionTerms j
  apply g32p_row50_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row50_finiteSupplier)
    (g32p_root 3) (g32p_root_primitive g32p_row50_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row50_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row50_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row50_groupEquiv i) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 50 ∧
      papersA τ τbar θ g32p_row50_finiteSupplier.H
        (g32p_complexCharacter g32p_row50_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row50_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row50_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row50_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 50 ∧ r.m = g32p_row50_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row50_finiteSupplier.H ∧
      (g32p_exponents g32p_row50_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 243),
      g32p_restrictionTrace τ τbar θ j (g32p_row50_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row50_restrictionCoefficients j (g32p_row50_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 50 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 50 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row50_finiteSupplier, g32p_complexCharacter g32p_row50_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row50_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 0 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 0 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 1 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 1 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_002 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 2 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 2 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_003 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 3 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 3 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_004 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 4 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 4 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_005 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 5 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 5 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_006 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 6 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 6 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_007 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 7 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 7 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_008 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 8 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 8 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_009 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 9 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 9 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_010 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 10 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 10 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_011 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 11 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 11 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_012 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 12 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 12 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_013 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 13 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 13 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_014 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 14 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 14 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses_015 : ∀ r : Fin 16,
    g32p_row50_supplierClassifier (g32p_finBlockIndex 243 15 r) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket (g32p_finBlockIndex 243 15 r)) := by
  decide +kernel

theorem g32p_row50_integrationClasses (i : Fin 243) :
    g32p_integrationLabel (g32p_row50_groupEquiv i) =
      g32p_row50_restrictionClasses (g32p_row50_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row50_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row50_supplierClassifier i =
    g32p_row50_restrictionClasses (g32p_row50_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row50_integrationClasses_000 r
  · exact g32p_row50_integrationClasses_001 r
  · exact g32p_row50_integrationClasses_002 r
  · exact g32p_row50_integrationClasses_003 r
  · exact g32p_row50_integrationClasses_004 r
  · exact g32p_row50_integrationClasses_005 r
  · exact g32p_row50_integrationClasses_006 r
  · exact g32p_row50_integrationClasses_007 r
  · exact g32p_row50_integrationClasses_008 r
  · exact g32p_row50_integrationClasses_009 r
  · exact g32p_row50_integrationClasses_010 r
  · exact g32p_row50_integrationClasses_011 r
  · exact g32p_row50_integrationClasses_012 r
  · exact g32p_row50_integrationClasses_013 r
  · exact g32p_row50_integrationClasses_014 r
  · exact g32p_row50_integrationClasses_015 r

theorem g32p_row50_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 50 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 49).H
        (g32p_recordedSupplierCharacters 49) = g32SparseVec v.coords := by
  exact g32p_row50_restriction_from_family g32p_integrationLabel g32p_row50_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row50_integrationRestriction

theorem g32p_row50_integrationNode (j : Fin 48) (i : Fin 243) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row50_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row50_restrictionCoefficients j (g32p_row50_restrictionBucket i)) := by
  rw [g32p_row50_integrationClasses, g32p_row50_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row51_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row51_terms_0, g32p_row51_terms_1, g32p_row51_terms_2, g32p_row51_terms_3, g32p_row51_terms_4, g32p_row51_terms_5, g32p_row51_terms_6, g32p_row51_terms_7, g32p_row51_terms_8, g32p_row51_terms_9, g32p_row51_terms_10, g32p_row51_terms_11, g32p_row51_terms_12, g32p_row51_terms_13, g32p_row51_terms_14, g32p_row51_terms_15, g32p_row51_terms_16, g32p_row51_terms_17, g32p_row51_terms_18, g32p_row51_terms_19, g32p_row51_terms_20, g32p_row51_terms_21, g32p_row51_terms_22, g32p_row51_terms_23, g32p_row51_terms_24, g32p_row51_terms_25, g32p_row51_terms_26, g32p_row51_terms_27, g32p_row51_terms_28, g32p_row51_terms_29, g32p_row51_terms_30, g32p_row51_terms_31, g32p_row51_terms_32, g32p_row51_terms_33, g32p_row51_terms_34, g32p_row51_terms_35, g32p_row51_terms_36, g32p_row51_terms_37, g32p_row51_terms_38, g32p_row51_terms_39, g32p_row51_terms_40, g32p_row51_terms_41, g32p_row51_terms_42, g32p_row51_terms_43, g32p_row51_terms_44, g32p_row51_terms_45, g32p_row51_terms_46, g32p_row51_terms_47]

def g32p_row51_pairingQuotients : Fin 48 → List ℤ :=
  ![[], [], [], [], [], [], [], [], [-216, 144], [], [], [], [], [], [], [], [], [], [], [], [], [], [216, -144], [], [], [], [-432, 288], [], [], [216, -144], [], [], [216, -144], [], [], [216, -144], [], [], [], [], [], [], [], [], [-72], [], [-144], [72]]

def g32p_row51_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]

def g32p_row51_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![1, 0, 2, 1]

theorem g32p_row51_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 216 (g32p_row51_freeCoordinates j)
      (g32p_pairingCoefficients 3 (g32p_row51_pairingTerms ⟨j.val, by omega⟩))
      [1, 1, 1] (g32p_row51_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row51_pairing_0
  · exact g32p_row51_pairing_1
  · exact g32p_row51_pairing_2
  · exact g32p_row51_pairing_3
  · exact g32p_row51_pairing_4
  · exact g32p_row51_pairing_5
  · exact g32p_row51_pairing_6
  · exact g32p_row51_pairing_7
  · exact g32p_row51_pairing_8
  · exact g32p_row51_pairing_9
  · exact g32p_row51_pairing_10
  · exact g32p_row51_pairing_11
  · exact g32p_row51_pairing_12
  · exact g32p_row51_pairing_13
  · exact g32p_row51_pairing_14
  · exact g32p_row51_pairing_15
  · exact g32p_row51_pairing_16
  · exact g32p_row51_pairing_17
  · exact g32p_row51_pairing_18
  · exact g32p_row51_pairing_19
  · exact g32p_row51_pairing_20
  · exact g32p_row51_pairing_21
  · exact g32p_row51_pairing_22
  · exact g32p_row51_pairing_23
  · exact g32p_row51_pairing_24
  · exact g32p_row51_pairing_25
  · exact g32p_row51_pairing_26
  · exact g32p_row51_pairing_27
  · exact g32p_row51_pairing_28
  · exact g32p_row51_pairing_29
  · exact g32p_row51_pairing_30
  · exact g32p_row51_pairing_31
  · exact g32p_row51_pairing_32
  · exact g32p_row51_pairing_33
  · exact g32p_row51_pairing_34
  · exact g32p_row51_pairing_35
  · exact g32p_row51_pairing_36
  · exact g32p_row51_pairing_37
  · exact g32p_row51_pairing_38
  · exact g32p_row51_pairing_39
  · exact g32p_row51_pairing_40
  · exact g32p_row51_pairing_41
  · exact g32p_row51_pairing_42
  · exact g32p_row51_pairing_43

theorem g32p_row51_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 216 (g32p_row51_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 3 (g32p_row51_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, 1, 1] (g32p_row51_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row51_pairing_44
  · exact g32p_row51_pairing_45
  · exact g32p_row51_pairing_46
  · exact g32p_row51_pairing_47

theorem g32p_row51_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 3) (horder : Fintype.card H = 216)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row51_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (3 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row51_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (3 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 51 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row51_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 3
    g32p_row51_freeCoordinates g32p_row51_quaternionicMultiplicities
    g32p_row51_pairingTerms [1, 1, 1] g32p_row51_pairingQuotients z
    (g32p_pairing_modulus_three hz) hfree hquat
    (by rw [horder]; exact g32p_row51_pairingFree)
    (by rw [horder]; exact g32p_row51_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
