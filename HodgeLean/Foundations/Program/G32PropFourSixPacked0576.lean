import HodgeLean.Foundations.Program.G32PropFourSixPacked0574
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0575
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0418
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0005

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row36_restrictionCount_24 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 24)).card = g32p_row36_restrictionSizes 24 := by
  decide +kernel

theorem g32p_row36_restrictionCount_25 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 25)).card = g32p_row36_restrictionSizes 25 := by
  decide +kernel

theorem g32p_row36_restrictionCount_26 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 26)).card = g32p_row36_restrictionSizes 26 := by
  decide +kernel

theorem g32p_row36_restrictionCount_27 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 27)).card = g32p_row36_restrictionSizes 27 := by
  decide +kernel

theorem g32p_row36_restrictionCount_28 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 28)).card = g32p_row36_restrictionSizes 28 := by
  decide +kernel

theorem g32p_row36_restrictionCount_29 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 29)).card = g32p_row36_restrictionSizes 29 := by
  decide +kernel

theorem g32p_row36_restrictionCount_30 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 30)).card = g32p_row36_restrictionSizes 30 := by
  decide +kernel

theorem g32p_row36_restrictionCount_31 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 31)).card = g32p_row36_restrictionSizes 31 := by
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

theorem g32p_row36_restrictionCount_32 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 32)).card = g32p_row36_restrictionSizes 32 := by
  decide +kernel

theorem g32p_row36_restrictionCount_33 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 33)).card = g32p_row36_restrictionSizes 33 := by
  decide +kernel

theorem g32p_row36_restrictionCount_34 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 34)).card = g32p_row36_restrictionSizes 34 := by
  decide +kernel

theorem g32p_row36_restrictionCount_35 :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = 35)).card = g32p_row36_restrictionSizes 35 := by
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

theorem g32p_row36_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 0 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 0 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 1 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 1 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_2 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 2 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 2 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_3 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 3 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 3 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_4 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 4 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 4 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_5 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 5 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 5 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_6 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 6 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 6 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_7 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 7 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 7 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_8 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 8 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 8 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_9 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 9 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 9 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_10 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 10 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 10 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_11 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 11 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 11 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_12 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 12 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 12 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_13 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 13 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 13 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_14 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 14 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 14 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_15 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 15 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 15 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_16 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 16 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 16 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_17 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 17 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 17 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_18 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 18 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 18 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_19 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 19 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 19 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_20 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 20 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 20 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_21 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 21 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 21 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_22 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 22 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 22 r)) := by
  decide +kernel

theorem g32p_row36_restrictionExponent_23 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row36_characterValues (g32p_finBlockIndex 384 23 r))⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 23 r)) := by
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

theorem g32p_row36_restrictionCounts (a : Fin 36) :
    (Finset.univ.filter (fun i => g32p_row36_restrictionBucket i = a)).card = g32p_row36_restrictionSizes a := by
  fin_cases a
  · exact g32p_row36_restrictionCount_0
  · exact g32p_row36_restrictionCount_1
  · exact g32p_row36_restrictionCount_2
  · exact g32p_row36_restrictionCount_3
  · exact g32p_row36_restrictionCount_4
  · exact g32p_row36_restrictionCount_5
  · exact g32p_row36_restrictionCount_6
  · exact g32p_row36_restrictionCount_7
  · exact g32p_row36_restrictionCount_8
  · exact g32p_row36_restrictionCount_9
  · exact g32p_row36_restrictionCount_10
  · exact g32p_row36_restrictionCount_11
  · exact g32p_row36_restrictionCount_12
  · exact g32p_row36_restrictionCount_13
  · exact g32p_row36_restrictionCount_14
  · exact g32p_row36_restrictionCount_15
  · exact g32p_row36_restrictionCount_16
  · exact g32p_row36_restrictionCount_17
  · exact g32p_row36_restrictionCount_18
  · exact g32p_row36_restrictionCount_19
  · exact g32p_row36_restrictionCount_20
  · exact g32p_row36_restrictionCount_21
  · exact g32p_row36_restrictionCount_22
  · exact g32p_row36_restrictionCount_23
  · exact g32p_row36_restrictionCount_24
  · exact g32p_row36_restrictionCount_25
  · exact g32p_row36_restrictionCount_26
  · exact g32p_row36_restrictionCount_27
  · exact g32p_row36_restrictionCount_28
  · exact g32p_row36_restrictionCount_29
  · exact g32p_row36_restrictionCount_30
  · exact g32p_row36_restrictionCount_31
  · exact g32p_row36_restrictionCount_32
  · exact g32p_row36_restrictionCount_33
  · exact g32p_row36_restrictionCount_34
  · exact g32p_row36_restrictionCount_35

theorem g32p_row36_restrictionExponent (i : Fin 384) :
    (Multiplicative.toAdd (g32p_row36_characterValues i)⁻¹).val =
      g32p_row36_restrictionExponents (g32p_row36_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_restrictionExponent_0
  · exact g32p_row36_restrictionExponent_1
  · exact g32p_row36_restrictionExponent_2
  · exact g32p_row36_restrictionExponent_3
  · exact g32p_row36_restrictionExponent_4
  · exact g32p_row36_restrictionExponent_5
  · exact g32p_row36_restrictionExponent_6
  · exact g32p_row36_restrictionExponent_7
  · exact g32p_row36_restrictionExponent_8
  · exact g32p_row36_restrictionExponent_9
  · exact g32p_row36_restrictionExponent_10
  · exact g32p_row36_restrictionExponent_11
  · exact g32p_row36_restrictionExponent_12
  · exact g32p_row36_restrictionExponent_13
  · exact g32p_row36_restrictionExponent_14
  · exact g32p_row36_restrictionExponent_15
  · exact g32p_row36_restrictionExponent_16
  · exact g32p_row36_restrictionExponent_17
  · exact g32p_row36_restrictionExponent_18
  · exact g32p_row36_restrictionExponent_19
  · exact g32p_row36_restrictionExponent_20
  · exact g32p_row36_restrictionExponent_21
  · exact g32p_row36_restrictionExponent_22
  · exact g32p_row36_restrictionExponent_23

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row36_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 384),
      g32p_restrictionTrace τ τbar θ j (g32p_row36_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row36_restrictionCoefficients j (g32p_row36_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 36 ∧
      papersA τ τbar θ g32p_row36_finiteSupplier.H (g32p_complexCharacter g32p_row36_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row36_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row36_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row36_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 6 ^ (6 / 3)) x.2.1 *
          g32p_root 6 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row36_finiteSupplier
      g32p_row36_groupEquiv g32p_row36_characterValues g32p_row36_finiteSupplier_value
      g32p_row36_restrictionBucket g32p_row36_restrictionSizes g32p_row36_restrictionExponents
      g32p_row36_restrictionCounts g32p_row36_restrictionExponent
      τ τbar θ g32p_row36_pairingTerms g32p_row36_restrictionCoefficients
      g32p_row36_restrictionLabels (g32p_restriction_root_omega 6 (by decide)) htrace
      g32p_row36_restrictionDecode g32p_row36_restrictionTerms j
  apply g32p_row36_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row36_finiteSupplier)
    (g32p_root 6) (g32p_root_primitive g32p_row36_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row36_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row36_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row36_groupEquiv i) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 36 ∧
      papersA τ τbar θ g32p_row36_finiteSupplier.H
        (g32p_complexCharacter g32p_row36_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row36_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row36_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row36_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 36 ∧ r.m = g32p_row36_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row36_finiteSupplier.H ∧
      (g32p_exponents g32p_row36_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 384),
      g32p_restrictionTrace τ τbar θ j (g32p_row36_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row36_restrictionCoefficients j (g32p_row36_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 36 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 36 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row36_finiteSupplier, g32p_complexCharacter g32p_row36_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row36_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 0 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 0 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 1 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 1 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_002 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 2 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 2 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_003 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 3 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 3 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_004 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 4 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 4 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_005 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 5 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 5 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_006 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 6 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 6 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_007 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 7 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 7 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_008 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 8 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 8 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_009 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 9 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 9 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_010 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 10 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 10 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_011 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 11 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 11 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_012 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 12 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 12 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_013 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 13 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 13 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_014 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 14 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 14 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_015 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 15 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 15 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_016 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 16 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 16 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_017 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 17 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 17 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_018 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 18 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 18 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_019 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 19 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 19 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_020 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 20 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 20 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_021 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 21 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 21 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_022 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 22 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 22 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses_023 : ∀ r : Fin 16,
    g32p_row36_supplierClassifier (g32p_finBlockIndex 384 23 r) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket (g32p_finBlockIndex 384 23 r)) := by
  decide +kernel

theorem g32p_row36_integrationClasses (i : Fin 384) :
    g32p_integrationLabel (g32p_row36_groupEquiv i) =
      g32p_row36_restrictionClasses (g32p_row36_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row36_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row36_supplierClassifier i =
    g32p_row36_restrictionClasses (g32p_row36_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row36_integrationClasses_000 r
  · exact g32p_row36_integrationClasses_001 r
  · exact g32p_row36_integrationClasses_002 r
  · exact g32p_row36_integrationClasses_003 r
  · exact g32p_row36_integrationClasses_004 r
  · exact g32p_row36_integrationClasses_005 r
  · exact g32p_row36_integrationClasses_006 r
  · exact g32p_row36_integrationClasses_007 r
  · exact g32p_row36_integrationClasses_008 r
  · exact g32p_row36_integrationClasses_009 r
  · exact g32p_row36_integrationClasses_010 r
  · exact g32p_row36_integrationClasses_011 r
  · exact g32p_row36_integrationClasses_012 r
  · exact g32p_row36_integrationClasses_013 r
  · exact g32p_row36_integrationClasses_014 r
  · exact g32p_row36_integrationClasses_015 r
  · exact g32p_row36_integrationClasses_016 r
  · exact g32p_row36_integrationClasses_017 r
  · exact g32p_row36_integrationClasses_018 r
  · exact g32p_row36_integrationClasses_019 r
  · exact g32p_row36_integrationClasses_020 r
  · exact g32p_row36_integrationClasses_021 r
  · exact g32p_row36_integrationClasses_022 r
  · exact g32p_row36_integrationClasses_023 r

theorem g32p_row36_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 36 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 35).H
        (g32p_recordedSupplierCharacters 35) = g32SparseVec v.coords := by
  exact g32p_row36_restriction_from_family g32p_integrationLabel g32p_row36_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row36_integrationRestriction

theorem g32p_row36_integrationNode (j : Fin 48) (i : Fin 384) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row36_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row36_restrictionCoefficients j (g32p_row36_restrictionBucket i)) := by
  rw [g32p_row36_integrationClasses, g32p_row36_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row37_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row37_terms_0, g32p_row37_terms_1, g32p_row37_terms_2, g32p_row37_terms_3, g32p_row37_terms_4, g32p_row37_terms_5, g32p_row37_terms_6, g32p_row37_terms_7, g32p_row37_terms_8, g32p_row37_terms_9, g32p_row37_terms_10, g32p_row37_terms_11, g32p_row37_terms_12, g32p_row37_terms_13, g32p_row37_terms_14, g32p_row37_terms_15, g32p_row37_terms_16, g32p_row37_terms_17, g32p_row37_terms_18, g32p_row37_terms_19, g32p_row37_terms_20, g32p_row37_terms_21, g32p_row37_terms_22, g32p_row37_terms_23, g32p_row37_terms_24, g32p_row37_terms_25, g32p_row37_terms_26, g32p_row37_terms_27, g32p_row37_terms_28, g32p_row37_terms_29, g32p_row37_terms_30, g32p_row37_terms_31, g32p_row37_terms_32, g32p_row37_terms_33, g32p_row37_terms_34, g32p_row37_terms_35, g32p_row37_terms_36, g32p_row37_terms_37, g32p_row37_terms_38, g32p_row37_terms_39, g32p_row37_terms_40, g32p_row37_terms_41, g32p_row37_terms_42, g32p_row37_terms_43, g32p_row37_terms_44, g32p_row37_terms_45, g32p_row37_terms_46, g32p_row37_terms_47]

def g32p_row37_pairingQuotients : Fin 48 → List ℤ :=
  ![[], [], [144, 168, 48, -72, -96, -48], [], [], [0, -24, 0, -24, 0, 48], [], [0, 24, 0, 24, 0, -48], [], [], [], [0, -24, 0, -24, 0, 48], [], [], [], [], [], [], [144, 168, 48, -72, -96, -48], [], [0, 24, 0, 24, 0, -48], [], [0, -24, 0, -24, 0, 48], [], [0, -24, 0, -24, 0, 48], [], [], [], [], [], [0, -24, 0, -24, 0, 48], [], [], [], [], [144, 168, 48, -72, -96, -48], [144, 168, 48, -72, -96, -48], [144, 168, 48, -72, -96, -48], [], [], [0, 24, 0, 24, 0, -48], [-144, -168, -48, 72, 96, 48], [-144, -168, -48, 72, 96, 48], [], [], [-96, -72, 0, 24], [], [-144, -144]]

def g32p_row37_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 1, 1, 0]

def g32p_row37_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 1, 0, 2]

theorem g32p_row37_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 144 (g32p_row37_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row37_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row37_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row37_pairing_0
  · exact g32p_row37_pairing_1
  · exact g32p_row37_pairing_2
  · exact g32p_row37_pairing_3
  · exact g32p_row37_pairing_4
  · exact g32p_row37_pairing_5
  · exact g32p_row37_pairing_6
  · exact g32p_row37_pairing_7
  · exact g32p_row37_pairing_8
  · exact g32p_row37_pairing_9
  · exact g32p_row37_pairing_10
  · exact g32p_row37_pairing_11
  · exact g32p_row37_pairing_12
  · exact g32p_row37_pairing_13
  · exact g32p_row37_pairing_14
  · exact g32p_row37_pairing_15
  · exact g32p_row37_pairing_16
  · exact g32p_row37_pairing_17
  · exact g32p_row37_pairing_18
  · exact g32p_row37_pairing_19
  · exact g32p_row37_pairing_20
  · exact g32p_row37_pairing_21
  · exact g32p_row37_pairing_22
  · exact g32p_row37_pairing_23
  · exact g32p_row37_pairing_24
  · exact g32p_row37_pairing_25
  · exact g32p_row37_pairing_26
  · exact g32p_row37_pairing_27
  · exact g32p_row37_pairing_28
  · exact g32p_row37_pairing_29
  · exact g32p_row37_pairing_30
  · exact g32p_row37_pairing_31
  · exact g32p_row37_pairing_32
  · exact g32p_row37_pairing_33
  · exact g32p_row37_pairing_34
  · exact g32p_row37_pairing_35
  · exact g32p_row37_pairing_36
  · exact g32p_row37_pairing_37
  · exact g32p_row37_pairing_38
  · exact g32p_row37_pairing_39
  · exact g32p_row37_pairing_40
  · exact g32p_row37_pairing_41
  · exact g32p_row37_pairing_42
  · exact g32p_row37_pairing_43

theorem g32p_row37_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 144 (g32p_row37_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row37_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row37_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row37_pairing_44
  · exact g32p_row37_pairing_45
  · exact g32p_row37_pairing_46
  · exact g32p_row37_pairing_47

theorem g32p_row37_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 144)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row37_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row37_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 37 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row37_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row37_freeCoordinates g32p_row37_quaternionicMultiplicities
    g32p_row37_pairingTerms [1, -1, 1] g32p_row37_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row37_pairingFree)
    (by rw [horder]; exact g32p_row37_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
