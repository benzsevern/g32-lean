import HodgeLean.Foundations.Program.G32PropFourSixPacked0624

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32cc_row01_from_classes
    (classify : g32p_determinantSupplier.H → Fin 102)
    (hcard : ∀ a, Nat.card {h : g32p_determinantSupplier.H // classify h = a} =
      g32p_row01_restrictionSizes a)
    (hchar : ∀ h, (g32p_complexCharacter g32p_determinantSupplier h⁻¹ : ℂ) =
      g32p_root 3 ^ g32p_row01_restrictionExponents (classify h))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ j (h : g32p_determinantSupplier.H), g32p_restrictionTrace τ τbar θ j h =
      HurwitzPrymRex_ev g32h_omega (g32p_row01_restrictionCoefficients j (classify h))) :
    ∃ v ∈ g32VectorTable, v.i = 1 ∧
      papersA τ τbar θ g32p_determinantSupplier.H (g32p_complexCharacter g32p_determinantSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_determinantSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        (g32p_complexCharacter g32p_determinantSupplier h⁻¹ : ℂ)) =
      ((g32p_row01_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 3 ^ (3 / 3)) x.2.1 * g32p_root 3 ^ x.2.2)).sum :=
    g32p_restriction_class_sums g32p_determinantSupplier
    classify g32p_row01_restrictionSizes g32p_row01_restrictionExponents
    (fun a => (Nat.card_eq_fintype_card).symm.trans (hcard a)) hchar τ τbar θ
    g32p_row01_pairingTerms g32p_row01_restrictionCoefficients g32p_row01_restrictionLabels
    (g32p_restriction_root_omega 3 (by decide)) htrace
    g32p_row01_restrictionDecode g32p_row01_restrictionTerms j
  apply g32p_row01_restriction_of_sums H τ τbar θ _ (g32p_root 3)
    (g32p_root_primitive g32p_determinantSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_determinantSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩

theorem g32cc_row01_from_family
    (classify : g32p_G → Fin 102)
    (hcard : ∀ c, Nat.card {g : g32p_G // classify g = c} = g32p_literalSize c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (classify g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 1 ∧
      papersA τ τbar θ g32p_determinantSupplier.H
        (g32p_complexCharacter g32p_determinantSupplier) = g32SparseVec v.coords := by
  apply g32cc_row01_from_classes (fun h => classify h)
  · intro c
    rw [Nat.card_congr (g32p_row01_classFiberEquiv classify c), hcard,
      g32p_row01_restrictionSizes_literal]
  · exact g32p_row01_restrictionCharacter_of_class classify hconj
  · intro j h
    rw [g32p_row01_restrictionFamily]
    have hc : g32p_row01_restrictionClasses (classify h) = classify h := by
      generalize classify h = c
      revert c
      decide +kernel
    rw [hc]
    exact g32p_restriction_family_trace τ τbar θ _ _
      (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


end HodgeLean.Foundations.Program
