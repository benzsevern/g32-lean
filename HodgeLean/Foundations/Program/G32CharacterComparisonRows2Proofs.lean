import HodgeLean.Foundations.Program.G32PropFourSixPacked0511
import HodgeLean.Foundations.Program.G32PropFourSixPacked0506
import HodgeLean.Foundations.Program.G32PropFourSixPacked0503
import HodgeLean.Foundations.Program.G32PropFourSixPacked0500
import HodgeLean.Foundations.Program.G32PropFourSixPacked0497
import HodgeLean.Foundations.Program.G32PropFourSixPacked0494
import HodgeLean.Foundations.Program.G32PropFourSixPacked0491
import HodgeLean.Foundations.Program.G32CharacterComparisonBridge
import HodgeLean.Foundations.Program.G32PropFourSixPacked0488
import HodgeLean.Foundations.Program.G32PropFourSixPacked0514
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0678
import HodgeLean.Foundations.Program.G32PropFourSixPacked0683
import HodgeLean.Foundations.Program.G32PropFourSixPacked0688
import HodgeLean.Foundations.Program.G32PropFourSixPacked0693
import HodgeLean.Foundations.Program.G32PropFourSixPacked0742
import HodgeLean.Foundations.Program.G32PropFourSixPacked1077
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow16Exponents

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Restriction coordinates for supplier row 10.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 10. -/
theorem g32cc_row10_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 10 ∧
      papersA τ τbar θ g32p_row10_finiteSupplier.H (g32p_complexCharacter g32p_row10_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row10_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row10 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 10 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 10 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row10_finiteSupplier, (g32p_complexCharacter g32p_row10_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row10_finiteSupplier_table,
    g32cc_row10_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 11.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 11. -/
theorem g32cc_row11_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 11 ∧
      papersA τ τbar θ g32p_row11_finiteSupplier.H (g32p_complexCharacter g32p_row11_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row11_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row11 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 11 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 11 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row11_finiteSupplier, (g32p_complexCharacter g32p_row11_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row11_finiteSupplier_table,
    g32cc_row11_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 12.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 12. -/
theorem g32cc_row12_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 12 ∧
      papersA τ τbar θ g32p_row12_finiteSupplier.H (g32p_complexCharacter g32p_row12_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row12_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row12 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 12 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 12 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row12_finiteSupplier, (g32p_complexCharacter g32p_row12_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row12_finiteSupplier_table,
    g32cc_row12_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 13.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 13. -/
theorem g32cc_row13_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 13 ∧
      papersA τ τbar θ g32p_row13_finiteSupplier.H (g32p_complexCharacter g32p_row13_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row13_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row13 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 13 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 13 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row13_finiteSupplier, (g32p_complexCharacter g32p_row13_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row13_finiteSupplier_table,
    g32cc_row13_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 14.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 14. -/
theorem g32cc_row14_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 14 ∧
      papersA τ τbar θ g32p_row14_finiteSupplier.H (g32p_complexCharacter g32p_row14_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row14_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row14 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 14 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 14 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row14_finiteSupplier, (g32p_complexCharacter g32p_row14_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row14_finiteSupplier_table,
    g32cc_row14_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 15.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 15. -/
theorem g32cc_row15_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 15 ∧
      papersA τ τbar θ g32p_row15_finiteSupplier.H (g32p_complexCharacter g32p_row15_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row15_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row15 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 15 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 15 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row15_finiteSupplier, (g32p_complexCharacter g32p_row15_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row15_finiteSupplier_table,
    g32cc_row15_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 16.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 16. -/
theorem g32cc_row16_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 16 ∧
      papersA τ τbar θ g32p_row16_finiteSupplier.H (g32p_complexCharacter g32p_row16_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row16_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row16 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 16 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 16 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row16_finiteSupplier, (g32p_complexCharacter g32p_row16_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row16_finiteSupplier_table,
    g32cc_row16_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 17.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 17. -/
theorem g32cc_row17_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 17 ∧
      papersA τ τbar θ g32p_row17_finiteSupplier.H (g32p_complexCharacter g32p_row17_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row17_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row17 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 17 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 17 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row17_finiteSupplier, (g32p_complexCharacter g32p_row17_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row17_finiteSupplier_table,
    g32cc_row17_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 18.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 18. -/
theorem g32cc_row18_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 18 ∧
      papersA τ τbar θ g32p_row18_finiteSupplier.H (g32p_complexCharacter g32p_row18_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row18_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row18 (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 18 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 18 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row18_finiteSupplier, (g32p_complexCharacter g32p_row18_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row18_finiteSupplier_table,
    g32cc_row18_aux D hrep hconj τ τbar θ ht hb hq⟩


end HodgeLean.Foundations.Program
