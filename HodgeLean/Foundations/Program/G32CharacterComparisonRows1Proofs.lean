import HodgeLean.Foundations.Program.G32CharacterComparisonRowOneBridge
import HodgeLean.Foundations.Program.G32PropFourSixPacked0485
import HodgeLean.Foundations.Program.G32PropFourSixPacked0482
import HodgeLean.Foundations.Program.G32PropFourSixPacked0479
import HodgeLean.Foundations.Program.G32PropFourSixPacked0475
import HodgeLean.Foundations.Program.G32PropFourSixPacked0472
import HodgeLean.Foundations.Program.G32PropFourSixPacked0469
import HodgeLean.Foundations.Program.G32PropFourSixPacked0462
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32CharacterComparisonBridge
import HodgeLean.Foundations.Program.G32PropFourSixPacked0008
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixPacked0641
import HodgeLean.Foundations.Program.G32PropFourSixPacked0644
import HodgeLean.Foundations.Program.G32PropFourSixPacked0649
import HodgeLean.Foundations.Program.G32PropFourSixPacked0661
import HodgeLean.Foundations.Program.G32PropFourSixPacked0664
import HodgeLean.Foundations.Program.G32PropFourSixPacked0668
import HodgeLean.Foundations.Program.G32PropFourSixPacked0673

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Restriction coordinates for supplier row 1.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 1. -/
theorem g32cc_row01_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 1 ∧
      papersA τ τbar θ g32p_determinantSupplier.H (g32p_complexCharacter g32p_determinantSupplier) =
        g32SparseVec v.coords := by
  apply g32cc_row01_from_family g32p_integrationLabel
  · intro c
    simpa only [g32p_integrationLabel] using
      (Classical.choose_spec g32p_literal_class_fibres).2 c
  · exact g32p_integrationLabel_conj
  · simpa only [g32cc_label_eq D hconj, g32p_comparisonAssembly_ordering.1] using ht
  · simpa only [g32cc_label_eq D hconj, g32p_comparisonAssembly_ordering.2.1] using hb
  · simpa only [g32cc_label_eq D hconj, g32p_comparisonAssembly_ordering.2.2] using hq

theorem g32cc_row01 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 1 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 1 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_determinantSupplier, (g32p_complexCharacter g32p_determinantSupplier),
    g32p_complexCharacter_apply _, g32p_determinantSupplier_table,
    g32cc_row01_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 2.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 2. -/
theorem g32cc_row02_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 2 ∧
      papersA τ τbar θ g32p_row02_finiteSupplier.H (g32p_complexCharacter g32p_row02_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row02_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row02 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 2 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 2 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row02_finiteSupplier, (g32p_complexCharacter g32p_row02_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row02_finiteSupplier_table,
    g32cc_row02_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 3.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 3. -/
theorem g32cc_row03_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 3 ∧
      papersA τ τbar θ g32p_row03_finiteSupplier.H (g32p_complexCharacter g32p_row03_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row03_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row03 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 3 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 3 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row03_finiteSupplier, (g32p_complexCharacter g32p_row03_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row03_finiteSupplier_table,
    g32cc_row03_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 4.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 4. -/
theorem g32cc_row04_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 4 ∧
      papersA τ τbar θ g32p_row04_finiteSupplier.H (g32p_complexCharacter g32p_row04_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row04_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row04 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 4 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 4 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row04_finiteSupplier, (g32p_complexCharacter g32p_row04_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row04_finiteSupplier_table,
    g32cc_row04_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 5.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 5. -/
theorem g32cc_row05_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 5 ∧
      papersA τ τbar θ g32p_row05_finiteSupplier.H (g32p_complexCharacter g32p_row05_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row05_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row05 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 5 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 5 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row05_finiteSupplier, (g32p_complexCharacter g32p_row05_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row05_finiteSupplier_table,
    g32cc_row05_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 6.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 6. -/
theorem g32cc_row06_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 6 ∧
      papersA τ τbar θ g32p_row06_finiteSupplier.H (g32p_complexCharacter g32p_row06_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row06_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row06 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 6 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 6 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row06_finiteSupplier, (g32p_complexCharacter g32p_row06_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row06_finiteSupplier_table,
    g32cc_row06_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 7.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 7. -/
theorem g32cc_row07_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 7 ∧
      papersA τ τbar θ g32p_row07_finiteSupplier.H (g32p_complexCharacter g32p_row07_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row07_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row07 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 7 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 7 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row07_finiteSupplier, (g32p_complexCharacter g32p_row07_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row07_finiteSupplier_table,
    g32cc_row07_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 8.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 8. -/
theorem g32cc_row08_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 8 ∧
      papersA τ τbar θ g32p_row08_finiteSupplier.H (g32p_complexCharacter g32p_row08_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row08_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row08 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 8 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 8 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row08_finiteSupplier, (g32p_complexCharacter g32p_row08_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row08_finiteSupplier_table,
    g32cc_row08_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 9.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 9. -/
theorem g32cc_row09_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 9 ∧
      papersA τ τbar θ g32p_row09_finiteSupplier.H (g32p_complexCharacter g32p_row09_finiteSupplier) =
        g32SparseVec v.coords := by
  apply g32p_row09_integrationRestriction τ τbar θ
  · simpa only [g32cc_label_eq D hconj] using ht
  · simpa only [g32cc_label_eq D hconj] using hb
  · simpa only [g32cc_label_eq D hconj] using hq

theorem g32cc_row09 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 9 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 9 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row09_finiteSupplier, (g32p_complexCharacter g32p_row09_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row09_finiteSupplier_table,
    g32cc_row09_aux D hrep hconj τ τbar θ ht hb hq⟩


end HodgeLean.Foundations.Program
