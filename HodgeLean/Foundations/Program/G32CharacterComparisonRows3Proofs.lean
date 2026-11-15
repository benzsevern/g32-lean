import HodgeLean.Foundations.Program.G32PropFourSixPacked0518
import HodgeLean.Foundations.Program.G32PropFourSixPacked0522
import HodgeLean.Foundations.Program.G32PropFourSixPacked0526
import HodgeLean.Foundations.Program.G32PropFourSixPacked0530
import HodgeLean.Foundations.Program.G32PropFourSixPacked0533
import HodgeLean.Foundations.Program.G32PropFourSixPacked0537
import HodgeLean.Foundations.Program.G32PropFourSixPacked0540
import HodgeLean.Foundations.Program.G32PropFourSixPacked0544
import HodgeLean.Foundations.Program.G32PropFourSixPacked0547
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0745
import HodgeLean.Foundations.Program.G32PropFourSixPacked0758
import HodgeLean.Foundations.Program.G32PropFourSixPacked0761
import HodgeLean.Foundations.Program.G32PropFourSixPacked0764
import HodgeLean.Foundations.Program.G32PropFourSixPacked0781
import HodgeLean.Foundations.Program.G32PropFourSixPacked0784
import HodgeLean.Foundations.Program.G32PropFourSixPacked0788
import HodgeLean.Foundations.Program.G32PropFourSixPacked0792
import HodgeLean.Foundations.Program.G32PropFourSixPacked0797

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Restriction coordinates for supplier row 19.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 19. -/
theorem g32cc_row19_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 19 ∧
      papersA τ τbar θ g32p_row19_finiteSupplier.H (g32p_complexCharacter g32p_row19_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row19_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row19 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 19 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 19 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row19_finiteSupplier, (g32p_complexCharacter g32p_row19_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row19_finiteSupplier_table,
    g32cc_row19_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 20.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 20. -/
theorem g32cc_row20_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 20 ∧
      papersA τ τbar θ g32p_row20_finiteSupplier.H (g32p_complexCharacter g32p_row20_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row20_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row20 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 20 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 20 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row20_finiteSupplier, (g32p_complexCharacter g32p_row20_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row20_finiteSupplier_table,
    g32cc_row20_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 21.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 21. -/
theorem g32cc_row21_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 21 ∧
      papersA τ τbar θ g32p_row21_finiteSupplier.H (g32p_complexCharacter g32p_row21_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row21_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row21 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 21 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 21 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row21_finiteSupplier, (g32p_complexCharacter g32p_row21_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row21_finiteSupplier_table,
    g32cc_row21_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 22.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 22. -/
theorem g32cc_row22_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 22 ∧
      papersA τ τbar θ g32p_row22_finiteSupplier.H (g32p_complexCharacter g32p_row22_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row22_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row22 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 22 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 22 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row22_finiteSupplier, (g32p_complexCharacter g32p_row22_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row22_finiteSupplier_table,
    g32cc_row22_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 23.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 23. -/
theorem g32cc_row23_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 23 ∧
      papersA τ τbar θ g32p_row23_finiteSupplier.H (g32p_complexCharacter g32p_row23_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row23_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row23 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 23 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 23 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row23_finiteSupplier, (g32p_complexCharacter g32p_row23_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row23_finiteSupplier_table,
    g32cc_row23_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 24.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 24. -/
theorem g32cc_row24_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 24 ∧
      papersA τ τbar θ g32p_row24_finiteSupplier.H (g32p_complexCharacter g32p_row24_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row24_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row24 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 24 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 24 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row24_finiteSupplier, (g32p_complexCharacter g32p_row24_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row24_finiteSupplier_table,
    g32cc_row24_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 25.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 25. -/
theorem g32cc_row25_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 25 ∧
      papersA τ τbar θ g32p_row25_finiteSupplier.H (g32p_complexCharacter g32p_row25_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row25_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row25 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 25 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 25 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row25_finiteSupplier, (g32p_complexCharacter g32p_row25_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row25_finiteSupplier_table,
    g32cc_row25_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 26.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 26. -/
theorem g32cc_row26_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 26 ∧
      papersA τ τbar θ g32p_row26_finiteSupplier.H (g32p_complexCharacter g32p_row26_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row26_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row26 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 26 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 26 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row26_finiteSupplier, (g32p_complexCharacter g32p_row26_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row26_finiteSupplier_table,
    g32cc_row26_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 27.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 27. -/
theorem g32cc_row27_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 27 ∧
      papersA τ τbar θ g32p_row27_finiteSupplier.H (g32p_complexCharacter g32p_row27_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row27_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row27 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 27 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 27 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row27_finiteSupplier, (g32p_complexCharacter g32p_row27_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row27_finiteSupplier_table,
    g32cc_row27_aux D hrep hconj τ τbar θ ht hb hq⟩


end HodgeLean.Foundations.Program
