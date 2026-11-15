import HodgeLean.Foundations.Program.G32PropFourSixPacked0550
import HodgeLean.Foundations.Program.G32PropFourSixPacked0553
import HodgeLean.Foundations.Program.G32PropFourSixPacked0556
import HodgeLean.Foundations.Program.G32PropFourSixPacked0559
import HodgeLean.Foundations.Program.G32PropFourSixPacked0562
import HodgeLean.Foundations.Program.G32PropFourSixPacked0565
import HodgeLean.Foundations.Program.G32PropFourSixPacked0569
import HodgeLean.Foundations.Program.G32PropFourSixPacked0572
import HodgeLean.Foundations.Program.G32PropFourSixPacked0576
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0802
import HodgeLean.Foundations.Program.G32PropFourSixPacked0807
import HodgeLean.Foundations.Program.G32PropFourSixPacked0813
import HodgeLean.Foundations.Program.G32PropFourSixPacked0909
import HodgeLean.Foundations.Program.G32PropFourSixPacked0913
import HodgeLean.Foundations.Program.G32PropFourSixPacked0918
import HodgeLean.Foundations.Program.G32PropFourSixPacked0923
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness36

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Restriction coordinates for supplier row 28.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 28. -/
theorem g32cc_row28_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 28 ∧
      papersA τ τbar θ g32p_row28_finiteSupplier.H (g32p_complexCharacter g32p_row28_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row28_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row28 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 28 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 28 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row28_finiteSupplier, (g32p_complexCharacter g32p_row28_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row28_finiteSupplier_table,
    g32cc_row28_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 29.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 29. -/
theorem g32cc_row29_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 29 ∧
      papersA τ τbar θ g32p_row29_finiteSupplier.H (g32p_complexCharacter g32p_row29_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row29_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row29 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 29 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 29 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row29_finiteSupplier, (g32p_complexCharacter g32p_row29_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row29_finiteSupplier_table,
    g32cc_row29_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 30.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 30. -/
theorem g32cc_row30_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 30 ∧
      papersA τ τbar θ g32p_row30_finiteSupplier.H (g32p_complexCharacter g32p_row30_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row30_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row30 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 30 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 30 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row30_finiteSupplier, (g32p_complexCharacter g32p_row30_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row30_finiteSupplier_table,
    g32cc_row30_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 31.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 31. -/
theorem g32cc_row31_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 31 ∧
      papersA τ τbar θ g32p_row31_finiteSupplier.H (g32p_complexCharacter g32p_row31_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row31_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row31 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 31 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 31 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row31_finiteSupplier, (g32p_complexCharacter g32p_row31_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row31_finiteSupplier_table,
    g32cc_row31_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 32.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 32. -/
theorem g32cc_row32_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 32 ∧
      papersA τ τbar θ g32p_row32_finiteSupplier.H (g32p_complexCharacter g32p_row32_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row32_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row32 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 32 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 32 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row32_finiteSupplier, (g32p_complexCharacter g32p_row32_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row32_finiteSupplier_table,
    g32cc_row32_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 33.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 33. -/
theorem g32cc_row33_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 33 ∧
      papersA τ τbar θ g32p_row33_finiteSupplier.H (g32p_complexCharacter g32p_row33_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row33_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row33 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 33 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 33 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row33_finiteSupplier, (g32p_complexCharacter g32p_row33_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row33_finiteSupplier_table,
    g32cc_row33_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 34.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 34. -/
theorem g32cc_row34_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 34 ∧
      papersA τ τbar θ g32p_row34_finiteSupplier.H (g32p_complexCharacter g32p_row34_finiteSupplier) =
        g32SparseVec v.coords := by
  have hlabel (g : g32p_G) : g32p_integrationLabel g = D.label g :=
    g32p_integrationLabel_of_isConj (hconj g)
  exact g32p_row34_integrationRestriction τ τbar θ
    (fun j g => (ht j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hb j g).trans (congrArg _ (hlabel g).symm))
    (fun j g => (hq j g).trans (congrArg _ (hlabel g).symm))

theorem g32cc_row34 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 34 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 34 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row34_finiteSupplier, (g32p_complexCharacter g32p_row34_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row34_finiteSupplier_table,
    g32cc_row34_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 35.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 35. -/
theorem g32cc_row35_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 35 ∧
      papersA τ τbar θ g32p_row35_finiteSupplier.H (g32p_complexCharacter g32p_row35_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row35_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row35 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 35 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 35 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row35_finiteSupplier, (g32p_complexCharacter g32p_row35_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row35_finiteSupplier_table,
    g32cc_row35_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 36.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 36. -/
theorem g32cc_row36_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 36 ∧
      papersA τ τbar θ g32p_row36_finiteSupplier.H (g32p_complexCharacter g32p_row36_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row36_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row36 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 36 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 36 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row36_finiteSupplier, (g32p_complexCharacter g32p_row36_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row36_finiteSupplier_table,
    g32cc_row36_aux D hrep hconj τ τbar θ ht hb hq⟩


end HodgeLean.Foundations.Program
