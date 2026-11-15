import HodgeLean.Foundations.Program.G32PropFourSixPacked0579
import HodgeLean.Foundations.Program.G32PropFourSixPacked0582
import HodgeLean.Foundations.Program.G32PropFourSixPacked0585
import HodgeLean.Foundations.Program.G32PropFourSixPacked0588
import HodgeLean.Foundations.Program.G32PropFourSixPacked0591
import HodgeLean.Foundations.Program.G32PropFourSixPacked0594
import HodgeLean.Foundations.Program.G32PropFourSixPacked0598
import HodgeLean.Foundations.Program.G32PropFourSixPacked0601
import HodgeLean.Foundations.Program.G32PropFourSixPacked0604
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0943
import HodgeLean.Foundations.Program.G32PropFourSixPacked0956
import HodgeLean.Foundations.Program.G32PropFourSixPacked0969
import HodgeLean.Foundations.Program.G32PropFourSixPacked0973
import HodgeLean.Foundations.Program.G32PropFourSixPacked0978
import HodgeLean.Foundations.Program.G32PropFourSixPacked0983
import HodgeLean.Foundations.Program.G32PropFourSixPacked0988

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Restriction coordinates for supplier row 37.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 37. -/
theorem g32cc_row37_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 37 ∧
      papersA τ τbar θ g32p_row37_finiteSupplier.H (g32p_complexCharacter g32p_row37_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row37_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row37 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 37 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 37 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row37_finiteSupplier, (g32p_complexCharacter g32p_row37_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row37_finiteSupplier_table,
    g32cc_row37_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 38.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 38. -/
theorem g32cc_row38_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 38 ∧
      papersA τ τbar θ g32p_row38_finiteSupplier.H (g32p_complexCharacter g32p_row38_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row38_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row38 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 38 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 38 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row38_finiteSupplier, (g32p_complexCharacter g32p_row38_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row38_finiteSupplier_table,
    g32cc_row38_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 39.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 39. -/
theorem g32cc_row39_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 39 ∧
      papersA τ τbar θ g32p_row39_finiteSupplier.H (g32p_complexCharacter g32p_row39_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row39_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row39 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 39 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 39 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row39_finiteSupplier, (g32p_complexCharacter g32p_row39_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row39_finiteSupplier_table,
    g32cc_row39_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 40.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 40. -/
theorem g32cc_row40_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 40 ∧
      papersA τ τbar θ g32p_row40_finiteSupplier.H (g32p_complexCharacter g32p_row40_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row40_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row40 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 40 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 40 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row40_finiteSupplier, (g32p_complexCharacter g32p_row40_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row40_finiteSupplier_table,
    g32cc_row40_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 41.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 41. -/
theorem g32cc_row41_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 41 ∧
      papersA τ τbar θ g32p_row41_finiteSupplier.H (g32p_complexCharacter g32p_row41_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row41_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row41 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 41 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 41 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row41_finiteSupplier, (g32p_complexCharacter g32p_row41_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row41_finiteSupplier_table,
    g32cc_row41_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 42.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 42. -/
theorem g32cc_row42_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 42 ∧
      papersA τ τbar θ g32p_row42_finiteSupplier.H (g32p_complexCharacter g32p_row42_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row42_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row42 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 42 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 42 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row42_finiteSupplier, (g32p_complexCharacter g32p_row42_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row42_finiteSupplier_table,
    g32cc_row42_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 43.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 43. -/
theorem g32cc_row43_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 43 ∧
      papersA τ τbar θ g32p_row43_finiteSupplier.H (g32p_complexCharacter g32p_row43_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row43_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row43 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 43 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 43 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row43_finiteSupplier, (g32p_complexCharacter g32p_row43_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row43_finiteSupplier_table,
    g32cc_row43_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 44.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 44. -/
theorem g32cc_row44_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 44 ∧
      papersA τ τbar θ g32p_row44_finiteSupplier.H (g32p_complexCharacter g32p_row44_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row44_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row44 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 44 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 44 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row44_finiteSupplier, (g32p_complexCharacter g32p_row44_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row44_finiteSupplier_table,
    g32cc_row44_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 45.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 45. -/
theorem g32cc_row45_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 45 ∧
      papersA τ τbar θ g32p_row45_finiteSupplier.H (g32p_complexCharacter g32p_row45_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row45_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row45 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 45 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 45 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row45_finiteSupplier, (g32p_complexCharacter g32p_row45_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row45_finiteSupplier_table,
    g32cc_row45_aux D hrep hconj τ τbar θ ht hb hq⟩


end HodgeLean.Foundations.Program
