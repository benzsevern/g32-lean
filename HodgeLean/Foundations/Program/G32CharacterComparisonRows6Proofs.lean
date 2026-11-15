import HodgeLean.Foundations.Program.G32PropFourSixPacked0607
import HodgeLean.Foundations.Program.G32PropFourSixPacked0610
import HodgeLean.Foundations.Program.G32PropFourSixPacked0613
import HodgeLean.Foundations.Program.G32PropFourSixPacked0616
import HodgeLean.Foundations.Program.G32PropFourSixPacked0619
import HodgeLean.Foundations.Program.G32PropFourSixPacked0622
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0993
import HodgeLean.Foundations.Program.G32PropFourSixPacked0998
import HodgeLean.Foundations.Program.G32PropFourSixPacked1000
import HodgeLean.Foundations.Program.G32PropFourSixPacked1006
import HodgeLean.Foundations.Program.G32PropFourSixPacked1014
import HodgeLean.Foundations.Program.G32PropFourSixPacked1022

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Restriction coordinates for supplier row 46.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 46. -/
theorem g32cc_row46_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 46 ∧
      papersA τ τbar θ g32p_row46_finiteSupplier.H (g32p_complexCharacter g32p_row46_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row46_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row46 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 46 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 46 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row46_finiteSupplier, (g32p_complexCharacter g32p_row46_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row46_finiteSupplier_table,
    g32cc_row46_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 47.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 47. -/
theorem g32cc_row47_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 47 ∧
      papersA τ τbar θ g32p_row47_finiteSupplier.H (g32p_complexCharacter g32p_row47_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row47_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row47 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 47 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 47 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row47_finiteSupplier, (g32p_complexCharacter g32p_row47_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row47_finiteSupplier_table,
    g32cc_row47_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 48.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 48. -/
theorem g32cc_row48_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 48 ∧
      papersA τ τbar θ g32p_row48_finiteSupplier.H (g32p_complexCharacter g32p_row48_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row48_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row48 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 48 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 48 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row48_finiteSupplier, (g32p_complexCharacter g32p_row48_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row48_finiteSupplier_table,
    g32cc_row48_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 49.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 49. -/
theorem g32cc_row49_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 49 ∧
      papersA τ τbar θ g32p_row49_finiteSupplier.H (g32p_complexCharacter g32p_row49_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row49_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row49 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 49 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 49 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row49_finiteSupplier, (g32p_complexCharacter g32p_row49_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row49_finiteSupplier_table,
    g32cc_row49_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 50.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 50. -/
theorem g32cc_row50_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 50 ∧
      papersA τ τbar θ g32p_row50_finiteSupplier.H (g32p_complexCharacter g32p_row50_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row50_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row50 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 50 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 50 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row50_finiteSupplier, (g32p_complexCharacter g32p_row50_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row50_finiteSupplier_table,
    g32cc_row50_aux D hrep hconj τ τbar θ ht hb hq⟩

/-- Restriction coordinates for supplier row 51.
Source: G32 v0.16, Appendix B, Tables 1 and 2, row 51. -/
theorem g32cc_row51_aux (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) :
    ∃ v ∈ g32VectorTable, v.i = 51 ∧
      papersA τ τbar θ g32p_row51_finiteSupplier.H (g32p_complexCharacter g32p_row51_finiteSupplier) =
        g32SparseVec v.coords := by
  have hl (g : g32p_G) : D.label g = g32p_integrationLabel g :=
    (g32p_integrationLabel_of_isConj (hconj g)).symm
  exact g32p_row51_integrationRestriction τ τbar θ
    (fun j g => by simpa only [hl g] using ht j g)
    (fun j g => by simpa only [hl g] using hb j g)
    (fun j g => by simpa only [hl g] using hq j g)

theorem g32cc_row51 (D : g32p_familiesClassData)
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
      (∃ r ∈ g32WitnessTable, r.i = 51 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = 51 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  exact ⟨g32p_row51_finiteSupplier, (g32p_complexCharacter g32p_row51_finiteSupplier),
    g32p_complexCharacter_apply _, g32p_row51_finiteSupplier_table,
    g32cc_row51_aux D hrep hconj τ τbar θ ht hb hq⟩


end HodgeLean.Foundations.Program
