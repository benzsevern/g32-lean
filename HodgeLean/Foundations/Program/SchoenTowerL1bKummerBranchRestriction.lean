import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSections
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBranchUnits

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The generated subfield for the retained section map is independent of the affine neighborhood. -/
theorem s2v_l1b_generic_section_generated_subfield
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    (U : X.affineOpens) [Nonempty U.1]
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) (t : K) :
    letI := κ.hom.toAlgebra
    Subfield.closure
      (Set.range (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) =
      (IntermediateField.adjoin X.functionField {t}).toSubfield := by
  letI := κ.hom.toAlgebra
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  rw [s2v_l1b_section_map_of_generic_factor X η κ hη U.1 hU hηU]
  exact s2v_l1b_fraction_field_generator (R := Γ(X, U)) (F := X.functionField) t

/-- Affine restriction along the actual generic map preserves every generated subfield. -/
theorem s2v_l1b_affine_generated_subfield_eq
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    (U V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1)
    (hV : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V.1)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) (hηV : ⊤ ≤ η ⁻¹ᵁ V.1) (t : K) :
    Subfield.closure
      (Set.range (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) =
    Subfield.closure
      (Set.range (η.appLE V.1 ⊤ hηV ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) := by
  exact (s2v_l1b_generic_section_generated_subfield X η κ hη U hU hηU t).trans
    (s2v_l1b_generic_section_generated_subfield X η κ hη V hV hηV t).symm

/-- A local branch equation and its field generation persist on smaller affine neighborhoods. -/
theorem s2v_l1b_affine_branch_data_restrict
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    (U V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (hVU : V.1 ≤ U.1)
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1)
    (hV : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V.1)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) (hηV : ⊤ ≤ η ⁻¹ᵁ V.1)
    {J : Type*} [Fintype J] (f : J → Γ(X, U)) (g : J → Γ(X, V)) (n : J → ℕ)
    (hfg : ∀ j, Ideal.span {(X.presheaf.map (homOfLE hVU).op) (f j)} =
      Ideal.span {g j}) (t : K) (m : ℕ) (ε : Γ(X, U)ˣ)
    (hgen : Subfield.closure
      (Set.range (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) = ⊤)
    (ht : t ^ m = (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom) (ε : Γ(X, U)) *
      ∏ j, (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom) (f j) ^ n j) :
    ∃ ε' : Γ(X, V)ˣ,
      Subfield.closure
        (Set.range (η.appLE V.1 ⊤ hηV ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) = ⊤ ∧
      t ^ m = (η.appLE V.1 ⊤ hηV ≫ (Scheme.ΓSpecIso (.of K)).hom) (ε' : Γ(X, V)) *
        ∏ j, (η.appLE V.1 ⊤ hηV ≫ (Scheme.ΓSpecIso (.of K)).hom) (g j) ^ n j := by
  let ρ := (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
  let ρ' := (η.appLE V.1 ⊤ hηV ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
  let φ := (X.presheaf.map (homOfLE hVU).op).hom
  have hρ : ρ'.comp φ = ρ := by
    change (X.presheaf.map (homOfLE hVU).op ≫
      η.appLE V.1 ⊤ hηV ≫ (Scheme.ΓSpecIso (.of K)).hom).hom = _
    rw [Scheme.Hom.map_appLE_assoc]
  obtain ⟨ε', hε'⟩ := s2v_l1b_branch_equation_restrict φ ρ ρ' hρ f g n hfg t m ε ht
  refine ⟨ε', ?_, hε'⟩
  rw [← s2v_l1b_affine_generated_subfield_eq X η κ hη U V hU hV hηU hηV t]
  exact hgen

end HodgeLean.Foundations.Program
