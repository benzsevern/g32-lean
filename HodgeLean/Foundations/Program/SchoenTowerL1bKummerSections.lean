import HodgeLean.Foundations.Program.SchoenTowerL1bKummerField
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback along the generic point is the canonical section germ. -/
theorem s2v_l1b_generic_section_germ (X : Scheme) [IsIntegral X]
    (U : X.Opens) [Nonempty U]
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) :
    (X.fromSpecStalk (genericPoint X)).appLE U ⊤ hU ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField U := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp,
    homOfLE_refl, op_id]
  rw [(Spec (X.presheaf.stalk (genericPoint X))).presheaf.map_id]
  simp only [Category.id_comp]
  change X.presheaf.germ U (genericPoint X) hx ≫
    (Scheme.ΓSpecIso X.functionField).inv ≫ (Scheme.ΓSpecIso X.functionField).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

/-- A generic factorization identifies the retained section map with the induced field embedding. -/
theorem s2v_l1b_section_map_of_generic_factor
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    (U : X.Opens) [Nonempty U]
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U) :
    η.appLE U ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom =
      X.germToFunctionField U ≫ κ := by
  subst η
  rw [← s2v_l1b_generic_section_germ X U hU, Category.assoc,
    ← Scheme.ΓSpecIso_naturality]
  change _ = (X.fromSpecStalk (genericPoint X)).appLE U ⊤ hU ≫
    ((Spec.map κ).appLE ⊤ ⊤ (by simp only [TopologicalSpace.Opens.map_top]; rfl) ≫ _)
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]

/-- Cyclic Kummer generation transfers to the actual section pullback along a compatible generic point. -/
theorem s2v_l1b_generic_cyclic_section_generator
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    [Algebra X.functionField K] [FiniteDimensional X.functionField K]
    [IsGalois X.functionField K] [IsCyclic (K ≃ₐ[X.functionField] K)]
    (η : Spec (.of K) ⟶ X)
    (hη : Spec.map (CommRingCat.ofHom (algebraMap X.functionField K)) ≫
      X.fromSpecStalk (genericPoint X) = η)
    (U : X.affineOpens) [Nonempty U.1]
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U.1)
    (hroots : (primitiveRoots (Module.finrank X.functionField K) X.functionField).Nonempty) :
    let ρ := (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
    ∃ t : K, t ≠ 0 ∧ Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ Module.finrank X.functionField K ∈ Set.range (algebraMap X.functionField K) := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  have hρ := s2v_l1b_section_map_of_generic_factor X η
    (CommRingCat.ofHom (algebraMap X.functionField K)) hη U.1 hU hηU
  dsimp only
  rw [hρ]
  exact s2v_l1b_cyclic_section_generator (R := Γ(X, U)) hroots

end HodgeLean.Foundations.Program
