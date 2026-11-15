import HodgeLean.Foundations.Program.SchoenTowerL1bKvalMaps
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A stalk unit is represented by a unit on a neighborhood. -/
theorem s2v_l1b_stalk_unit_section (X : Scheme.{0}) (x : X)
    (ε : (X.presheaf.stalk x)ˣ) :
    ∃ (U : X.Opens) (hx : x ∈ U) (u : Γ(X, U)ˣ),
      X.presheaf.germ U x hx (u : Γ(X, U)) = ε := by
  obtain ⟨V, hxV, s, hs⟩ := X.presheaf.exists_germ_eq (ε : X.presheaf.stalk x)
  have hu : IsUnit (X.presheaf.germ V x hxV s) := hs ▸ ε.isUnit
  obtain ⟨U, j, hxU, u, hu⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ V s x hxV hu
  refine ⟨U, hxU, u, ?_⟩
  rw [hu, X.presheaf.germ_res_apply j x hxU s]
  exact hs

/-- The stalk and any nonempty affine section ring generate the same subfield with a fixed element. -/
theorem s2v_l1b_stalk_section_generated_subfield
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] (x : X)
    (η : Spec (.of K) ⟶ X) (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    (U : X.affineOpens) [Nonempty U.1]
    (hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) (t : K) :
    Subfield.closure (Set.range (s2v_l1b_kval_stalkMap X x κ) ∪ {t}) =
      Subfield.closure
        (Set.range (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) := by
  letI := κ.hom.toAlgebra
  rw [s2v_l1b_generic_section_generated_subfield X η κ hη U hU hηU t]
  exact s2v_l1b_fraction_field_generator (R := X.presheaf.stalk x)
    (F := X.functionField) t

/-- A weighted equation with a stalk unit spreads with every choice of branch generators. -/
theorem s2v_l1b_stalk_weighted_equation_spread
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] (x : X)
    (η : Spec (.of K) ⟶ X) (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    (V : X.affineOpens) (hxV : x ∈ V.1)
    {J : Type} [Fintype J] (I : J → X.IdealSheafData)
    (f : J → Γ(X, V)) (hf : ∀ j, (I j).ideal V = Ideal.span {f j})
    (n : J → ℕ) (t : K) (m : ℕ) (ε : (X.presheaf.stalk x)ˣ)
    (hgen : Subfield.closure (Set.range (s2v_l1b_kval_stalkMap X x κ) ∪ {t}) = ⊤)
    (ht : t ^ m = s2v_l1b_kval_stalkMap X x κ ε *
      ∏ j, s2v_l1b_kval_stalkMap X x κ (X.presheaf.germ V.1 x hxV (f j)) ^ n j) :
    ∃ U₀ : X.Opens, x ∈ U₀ ∧
      ∀ (U : X.affineOpens) (hU : U.1 ≤ U₀) (hxU : x ∈ U.1)
        (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) (g : J → Γ(X, U)),
        (∀ j, (I j).ideal U = Ideal.span {g j}) →
        ∃ ε' : Γ(X, U)ˣ,
          Subfield.closure
            (Set.range (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ∪ {t}) = ⊤ ∧
          t ^ m = (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom ε' *
            ∏ j, (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom (g j) ^ n j := by
  obtain ⟨W, hxW, u, hu⟩ := s2v_l1b_stalk_unit_section X x ε
  refine ⟨V.1 ⊓ W, ⟨hxV, hxW⟩, ?_⟩
  intro U hU hxU hηU g hg
  letI : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  letI : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  have hUV : U.1 ≤ V.1 := hU.trans inf_le_left
  have hUW : U.1 ≤ W := hU.trans inf_le_right
  have hgeneric : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1 := by
    intro z _
    change X.fromSpecStalk (genericPoint X) z ∈ U.1
    haveI : Subsingleton (Spec X.functionField) := by
      change Subsingleton (PrimeSpectrum X.functionField)
      infer_instance
    rw [Subsingleton.elim z (IsLocalRing.closedPoint X.functionField),
      Scheme.fromSpecStalk_closedPoint]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty U.1›)
  let ρ := (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
  let uU : Γ(X, U)ˣ := Units.map (X.presheaf.map (homOfLE hUW).op).hom u
  let fU : J → Γ(X, U) := fun j => X.presheaf.map (homOfLE hUV).op (f j)
  have hmap (s : Γ(X, U)) :
      ρ s = s2v_l1b_kval_stalkMap X x κ (X.presheaf.germ U.1 x hxU s) := by
    dsimp only [ρ]
    rw [s2v_l1b_section_map_of_generic_factor X η κ hη U.1 hgeneric hηU]
    change κ (X.germToFunctionField U.1 s) =
      κ (algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U.1 x hxU s))
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  have hunit : ρ (uU : Γ(X, U)) = s2v_l1b_kval_stalkMap X x κ ε := by
    rw [hmap]
    change s2v_l1b_kval_stalkMap X x κ
      (X.presheaf.germ U.1 x hxU (X.presheaf.map (homOfLE hUW).op (u : Γ(X, W)))) = _
    rw [X.presheaf.germ_res_apply, hu]
  have hfU (j : J) : ρ (fU j) =
      s2v_l1b_kval_stalkMap X x κ (X.presheaf.germ V.1 x hxV (f j)) := by
    rw [hmap]
    dsimp only [fU]
    rw [X.presheaf.germ_res_apply]
  have heq : t ^ m = ρ (uU : Γ(X, U)) * ∏ j, ρ (fU j) ^ n j := by
    simpa only [hunit, hfU] using ht
  have hfg (j : J) : Ideal.span {fU j} = Ideal.span {g j} := by
    rw [← hg j, ← (I j).map_ideal hUV, hf j, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  obtain ⟨ε', hε'⟩ := s2v_l1b_branch_equation_change_generators ρ fU g n hfg t m uU heq
  refine ⟨ε', ?_, hε'⟩
  rw [← s2v_l1b_stalk_section_generated_subfield X x η κ hη U hgeneric hηU t]
  exact hgen

end HodgeLean.Foundations.Program
