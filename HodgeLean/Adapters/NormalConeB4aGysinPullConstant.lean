import HodgeLean.Adapters.NormalConeB4aGysinBridgeDefs

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- Pullback of a constant section is the same constant on the inverse image open. -/
theorem a3b4a_gysin_pull_sectionConst
    {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (i : K ⟶ Z) (U : Z.Opens) (c : ℂ) :
    i.app U (a3b4a_gysin_sectionConst q U c) =
      a3b4a_gysin_sectionConst (i ≫ q) (i ⁻¹ᵁ U) c := by
  have h := Scheme.Hom.appLE_comp_appLE i q ⊤ U (i ⁻¹ᵁ U) le_top le_rfl
  rw [i.appLE_eq_app] at h
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)

end HodgeLean.Adapters
