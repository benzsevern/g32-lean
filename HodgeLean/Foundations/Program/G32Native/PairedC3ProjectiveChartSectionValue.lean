import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusionCharts

/-! # Original homogeneous fractions under the affine chart section map -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original retained standard open pulls back to the entire affine chart. -/
theorem paired_c3_projective_chart_preimage (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayι (homogeneousSubmodule (Fin (n + 1)) ℂ) (X i)
      (isHomogeneous_X ℂ i) zero_lt_one ⁻¹ᵁ ProjSpace.standardOpen ℂ n i = ⊤ := by
  let a := Proj.awayι (homogeneousSubmodule (Fin (n + 1)) ℂ) (X i)
    (isHomogeneous_X ℂ i) zero_lt_one
  have hr := Proj.opensRange_awayι (homogeneousSubmodule (Fin (n + 1)) ℂ)
    (X i) (isHomogeneous_X ℂ i) zero_lt_one
  exact (congrArg (fun U => a ⁻¹ᵁ U) hr).symm.trans (Scheme.Hom.preimage_opensRange a)

/-- The affine chart structural map recovers the original degree-zero
fraction from its original regular section, with coefficient one. -/
theorem paired_c3_projective_chart_section_value (n : ℕ) (i : Fin (n + 1))
    (x : Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X i)) :
    let G := homogeneousSubmodule (Fin (n + 1)) ℂ
    let a := Proj.awayι G (X i) (isHomogeneous_X ℂ i) zero_lt_one
    (Scheme.ΓSpecIso (CommRingCat.of (Away G (X i)))).hom
      (a.appLE (ProjSpace.standardOpen ℂ n i) ⊤
        (paired_c3_projective_chart_preimage n i).ge
        (Proj.awayToSection G (X i) x)) = x := by
  let G := homogeneousSubmodule (Fin (n + 1)) ℂ
  let U := ProjSpace.standardOpen ℂ n i
  let R := CommRingCat.of (Away G (X i))
  let E := Proj.basicOpenIsoSpec G (X i) (isHomogeneous_X ℂ i) zero_lt_one
  let a := Proj.awayι G (X i) (isHomogeneous_X ℂ i) zero_lt_one
  let hpre := (paired_c3_projective_chart_preimage n i).ge
  have he : E.hom ≫ a = U.ι := by
    change E.hom ≫ (E.inv ≫ U.ι) = U.ι
    rw [Iso.hom_inv_id_assoc]
  have ht : a.appLE U ⊤ hpre ≫ E.hom.appTop = U.topIso.inv := by
    change a.appLE U ⊤ hpre ≫ E.hom.appLE ⊤ ⊤ le_top = U.topIso.inv
    rw [Scheme.Hom.appLE_comp_appLE]
    simp only [he, Scheme.Opens.ι_appLE]
    rfl
  have heapp : E.hom.appTop = (Scheme.ΓSpecIso R).hom ≫
      Proj.awayToSection G (X i) ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top G (X i)
  let B := Proj.basicOpenIsoAway G (X i) (isHomogeneous_X ℂ i) zero_lt_one
  have hleft : (a.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso R).hom) ≫ B.hom = 𝟙 _ := by
    apply (cancel_mono U.topIso.inv).mp
    simpa only [Category.assoc, Category.id_comp] using (heapp ▸ ht)
  have hright : B.hom ≫ a.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso R).hom = 𝟙 _ := by
    apply (cancel_mono B.hom).mp
    simp only [Category.assoc, hleft, Category.id_comp]
    exact Category.comp_id _
  exact ConcreteCategory.congr_hom hright x

#print axioms paired_c3_projective_chart_section_value
end HodgeLean.Foundations.Program.G32Native
