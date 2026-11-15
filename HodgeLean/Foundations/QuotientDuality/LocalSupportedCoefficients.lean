import HodgeLean.Foundations.QuotientDuality.LocalOpenCoefficients

/-! Locally constant coefficients for classes supported on an arbitrary open orientation domain. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem relative_open_coefficients (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (U : Opens X)
    (w : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n) :
    ∃ f : U → ℚ, IsLocallyConstant f ∧ ∀ y : U,
      relativeHomologyMap ℚ n (supportInclusionPairMap X
        (Set.singleton_subset_iff.mpr y.property)) w = f y • o.generator y.val := by
  let e := localOrientationHomologySheafIso X n o
  let s := relativeHomologyToHomologySheafSection ℚ X U n w
  let t := e.inv.hom.app (op U) s
  obtain ⟨f, hflc, hf⟩ := constant_section_open_coefficients X U t
  refine ⟨f, hflc, fun y => ?_⟩
  have hs : s = e.hom.hom.app (op U) t := by
    change s = (e.inv.hom ≫ e.hom.hom).app (op U) s
    rw [← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
    rfl
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ X U y.val y.property n) w
  have hstalk := ConcreteCategory.congr_hom (localOrientationHomologySheafIso_stalk X n o y.val) (f y)
  simp only [ConcreteCategory.comp_apply] at hgerm hstalk
  have hgerm' : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr y.property)) w =
      (singularChainHomologySheafStalkIso ℚ X y.val n).hom
        ((singularChainHomologySheaf ℚ X n).presheaf.germ U y.val y.property s) :=
    hgerm.symm
  rw [hgerm', hs]
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U y.val y.property e.hom.hom]
  rw [hf y]
  erw [HodgeLean.RealDefs.germ_constSection_eq_constantSheafStalkIso]
  exact hstalk

#print axioms relative_open_coefficients
end HodgeLean.Foundations.QuotientDuality
