import HodgeLean.RealDefs.DegreeZero
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.OrientationHomologySheaf

/-! # Global top homology classes against the complex orientation

On a preconnected smooth complex variety of dimension `d`, a class `w` in
`H_{2d}(X(ℂ), ∅; ℚ)` has, at every complex point `y`, local value `q • μ_y` for one rational `q`
independent of `y`, where `μ_y` is upstream's `complexLocalOrientation`. The proof sends `w` to a
global section of the singular homology sheaf, transports it along upstream's
`complexOrientationHomologySheafIso` to a global section of the constant sheaf `ℚ`, which is
constant (`exists_eq_constSection`), and reads off the germs. -/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [T2Space (ComplexPoint X)]

set_option backward.isDefEq.respectTransparency false in
/-- The germ of a constant section is the constant-sheaf stalk identification. -/
lemma germ_constSection_eq_constantSheafStalkIso {T : TopCat.{0}} (A : AddCommGrpCat.{0})
    (y : T) (a : A) :
    (constSheaf (T := T) A).presheaf.germ ⊤ y (Opens.mem_top y) (constSection A ⊤ a) =
      (TopCat.Sheaf.constantSheafStalkIso A y).hom a := by
  rw [germ_constSection]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a preconnected smooth complex variety, every global top homology class has local values
a fixed rational multiple of the complex orientation. -/
theorem exists_relativeHomologyMap_eq_smul_complexLocalOrientation
    [PreconnectedSpace (ComplexPoint X)]
    (w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) (2 * d)) :
    ∃ q : ℚ, ∀ y : ComplexPoint X,
      relativeHomologyMap ℚ (2 * d)
          (supportInclusionPairMap (TopCat.of (ComplexPoint X))
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
        q • complexLocalOrientation X d y := by
  let T := TopCat.of (ComplexPoint X)
  let e := complexOrientationHomologySheafIso X d
  let s := relativeHomologyToHomologySheafSection ℚ T ⊤ (2 * d) w
  let t := e.inv.hom.app (op ⊤) s
  obtain ⟨a, ha⟩ := exists_eq_constSection (T := T) (AddCommGrpCat.of ℚ) t
  refine ⟨a, fun y => ?_⟩
  have hs : s = e.hom.hom.app (op ⊤) t := by
    change s = (e.inv.hom ≫ e.hom.hom).app (op ⊤) s
    rw [← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
    rfl
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ T ⊤ y (Opens.mem_top y) (2 * d)) w
  have hstalk := ConcreteCategory.congr_hom (complexOrientationHomologySheafIso_stalk X d y) a
  simp only [ConcreteCategory.comp_apply] at hgerm hstalk
  have hgerm' : relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap T (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
      (singularChainHomologySheafStalkIso ℚ T y (2 * d)).hom
        ((singularChainHomologySheaf ℚ T (2 * d)).presheaf.germ ⊤ y (Opens.mem_top y) s) :=
    hgerm.symm
  rw [hgerm', hs, ha]
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y (Opens.mem_top y) e.hom.hom]
  erw [germ_constSection_eq_constantSheafStalkIso]
  erw [hstalk]
  rfl

end HodgeLean.RealDefs
