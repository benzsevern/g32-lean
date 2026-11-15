import HodgeLean.Foundations.QuotientDuality.LocalOrientationSheaf

/-! Local coefficients of actual homology classes vary locally constantly. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

private theorem constSection_locally_constant {X : TopCat.{0}}
    (s : (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.obj (op ⊤)) :
    ∃ f : X → ℚ, IsLocallyConstant f ∧ ∀ x,
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ ⊤ x (Opens.mem_top x) s =
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ ⊤ x (Opens.mem_top x)
        (constSection (AddCommGrpCat.of ℚ) ⊤ (f x)) := by
  choose f hf using exists_germ_eq_constSection (T := X) (AddCommGrpCat.of ℚ) s
  refine ⟨f, ?_, hf⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨W, hxW, iU, iV, heq⟩ :=
    (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ_eq x
      (Opens.mem_top x) (Opens.mem_top x) _ _ (hf x)
  filter_upwards [W.isOpen.mem_nhds hxW] with y hy
  apply germ_constSection_injective (AddCommGrpCat.of ℚ) y
  rw [← hf y, ← TopCat.Presheaf.germ_res_apply _ iU y hy,
    ← TopCat.Presheaf.germ_res_apply _ iV y hy]
  exact congrArg _ heq

theorem relative_local_coefficients (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n)
    (w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens X) : Set X)ᶜ : Set X)) n) :
    ∃ f : X → ℚ, IsLocallyConstant f ∧ ∀ y,
      relativeHomologyMap ℚ n (supportInclusionPairMap X
        (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w = f y • o.generator y := by
  let e := localOrientationHomologySheafIso X n o
  let s := relativeHomologyToHomologySheafSection ℚ X ⊤ n w
  let t := e.inv.hom.app (op ⊤) s
  obtain ⟨f, hflc, hf⟩ := constSection_locally_constant t
  refine ⟨f, hflc, fun y => ?_⟩
  have hs : s = e.hom.hom.app (op ⊤) t := by
    change s = (e.inv.hom ≫ e.hom.hom).app (op ⊤) s
    rw [← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
    rfl
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ X ⊤ y (Opens.mem_top y) n) w
  have hstalk := ConcreteCategory.congr_hom (localOrientationHomologySheafIso_stalk X n o y) (f y)
  simp only [ConcreteCategory.comp_apply] at hgerm hstalk
  have hgerm' : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
      (singularChainHomologySheafStalkIso ℚ X y n).hom
        ((singularChainHomologySheaf ℚ X n).presheaf.germ ⊤ y (Opens.mem_top y) s) :=
    hgerm.symm
  rw [hgerm', hs]
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y (Opens.mem_top y) e.hom.hom]
  rw [hf y]
  erw [HodgeLean.RealDefs.germ_constSection_eq_constantSheafStalkIso]
  exact hstalk

theorem local_coefficients (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (c : Homology ℚ X n) :
    ∃ f : X → ℚ, IsLocallyConstant f ∧ ∀ y, localOrientation X n c y = f y • o.generator y := by
  let A := TopPair.ofSubset ((((⊤ : Opens X) : Set X)ᶜ) : Set X)
  obtain ⟨f, hlc, hf⟩ := relative_local_coefficients X n o
    ((relativeHomologyProjection ℚ A n).hom c)
  refine ⟨f, hlc, fun y => ?_⟩
  have hn := relativeHomologyProjection_map n
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y))) c
  have hi : (supportInclusionPairMap X
      (Set.singleton_subset_iff.mpr (Opens.mem_top y))).hom.right = 𝟙 X := rfl
  rw [hi] at hn
  erw [homologyMap_id] at hn
  exact hn.symm.trans (hf y)

#print axioms local_coefficients
end HodgeLean.Foundations.QuotientDuality
