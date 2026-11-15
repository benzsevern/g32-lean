import HodgeLean.Foundations.QuotientDuality.LocalOrientationCoefficients

/-! Local coefficients of supported classes on arbitrary orientation neighborhoods. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem constant_section_open_coefficients (X : TopCat.{0}) (U : Opens X)
    (s : (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.obj (op U)) :
    ∃ f : U → ℚ, IsLocallyConstant f ∧ ∀ y : U,
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U y.val y.property s =
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ ⊤ y.val (Opens.mem_top y.val)
        (constSection (AddCommGrpCat.of ℚ) ⊤ (f y)) := by
  have hex (y : U) : ∃ q : ℚ,
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U y.val y.property s =
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ ⊤ y.val (Opens.mem_top y.val)
        (constSection (AddCommGrpCat.of ℚ) ⊤ q) := by
    obtain ⟨t, ht⟩ : ∃ t, constStalkMap (AddCommGrpCat.of ℚ) y.val t =
        (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U y.val y.property s :=
      ⟨inv (constStalkMap (AddCommGrpCat.of ℚ) y.val)
        ((constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U y.val y.property s),
        apply_inv_self _ _⟩
    obtain ⟨V, hyV, q, rfl⟩ := (constPresheaf (T := X) (AddCommGrpCat.of ℚ)).exists_germ_eq t
    exact ⟨q, by rw [← ht, ← germ_constSection, germ_constSection_top]⟩
  choose f hf using hex
  refine ⟨f, ?_, hf⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U x.val x.property s =
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U x.val x.property
        (constSection (AddCommGrpCat.of ℚ) U (f x)) := by
    rw [germ_constSection_top]
    exact hf x
  obtain ⟨W, hxW, iU, iV, heq⟩ :=
    (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ_eq x.val
      x.property x.property _ _ hx
  have hopen : IsOpen (Subtype.val ⁻¹' (W : Set X) : Set U) :=
    W.isOpen.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds hxW] with y hy
  apply germ_constSection_injective (AddCommGrpCat.of ℚ) y.val
  have hyy : (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U y.val y.property s =
      (constSheaf (T := X) (AddCommGrpCat.of ℚ)).presheaf.germ U y.val y.property
        (constSection (AddCommGrpCat.of ℚ) U (f x)) := by
    rw [← TopCat.Presheaf.germ_res_apply _ iU y.val hy,
      ← TopCat.Presheaf.germ_res_apply _ iV y.val hy]
    exact congrArg _ heq
  exact (hf y).symm.trans (hyy.trans (germ_constSection_top (T := X) (AddCommGrpCat.of ℚ) U y.val y.property (f x)))

#print axioms constant_section_open_coefficients
end HodgeLean.Foundations.QuotientDuality
