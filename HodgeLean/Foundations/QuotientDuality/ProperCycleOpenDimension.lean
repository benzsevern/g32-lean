import HodgeLean.Foundations.QuotientDuality.ProperCycleDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenResidueDegree

/-! # Intrinsic dimension of actual nonempty algebraic opens -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual nonempty algebraic open of an integral finite-type complex scheme retains the original intrinsic dimension.
Source: EGA IV, 5.6.5, generic residue-field dimension; open-immersion residue-field isomorphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_nonempty_open_dimension
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (U : Y.left.Opens) [Nonempty U] :
    TopologicalSpace.dim U.toScheme = TopologicalSpace.dim Y.left := by
  let Z := openScheme Y U
  letI : Nonempty Z.left := inferInstanceAs (Nonempty U.toScheme)
  letI : IsIntegral Z.left := isIntegral_of_isOpenImmersion U.ι
  letI : LocallyOfFiniteType Z.hom := by
    change LocallyOfFiniteType (U.ι ≫ Y.hom)
    infer_instance
  have hd : a1p_degree U.ι (genericPoint Z.left) = 1 := by
    have h := properCycle_degree_precompose_open_immersion U.ι (𝟙 Y.left) (genericPoint Z.left)
    rw [Category.comp_id] at h
    exact h.trans (Scheme.Hom.residueDegree_id _)
  have h := (a1p_degree_pos_iff (openInclusion Y U) (genericPoint Z.left)).mp
    (show 0 < a1p_degree (openInclusion Y U).left (genericPoint Z.left) by exact hd ▸ Nat.zero_lt_one)
  change Order.height (U.ι (genericPoint Z.left)) = Order.height (genericPoint Z.left) at h
  have hg : U.ι (genericPoint Z.left) = genericPoint Y.left :=
    genericPoint_eq_of_isOpenImmersion U.ι
  rw [hg, properCycle_height_generic Y, properCycle_height_generic Z] at h
  exact_mod_cast h.symm

end HodgeLean.Foundations.QuotientDuality
