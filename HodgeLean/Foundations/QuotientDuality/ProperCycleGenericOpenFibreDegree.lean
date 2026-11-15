import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenResidueDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericFibreDegree

/-! # Original generic residue degrees measured on actual finite etale base opens -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Finiteness and etaleness only on the specified actual affine base open suffice to measure the original generic residue degree by its original complex fibre.
Source: Fulton, Intersection Theory, section 1.4; SGA 1, Expose I, finite etale degree and geometric fibres.
HC no distance; AV milestone no distance. -/
lemma properCycle_generic_degree_eq_fibre_card_on_finite_etale_open
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f.left ⁻¹ᵁ U)]
    [IsFinite (f.left ∣_ U)] [Etale (f.left ∣_ U)]
    (y : ComplexPoint (openScheme Y U)) :
    a1p_degree f.left (genericPoint X.left) =
      Nat.card ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) := by
  let XU := openScheme X (f.left ⁻¹ᵁ U)
  let YU := openScheme Y U
  let g := s2e_c11_restricted_over_morphism X Y f U
  letI : Nonempty XU.left := inferInstanceAs (Nonempty (f.left ⁻¹ᵁ U))
  letI : Nonempty YU.left := inferInstanceAs (Nonempty U)
  letI : IsIntegral XU.left := isIntegral_of_isOpenImmersion (f.left ⁻¹ᵁ U).ι
  letI : IsIntegral YU.left := isIntegral_of_isOpenImmersion U.ι
  letI : IsAffine YU.left := hU
  letI : IsFinite g.left := inferInstanceAs (IsFinite (f.left ∣_ U))
  letI : Etale g.left := inferInstanceAs (Etale (f.left ∣_ U))
  have hxgen : (f.left ⁻¹ᵁ U).ι (genericPoint XU.left) = genericPoint X.left :=
    genericPoint_eq_of_isOpenImmersion (f.left ⁻¹ᵁ U).ι
  have hygen : U.ι (genericPoint YU.left) = genericPoint Y.left :=
    genericPoint_eq_of_isOpenImmersion U.ι
  have hgU : g.left (genericPoint XU.left) = genericPoint YU.left := by
    apply U.ι.isOpenEmbedding.injective
    have h := congrArg (fun m => m (genericPoint XU.left)) (morphismRestrict_ι f.left U)
    change U.ι (g.left (genericPoint XU.left)) = f.left ((f.left ⁻¹ᵁ U).ι (genericPoint XU.left)) at h
    rw [hxgen, hg] at h
    exact h.trans hygen.symm
  have hdegree : a1p_degree g.left (genericPoint XU.left) =
      a1p_degree f.left (genericPoint X.left) := by
    have h := properCycle_degree_target_open_restriction f.left U (genericPoint XU.left)
    rw [hxgen] at h
    exact h
  letI : Nonempty (⊤ : YU.left.Opens) := ⟨⟨genericPoint YU.left, trivial⟩⟩
  letI : Nonempty (g.left ⁻¹ᵁ (⊤ : YU.left.Opens)) := ⟨⟨genericPoint XU.left, trivial⟩⟩
  let yT : ComplexPoint (openScheme YU ⊤) := (openHomeomorph YU ⊤).symm ⟨y, trivial⟩
  have hyT : Point.map (openInclusion YU ⊤) yT = y := by
    exact congrArg Subtype.val ((openHomeomorph YU ⊤).apply_symm_apply ⟨y, trivial⟩)
  have hc := properCycle_generic_residue_degree_eq_etale_fibre_card XU YU g hgU ⊤
    (isAffineOpen_top YU.left) yT
  rw [hyT, hdegree] at hc
  exact hc.trans (s2e_c1_restricted_complex_fibre_card X Y f U y)

end HodgeLean.Foundations.QuotientDuality
