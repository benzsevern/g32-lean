import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

/-! # The actual branch insertion as a coordinate fibre

Implication from the retained product insertion to its actual pullback square
and coordinate point kernel. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Forgetting the inserted first coordinate recovers the actual retained
ordered tuple, as a scheme map.
Source: Schoen (1988), §2, printed p. 12, insertion map. -/
theorem s2v_l1a_branchInsertion_snd (Z : Over (Spec ↧ℂ)) (h : ℕ) (b : ComplexPoint Z) :
    (s2c_branchInsertion Z h b).left ≫ pullback.snd Z.hom (g3_power Z h).hom =
      𝟙 (g3_power Z h).left := by
  have H : s2c_branchInsertion Z h b ≫
      CartesianMonoidalCategory.snd Z (g3_power Z h) = 𝟙 (g3_power Z h) := by
    apply s2_product_hom_ext h
    intro i
    rw [Category.assoc]
    change s2c_branchInsertion Z h b ≫ g3_proj Z (h + 1) i.succ = _
    rw [s2c_branchInsertion, s2_check_lift_proj, Category.id_comp]
    rfl
  exact congrArg (fun f : g3_power Z h ⟶ g3_power Z h => f.left) H

/-- The retained insertion is the actual scheme fibre of the first coordinate
projection at the retained complex point.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Hartshorne, Algebraic Geometry, II.3. -/
theorem s2v_l1a_branchInsertion_isPullback (Z : Over (Spec ↧ℂ)) (h : ℕ)
    (b : ComplexPoint Z) :
    IsPullback (s2c_branchInsertion Z h b).left (g3_power Z h).hom
      (g3_proj Z (h + 1) 0).left b.left := by
  let P := g3_power Z h
  have H : s2c_branchInsertion Z h b ≫ g3_proj Z (h + 1) 0 =
      CartesianMonoidalCategory.toUnit P ≫ b := by
    change CartesianMonoidalCategory.lift _ _ ≫ CartesianMonoidalCategory.fst _ _ = _
    exact CartesianMonoidalCategory.lift_fst _ _
  have hc : (s2c_branchInsertion Z h b).left ≫ pullback.fst Z.hom P.hom =
      P.hom ≫ b.left := congrArg (fun f : P ⟶ Z => f.left) H
  have Hr : IsPullback (pullback.snd Z.hom P.hom) (pullback.fst Z.hom P.hom)
      P.hom Z.hom := (IsPullback.of_hasPullback Z.hom P.hom).flip
  change IsPullback (s2c_branchInsertion Z h b).left P.hom
    (pullback.fst Z.hom P.hom) b.left
  refine IsPullback.of_right ?_ hc Hr
  rw [s2v_l1a_branchInsertion_snd, b.w]
  exact IsPullback.of_id_fst

/-- The actual branch insertion kernel is the full first-coordinate point
ideal pullback, as an ideal sheaf.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Hartshorne, Algebraic Geometry, II.5–6. -/
theorem s2v_l1a_branchInsertion_kernel (Z : Over (Spec ↧ℂ)) [IsSeparated Z.hom]
    (h : ℕ) (b : ComplexPoint Z) :
    (s2c_branchInsertion Z h b).left.ker =
      b.left.ker.comap (g3_proj Z (h + 1) 0).left := by
  letI : IsClosedImmersion (b.left ≫ Z.hom) := by
    rw [b.w]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion b.left := IsClosedImmersion.of_comp b.left Z.hom
  let H := s2v_l1a_branchInsertion_isPullback Z h b
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion b.left
    (g3_proj Z (h + 1) 0).left]
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end HodgeLean.Foundations.Program
