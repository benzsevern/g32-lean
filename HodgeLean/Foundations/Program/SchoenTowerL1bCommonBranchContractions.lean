import HodgeLean.Foundations.Program.SchoenTowerL1bCurvePointEquations
import HodgeLean.Foundations.Program.SchoenTowerL1aCompatibleCurveChart
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedPointIdeals
import HodgeLean.Foundations.Program.SchoenTowerL1aBranchIdealContraction

/-! # Simultaneous branch contractions on a compatible quotient chart

All branch equations use the same curve parameter and the same retained map.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Translated point equations on one curve chart identify every actual branch
insertion ideal on one compatible retained quotient chart by exact contraction. -/
theorem s2v_l1b_common_chart_branch_contractions
    (A Z B : Over (Spec ↧ℂ)) [IsAffine A.left] [IsSeparated Z.hom]
    (h : ℕ) (a : A ⟶ Z) (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (O : B.left.affineOpens)
    (j : ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) ⟶
      g3_power A (h + 1))
    (hj : j ≫ s2_powerMap a (h + 1) =
      ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1))
    {κ : Type} (b : κ → ComplexPoint Z) (c : κ → Γ(Spec ↧ℂ, ⊤))
    (zA : Γ(A.left, ⊤))
    (hI : ∀ k, ((b k).left.ker.comap a.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {zA - A.hom.appTop.hom (c k)}) :
    let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
    letI : IsAffine V.left := O.2.preimage γ.left
    let z (i : Fin (h + 1)) := (j ≫ g3_proj A (h + 1) i).left.appTop.hom zA
    ∀ k, ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι).ideal
        ⟨⊤, @isAffineOpen_top _ O.2⟩ =
      (Ideal.span {z 0 - V.hom.appTop.hom (c k)}).comap (γ.left ∣_ O.1).appTop.hom := by
  let X := g3_power Z (h + 1)
  let V := ComplexPoint.openScheme X (γ.left ⁻¹ᵁ O.1)
  let v : V ⟶ X := ComplexPoint.openInclusion X (γ.left ⁻¹ᵁ O.1)
  letI : IsAffine V.left := O.2.preimage γ.left
  let ac (i : Fin (h + 1)) := j ≫ g3_proj A (h + 1) i
  let z (i : Fin (h + 1)) := (ac i).left.appTop.hom zA
  have hac (i : Fin (h + 1)) : ac i ≫ a = v ≫ g3_proj Z (h + 1) i := by
    have H : s2_powerMap a (h + 1) ≫ g3_proj Z (h + 1) i =
        g3_proj A (h + 1) i ≫ a := s2_check_lift_proj (h + 1) _ i
    change (j ≫ g3_proj A (h + 1) i) ≫ a = _
    rw [Category.assoc, ← H, ← Category.assoc, hj]
  have hzi (k : κ) (i : Fin (h + 1)) :
      ((b k).left.ker.comap (v ≫ g3_proj Z (h + 1) i).left).ideal
        ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {z i - V.hom.appTop.hom (c k)} := by
    rw [← hac]
    have H := s2v_l1a_curve_point_equation_pullback a.left (ac i).left
      (b k).left.ker (zA - A.hom.appTop.hom (c k)) (hI k)
    rw [map_sub] at H
    have hc : (ac i).left.appTop.hom (A.hom.appTop.hom (c k)) =
        V.hom.appTop.hom (c k) := by
      exact congrArg (fun f : V.left ⟶ Spec ↧ℂ => f.appTop.hom (c k)) (Over.w (ac i))
    rw [hc] at H
    exact H
  change ∀ k, ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι).ideal
      ⟨⊤, @isAffineOpen_top _ O.2⟩ =
    (Ideal.span {z 0 - V.hom.appTop.hom (c k)}).comap (γ.left ∣_ O.1).appTop.hom
  intro k
  have H := s2v_l1a_branchIdeal_affine_contraction Z B h γ (b k) O
  dsimp only at H
  change ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι).ideal
    ⟨⊤, @isAffineOpen_top _ O.2⟩ =
      ((((b k).left.ker.comap (g3_proj Z (h + 1) 0).left).comap v.left).ideal
        ⟨⊤, isAffineOpen_top _⟩).comap (γ.left ∣_ O.1).appTop.hom at H
  rw [← Scheme.IdealSheafData.comap_comp] at H
  have hz := hzi k 0
  rw [Over.comp_left] at hz
  rw [hz] at H
  exact H

end HodgeLean.Foundations.Program
