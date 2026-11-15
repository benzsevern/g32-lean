import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedPointIdeals
import HodgeLean.Foundations.Program.SchoenTowerOverSections
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedParameterEtale

/-! # Actual etale parameters on compatible ordered curve charts
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- An actual open chart in a retained curve power inherits the etale root parameters of the curve chart.
Source: Schoen (1988), Lemma 2.2; the checked ordered-parameter etaleness supplier and composition with an open immersion. -/
theorem s2v_i2a_ordered_curve_chart_parameters_etale
    (A V : Over (Spec ↧ℂ)) [IsAffine A.left] [IsAffine V.left]
    (n : ℕ) (j : V ⟶ g3_power A n) [IsOpenImmersion j.left]
    (z : Γ(A.left, ⊤))
    (hEt : (MvPolynomial.eval₂Hom A.hom.appTop.hom (fun _ : Fin 1 => z)).Etale) :
    (MvPolynomial.eval₂Hom V.hom.appTop.hom
      (fun i => (j ≫ g3_proj A n i).left.appTop.hom z)).Etale := by
  letI : IsAffine (g3_power A n).left := s2v_l1a_ordered_power_affine A n
  have hjEt : j.left.appTop.hom.Etale :=
    HasRingHomProperty.appTop (P := @Etale) j.left inferInstance
  have heval : MvPolynomial.eval₂Hom V.hom.appTop.hom
      (fun i => (j ≫ g3_proj A n i).left.appTop.hom z) =
        j.left.appTop.hom.comp (MvPolynomial.eval₂Hom (g3_power A n).hom.appTop.hom
          (fun i => (g3_proj A n i).left.appTop.hom z)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      have H := congrArg (fun f : V.left ⟶ Spec ↧ℂ => f.appTop.hom c) (Over.w j)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using H.symm
    · intro i
      rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change (j ≫ g3_proj A n i).left.appTop z = _
      rw [Over.comp_left, Scheme.Hom.comp_appTop]
      rfl
  rw [heval]
  exact RingHom.Etale.stableUnderComposition _ _
    (s2v_l1a_ordered_parameter_etale A z hEt n) hjEt

/-- Every retained branch point equation pulls back to its actual shifted root-parameter equation on the compatible ordered chart.
Source: Schoen (1988), Lemma 2.2; the checked affine curve point-equation pullback supplier. -/
theorem s2v_i2a_ordered_curve_branch_ideals
    (A V Z : Over (Spec ↧ℂ)) [IsAffine A.left] [IsAffine V.left]
    (n : ℕ) (a : A ⟶ Z) (j : V ⟶ g3_power A n) (v : V ⟶ g3_power Z n)
    (hsquare : j ≫ s2_powerMap a n = v)
    {T : Type} (branch : T → ComplexPoint Z) (b : T → ℂ) (z : Γ(A.left, ⊤))
    (hCurve : ∀ t, ((branch t).left.ker.comap a.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {z - algebraMap ℂ Γ(A.left, ⊤) (b t)}) :
    ∀ t i, ((branch t).left.ker.comap ((v ≫ g3_proj Z n i).left)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(j ≫ g3_proj A n i).left.appTop.hom z -
        algebraMap ℂ Γ(V.left, ⊤) (b t)} := by
  intro t i
  have hcoord : (j ≫ g3_proj A n i) ≫ a = v ≫ g3_proj Z n i := by
    have H : s2_powerMap a n ≫ g3_proj Z n i = g3_proj A n i ≫ a :=
      s2_check_lift_proj n _ i
    rw [Category.assoc, ← H, ← Category.assoc, hsquare]
  have H := s2v_l1a_curve_point_equation_pullback a.left (j ≫ g3_proj A n i).left
    (branch t).left.ker (z - algebraMap ℂ Γ(A.left, ⊤) (b t)) (hCurve t)
  rw [← Over.comp_left, hcoord, map_sub] at H
  have hscalar : (j ≫ g3_proj A n i).left.appTop.hom (algebraMap ℂ Γ(A.left, ⊤) (b t)) =
      algebraMap ℂ Γ(V.left, ⊤) (b t) := (s2t_overSectionsAlgHom (j ≫ g3_proj A n i)).commutes (b t)
  rw [hscalar] at H
  exact H

end HodgeLean.Foundations.Program
