import HodgeLean.Foundations.Program.SchoenCycleBranchTupleDivisibility
import HodgeLean.Foundations.Program.SchoenCycleInvariantSectionStalk

/-! # Actual branch sections at every marked coordinate -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A section of the actual branch ideal is divisible upstairs by every coordinate parameter centered at the mark.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_branch_section_coordinate_parameter_dvd
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z (n + 1)))
    (i : Fin (n + 1)) (hi : Point.map (g3_proj Z (n + 1) i) x = a)
    (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1)
    (s : Γ(B.left, U.1)) (hs : s ∈ (s2c_branchIdeal Z B n γ a).ideal U) :
    s2e_curvePowerParameter Z (n + 1) x i ∣
      γ.left.stalkMap x.underlying (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU s) := by
  classical
  let σ := Equiv.swap (0 : Fin (n + 1)) i
  let u := s2_permute Z (n + 1) σ
  let y := Point.map u x
  have hy : Point.map (g3_proj Z (n + 1) 0) y = a := by
    change x ≫ (u ≫ g3_proj Z (n + 1) 0) = a
    have hp : u ≫ g3_proj Z (n + 1) 0 = g3_proj Z (n + 1) (σ.symm 0) :=
      s2_check_lift_proj _ _ _
    rw [hp]
    change x ≫ g3_proj Z (n + 1) i = a at hi
    simpa only [σ, Equiv.symm_swap, Equiv.swap_apply_left] using hi
  have hu : u.left ≫ γ.left = γ.left := congrArg Over.Hom.left (hγ σ)
  have hyU : γ.left y.underlying ∈ U.1 := by
    change (u.left ≫ γ.left) x.underlying ∈ U.1
    rwa [hu]
  have hd := s2e_branch_section_first_parameter_dvd Z B n γ a y hy U hyU s hs
  have hm := map_dvd (u.left.stalkMap x.underlying).hom hd
  change u.left.stalkMap x.underlying (s2e_curvePowerParameter Z (n + 1) y 0) ∣
    u.left.stalkMap x.underlying (γ.left.stalkMap y.underlying
      (B.left.presheaf.germ U.1 (γ.left y.underlying) hyU s)) at hm
  rw [s2e_curvePowerParameter_permute Z (n + 1) σ x 0] at hm
  simp only [σ, Equiv.symm_swap, Equiv.swap_apply_left] at hm
  change s2e_curvePowerParameter Z (n + 1) x i ∣
    u.left.stalkMap x.underlying (γ.left.stalkMap (u.left x.underlying)
      (B.left.presheaf.germ U.1 (γ.left (u.left x.underlying)) hyU s)) at hm
  rw [s2e_invariant_section_stalk_pullback u.left γ.left hu U.1 x.underlying hxU hyU s] at hm
  exact hm

end HodgeLean.Foundations.Program
