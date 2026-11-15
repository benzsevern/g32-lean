import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIncidenceSupport
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCurvePoints
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSectionLift

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Incidence equations have prime order zero over an ordered point with only generic coordinates. -/
theorem s2v_l1b_divisor_generic_incidence_order_zero
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left] [IsDominant γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (x : B.left) (y : (g3_power Z (h + 1)).left)
    (hy : ∀ i, (g3_proj Z (h + 1) i).left y = genericPoint Z.left)
    (p : B.left.presheaf.stalk x)
    (φ : B.left.presheaf.stalk x →+* (g3_power Z (h + 1)).left.presheaf.stalk y)
    (hφunit : ∀ r, IsUnit (φ r) ↔ ¬ p ∣ r)
    (hφfield : ∀ r, s2v_l1b_functionFieldPullback γ.left (algebraMap _ B.left.functionField r) =
      algebraMap _ (g3_power Z (h + 1)).left.functionField (φ r))
    (U : B.left.affineOpens) (hx : x ∈ U.1) (hyU : γ.left y ∈ U.1)
    (b : ComplexPoint Z) (g : Γ(B.left, U.1))
    (hg : (s2c_branchIdeal Z B h γ b).ideal U = Ideal.span {g}) :
    emultiplicity p (B.left.presheaf.germ U.1 x hx g) = 0 := by
  have hn : γ.left y ∉ (s2c_branchIdeal Z B h γ b).support := by
    intro H
    obtain ⟨i, hi⟩ := (s2v_l1b_divisor_incidence_support_coordinate
      Z B hdimZ h γ hγsurj hγinv hγ b y).mp H
    exact s2v_l1b_divisor_curve_complex_ne_generic Z hdimZ b (hi.symm.trans (hy i))
  have hu := (s2v_l1b_divisor_generator_unit_iff B.left _ U g hg _ hyU).mpr hn
  have hunit : IsUnit (φ (B.left.presheaf.germ U.1 x hx g)) := by
    rw [s2v_l1b_divisor_section_stalk_lift γ.left x y φ hφfield U.1 hx hyU g]
    exact hu.map (γ.left.stalkMap y).hom
  exact emultiplicity_eq_zero.mpr ((hφunit _).mp hunit)

end HodgeLean.Foundations.Program
