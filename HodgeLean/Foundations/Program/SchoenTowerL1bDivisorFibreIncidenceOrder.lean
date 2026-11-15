import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFibreIncidence
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIncidenceGermPrime
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSectionLift

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- Incidence equations have prime order one precisely at the point defining the coordinate fibre. -/
theorem s2v_l1b_divisor_coordinate_fibre_incidence_order
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left] [IsDominant γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (b c : ComplexPoint Z) (i : Fin (h + 1))
    (x : B.left) (y : (g3_power Z (h + 1)).left) (hy : Order.coheight y = 1)
    (hyi : (g3_proj Z (h + 1) i).left y = b.underlying)
    (p : B.left.presheaf.stalk x) (hp : Prime p)
    (φ : B.left.presheaf.stalk x →+* (g3_power Z (h + 1)).left.presheaf.stalk y)
    (hφunit : ∀ r, IsUnit (φ r) ↔ ¬ p ∣ r)
    (hφfield : ∀ r, s2v_l1b_functionFieldPullback γ.left (algebraMap _ B.left.functionField r) =
      algebraMap _ (g3_power Z (h + 1)).left.functionField (φ r))
    (U : B.left.affineOpens) (hx : x ∈ U.1) (hyU : γ.left y ∈ U.1)
    (g : Γ(B.left, U.1)) (hg : (s2c_branchIdeal Z B h γ c).ideal U = Ideal.span {g})
    (hg0 : (B.left.presheaf.germ U.1 x hx).hom g ≠ 0) :
    emultiplicity p ((B.left.presheaf.germ U.1 x hx).hom g) =
      if c = b then 1 else 0 := by
  classical
  let a := (B.left.presheaf.germ U.1 x hx).hom g
  have hunit : IsUnit (φ a) ↔ c ≠ b := by
    dsimp only [a]
    rw [s2v_l1b_divisor_section_stalk_lift γ.left x y φ hφfield U.1 hx hyU g,
      isUnit_map_iff]
    exact (s2v_l1b_divisor_generator_unit_iff B.left _ U g hg _ hyU).trans
      (not_congr (s2v_l1b_divisor_coordinate_fibre_incidence_support
        Z B hdimZ h γ hγsurj hγinv hγ b c i y hy hyi))
  have hdiv : p ∣ a ↔ c = b := by
    simpa only [not_not] using not_congr ((hφunit a).symm.trans hunit)
  by_cases hcb : c = b
  · rw [if_pos hcb]
    have haPrime : Prime a :=
      (s2v_l1b_divisor_incidence_germ_prime_or_unit Z B h γ c x U hx g hg hg0).resolve_left
        (fun hu => hp.not_isUnit (isUnit_of_dvd_unit (hdiv.mpr hcb) hu))
    have hassoc : Associated p a := (hp.dvd_prime_iff_associated haPrime).mp (hdiv.mpr hcb)
    rw [emultiplicity_eq_of_associated_right hassoc.symm]
    exact (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self
  · rw [if_neg hcb]
    exact emultiplicity_eq_zero.mpr (fun H => hcb (hdiv.mp H))

end HodgeLean.Foundations.Program
