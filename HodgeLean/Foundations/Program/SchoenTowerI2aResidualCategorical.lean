import HodgeLean.Foundations.Program.SchoenTowerI2aPeriodicQuotient
import HodgeLean.Foundations.Program.SchoenTowerI2aNormalQuotientComparison

/-! # The retained residual map as its actual categorical quotient
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained normal residual target represents the categorical quotient by its periodic deck generator.
Source: Schoen (1988), section 1; finite-action quotient comparison and the normal-target Zariski main isomorphism criterion. -/
theorem s2v_i2a_residual_categorical_quotient
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (hY : zmtiso_IsNormal Y.left) (d : X ⟶ X) [IsIso d]
    (m : ℕ) (hm : 0 < m) (hd : (End.of d) ^ m = 1)
    (β : X ⟶ Y) (hβd : d ≫ β = β)
    (hβsurj : Function.Surjective (Point.map β))
    (hβorbit : ∀ x z : ComplexPoint X, Point.map β x = Point.map β z →
      ∃ k : ℕ, (Point.map d)^[k] x = z) :
    ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T), d ≫ f = f →
      ∃! u : Y ⟶ T, β ≫ u = f := by
  obtain ⟨Q, q, hQ, hQproper, hqfin, hqsurj, hqd, hqorbit, hqcat⟩ :=
    s2v_i2a_periodic_deck_quotient X d m hm hd
  letI := hQ
  letI := hQproper
  letI := hqfin
  obtain ⟨u, hu, huunique⟩ := hqcat Y β hβd
  haveI : IsProper (u.left ≫ Y.hom) := by rw [Over.w u]; infer_instance
  haveI : IsProper u.left := IsProper.of_comp u.left Y.hom
  have hubij : Function.Bijective (Point.map u) := by
    constructor
    · intro p₁ p₂ heq
      obtain ⟨x₁, hx₁⟩ := hqsurj p₁
      obtain ⟨x₂, hx₂⟩ := hqsurj p₂
      have hβeq : Point.map β x₁ = Point.map β x₂ := by
        simpa only [← hu, Point.map_comp_apply, hx₁, hx₂] using heq
      obtain ⟨k, hk⟩ := hβorbit x₁ x₂ hβeq
      have H := (hqorbit x₁ x₂).mpr ⟨k, hk⟩
      simpa only [hx₁, hx₂] using H
    · intro y
      obtain ⟨x, hx⟩ := hβsurj y
      refine ⟨Point.map q x, ?_⟩
      simpa only [← Point.map_comp_apply, hu] using hx
  haveI : IsIso u.left := s2v_i2a_proper_point_bijective_isIso Q Y u hY hubij
  haveI : IsIso ((Over.forget (Spec ↧ℂ)).map u) := inferInstanceAs (IsIso u.left)
  haveI : IsIso u := isIso_of_reflects_iso u (Over.forget (Spec ↧ℂ))
  intro T f hf
  obtain ⟨v, hv, hvunique⟩ := hqcat T f hf
  refine ⟨inv u ≫ v, ?_, ?_⟩
  · change β ≫ (inv u ≫ v) = f
    rw [← hu, Category.assoc, IsIso.hom_inv_id_assoc]
    exact hv
  · intro w hw
    have H : u ≫ w = v := hvunique (u ≫ w) (by
      change q ≫ (u ≫ w) = f
      rw [← Category.assoc, hu]
      exact hw)
    apply (cancel_epi u).mp
    change u ≫ w = u ≫ (inv u ≫ v)
    rw [IsIso.hom_inv_id_assoc]
    exact H

end HodgeLean.Foundations.Program
