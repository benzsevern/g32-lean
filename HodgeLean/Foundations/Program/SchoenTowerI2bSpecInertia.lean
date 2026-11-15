import HodgeLean.Foundations.Program.SchoenTowerI2bFieldAction
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! Evaluation inertia as equality of spectrum points.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
universe u
namespace HodgeLean.Foundations.Program

/-- Equality of every evaluation is exactly fixing the corresponding spectrum point.
Source: full faithfulness of the spectrum functor. -/
theorem s2v_i2b_spec_point_fixed_iff
    {A L : Type u} [CommRing A] [CommRing L]
    (p : Spec ↧L ⟶ Spec ↧A) (g : A →+* A) :
    p ≫ Spec.map (CommRingCat.ofHom g) = p ↔
      ∀ b, (Spec.homEquivRingHom p) (g b) = (Spec.homEquivRingHom p) b := by
  rw [← Spec.preimage_inj]
  simp only [Spec.preimage_comp, Spec.preimage_map]
  constructor
  · intro he b
    exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of L => f.hom b) he
  · intro he
    ext b
    exact he b

/-- Postcomposition by a spectrum automorphism iterates by ring powers in the same direction.
Source: contravariant functoriality of the spectrum functor. -/
theorem s2v_i2b_spec_point_iterate
    {R A L : Type u} [CommRing R] [CommRing A] [CommRing L] [Algebra R A]
    (p : Spec ↧L ⟶ Spec ↧A) (g : A ≃ₐ[R] A) (n : ℕ) :
    (fun q : Spec ↧L ⟶ Spec ↧A =>
      q ≫ Spec.map (CommRingCat.ofHom g.toRingHom))^[n] p =
      p ≫ Spec.map (CommRingCat.ofHom (g ^ n).toRingHom) := by
  induction n with
  | zero =>
    change p = p ≫ Spec.map (𝟙 (CommRingCat.of A))
    rw [Spec.map_id, Category.comp_id]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Category.assoc, ← Spec.map_comp]
    congr 1


/-- Pointwise integral-element inertia fixes the actual spectrum point under its iterate.
Source: full faithfulness and contravariant functoriality of the spectrum functor. -/
theorem s2v_i2b_integral_spec_iterate_fixed
    {R K L : Type u} [CommRing R] [Field K] [CommRing L] [Algebra R K]
    (p : Spec ↧L ⟶ Spec ↧(integralClosure R K))
    (d : K ≃ₐ[R] K) (n : ℕ)
    (hp : ∀ b, (Spec.homEquivRingHom p) ((d.mapIntegralClosure ^ n) b) =
      (Spec.homEquivRingHom p) b) :
    (fun q : Spec ↧L ⟶ Spec ↧(integralClosure R K) =>
      q ≫ Spec.map (CommRingCat.ofHom d.mapIntegralClosure.toRingHom))^[n] p = p := by
  rw [s2v_i2b_spec_point_iterate]
  exact (s2v_i2b_spec_point_fixed_iff p _).mpr hp

end HodgeLean.Foundations.Program
