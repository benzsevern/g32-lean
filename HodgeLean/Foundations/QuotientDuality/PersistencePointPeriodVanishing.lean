import HodgeLean.Foundations.Program.SchoenExceptionalProofs

/-! Primitive cohomology vanishing from an actual pointwise shorter deck period. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_primitive_vanishing_of_point_period
    (X : TopCat.{0}) (f : X ⟶ X) (m a : ℕ) (ha : ¬ m ∣ a)
    (hperiod : ∀ x : X, f^[a] x = x)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (n : ℕ)
    (v : Cohomology ℂ X n) (hv : cohomologyMap ℂ n f v = ζ • v) : v = 0 := by
  have he : TopCat.ofHom ⟨f^[a], f.hom.continuous.iterate a⟩ = 𝟙 X := by
    apply TopCat.ext
    exact hperiod
  have hp := s3_cohomology_iterate f n a v ζ hv
  rw [he, cohomologyMap_id, LinearMap.id_apply] at hp
  have hne : ζ ^ a ≠ 1 := fun h => ha ((hζ.pow_eq_one_iff_dvd a).mp h)
  have hz : (ζ ^ a - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hp, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end HodgeLean.Foundations.QuotientDuality
