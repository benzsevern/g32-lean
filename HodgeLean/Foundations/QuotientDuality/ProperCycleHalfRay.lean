import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeContraction

/-! # Relative vanishing for a tangential half-ray support -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Push the entire real tangential coordinate below the endpoint of the upper half-ray.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance of pairs.
HC no distance; AV milestone no distance. -/
def properCycle_upper_half_ray_push (Y : TopCat.{0}) (S : Set Y) (a : ℝ) :
    TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | a ≤ z.1 ∧ z.2 ∈ S}ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | a ≤ z.1 ∧ z.2 ∈ S}ᶜ :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun z => (a - 1, z.2), continuous_const.prodMk continuous_snd⟩)
    (by intro z _ h; have hh : a ≤ a - 1 := h.1; linarith)

private lemma upper_half_ray_interpolate_mem
    {Y : Type} (S : Set Y) (a : ℝ) (u : unitInterval) (t : ℝ) (y : Y)
    (hz : ¬ (a ≤ t ∧ y ∈ S)) :
    ¬ (a ≤ (1 - (u : ℝ)) * (a - 1) + (u : ℝ) * t ∧ y ∈ S) := by
  intro h
  have ht : t < a := lt_of_not_ge (fun ha => hz ⟨ha, h.2⟩)
  have he : (1 - (u : ℝ)) * (a - 1) + (u : ℝ) * t < a :=
    (convex_Iio (𝕜 := ℝ) a) (show a - 1 ∈ Set.Iio a from sub_lt_self a zero_lt_one) ht
      (sub_nonneg.mpr u.2.2) u.2.1 (by ring)
  exact (not_lt_of_ge h.1) he

/-- Linear tangential interpolation preserves the upper half-ray support complement.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance.
HC no distance; AV milestone no distance. -/
def properCycle_upper_half_ray_contraction (Y : TopCat.{0}) (S : Set Y) (a : ℝ) :
    TopPair.Homotopy (properCycle_upper_half_ray_push Y S a)
      (𝟙 (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | a ≤ z.1 ∧ z.2 ∈ S}ᶜ)) where
  fst :=
    { toFun := fun uz => ((1 - (uz.1 : ℝ)) * (a - 1) + (uz.1 : ℝ) * uz.2.1, uz.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro z
        change ((1 - (0 : ℝ)) * (a - 1) + 0 * z.1, z.2) = (a - 1, z.2)
        simp <;> rfl
      map_one_left := by
        intro z
        change ((1 - (1 : ℝ)) * (a - 1) + 1 * z.1, z.2) = z
        simp <;> rfl }
  snd :=
    { toFun := fun uz => ⟨((1 - (uz.1 : ℝ)) * (a - 1) +
          (uz.1 : ℝ) * uz.2.1.1, uz.2.1.2),
        upper_half_ray_interpolate_mem S a uz.1 uz.2.1.1 uz.2.1.2 uz.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro z
        apply Subtype.ext
        change ((1 - (0 : ℝ)) * (a - 1) + 0 * z.1.1, z.1.2) = (a - 1, z.1.2)
        simp <;> rfl
      map_one_left := by
        intro z
        apply Subtype.ext
        change ((1 - (1 : ℝ)) * (a - 1) + 1 * z.1.1, z.1.2) = z.1
        simp <;> rfl }
  w := rfl

/-- Homology supported on a real tangential upper half-ray vanishes in every degree.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_upper_half_ray_homology_subsingleton
    (Y : TopCat.{0}) (S : Set Y) (a : ℝ) (n : ℕ) :
    Subsingleton (RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | a ≤ z.1 ∧ z.2 ∈ S}ᶜ) n) := by
  apply properCycle_relative_homology_subsingleton_of_contraction
    (TopCat.of (ℝ × Y)) _ (properCycle_upper_half_ray_push Y S a)
    (fun z h => ?_) (properCycle_upper_half_ray_contraction Y S a) n
  have := h.1
  change a ≤ a - 1 at this
  linarith

end HodgeLean.Foundations.QuotientDuality
