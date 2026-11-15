import Mathlib.Algebra.Homology.HomologySequence
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! Detection of actual homology images by cohomology extension. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Surjectivity of the actual cohomology pullback makes the homology pushforward injective. -/
lemma retained_homology_injective_of_cohomology_surjective
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (hs : Function.Surjective (cohomologyMap ℚ n f)) :
    Function.Injective (homologyMap ℚ n f) := by
  intro x y h
  apply Module.eval_apply_injective ℚ
  apply LinearMap.ext
  intro φ
  obtain ⟨a, rfl⟩ := (cohomologyEquivDualHomology ℚ X n).surjective φ
  obtain ⟨b, rfl⟩ := hs a
  change cohomologyEquivDualHomology ℚ X n (cohomologyMap ℚ n f b) x =
    cohomologyEquivDualHomology ℚ X n (cohomologyMap ℚ n f b) y
  rw [cohomologyEquivDualHomology_cohomologyMap,
    cohomologyEquivDualHomology_cohomologyMap, h]

/-- A projection detects a nonzero image through an open carrier whose cohomology extends. -/
lemma retained_image_nonzero_of_detected_projection
    {C U X P : TopCat.{0}} (i : C ⟶ U) (j : U ⟶ X) (π : U ⟶ P)
    (n : ℕ) (c : Homology ℚ C n)
    (hs : Function.Surjective (cohomologyMap ℚ n j))
    (hπ : homologyMap ℚ n π (homologyMap ℚ n i c) ≠ 0) :
    homologyMap ℚ n (i ≫ j) c ≠ 0 := by
  intro h
  rw [homologyMap_comp, LinearMap.comp_apply] at h
  have hinj := retained_homology_injective_of_cohomology_surjective j n hs
  have hzero := hinj (h.trans (map_zero _).symm)
  apply hπ
  rw [hzero, map_zero]

/-- Vanishing in the next relative cohomology degree makes actual subspace homology inclusion injective. -/
lemma retained_homology_inclusion_injective_of_relative_vanishing
    (P : TopPair.{0}) (n : ℕ) [Subsingleton (RelativeCohomology ℚ P (n+1))] :
    Function.Injective (homologyMap ℚ n P.map) := by
  letI : Subsingleton (Module.Dual ℚ (RelativeHomology ℚ P (n+1))) :=
    (relativeCohomologyEquivDualHomology ℚ P (n+1)).symm.injective.subsingleton
  letI : Subsingleton (RelativeHomology ℚ P (n+1)) :=
    (Module.subsingleton_dual_iff ℚ).mp inferInstance
  have hz := ModuleCat.isZero_of_subsingleton (RelativeHomology ℚ P (n+1))
  have hex := (relativeChainShortComplex_shortExact ℚ P).homology_exact₁ (n+1) n
    (ComplexShape.down_mk (n+1) n (by omega))
  exact (ModuleCat.mono_iff_injective _).mp (hex.mono_g (hz.eq_zero_of_src _))

end HodgeLean.Foundations.QuotientDuality
