import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineHalfBoundaryComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleHalfRayPairGeometry

/-! # The specified singular-subcomplex sequence for the affine suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Singular simplices in the actual upper-half-ray complement. -/
abbrev properCycle_affine_upper_half_subcomplex (d : ℕ) :=
  subsetSingularSubcomplex (TopCat.of (ℝ × (Fin d → ℝ))) {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ

/-- Singular simplices in the actual lower-half-ray complement. -/
abbrev properCycle_affine_lower_half_subcomplex (d : ℕ) :=
  subsetSingularSubcomplex (TopCat.of (ℝ × (Fin d → ℝ))) {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ

/-- The actual intersection subcomplex is the original axis-complement singular subcomplex. -/
theorem properCycle_affine_half_ray_subcomplex_intersection (d : ℕ) :
    properCycle_affine_upper_half_subcomplex d ⊓ properCycle_affine_lower_half_subcomplex d =
      subsetSingularSubcomplex (TopCat.of (ℝ × (Fin d → ℝ))) {z | z.2 ≠ 0} := by
  rw [← subsetSingularSubcomplex_inter, properCycle_half_ray_complement_intersection]

/-- The original signed quotient sequence for the two specified half-ray complements. -/
def properCycle_affine_half_ray_sequence (d : ℕ) : ShortComplex (ChainCategory ℚ) :=
  properCycle_subcomplex_quotient_sequence (properCycle_affine_upper_half_subcomplex d)
    (properCycle_affine_lower_half_subcomplex d)

/-- The left term of the actual sequence retains the original axis-complement relative chains. -/
def properCycle_affine_half_ray_left_iso (d : ℕ) :
    (properCycle_affine_half_ray_sequence d).X₁ ≅
      (relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d) :=
  properCycle_subcomplex_quotient_iso_of_eq (properCycle_affine_half_ray_subcomplex_intersection d) ≪≫
    properCycle_subset_subcomplex_relative_iso (TopCat.of (ℝ × (Fin d → ℝ))) {z | z.2 ≠ 0}

/-- The actual left comparison retains its original ambient chain projection. -/
theorem properCycle_affine_half_ray_left_projection (d : ℕ) :
    cokernel.π (SSet.chainComplexMap
      (properCycle_affine_upper_half_subcomplex d ⊓ properCycle_affine_lower_half_subcomplex d).ι
        (ModuleCat.of ℚ ℚ)) ≫ (properCycle_affine_half_ray_left_iso d).hom =
      relativeChainProjection ℚ (properCycle_real_equator_pair d) := by
  unfold properCycle_affine_half_ray_left_iso
  rw [Iso.trans_hom, ← Category.assoc]
  change (_ ≫ properCycle_subcomplex_quotient_map (properCycle_affine_half_ray_subcomplex_intersection d).le) ≫ _ = _
  rw [properCycle_subcomplex_quotient_projection, properCycle_subset_subcomplex_relative_projection]

/-- The upper-half-ray quotient retains its actual relative pair. -/
abbrev properCycle_affine_half_ray_upper_iso (d : ℕ) :=
  properCycle_subset_subcomplex_relative_iso (TopCat.of (ℝ × (Fin d → ℝ)))
    {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ

/-- The lower-half-ray quotient retains its actual relative pair. -/
abbrev properCycle_affine_half_ray_lower_iso (d : ℕ) :=
  properCycle_subset_subcomplex_relative_iso (TopCat.of (ℝ × (Fin d → ℝ)))
    {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ

/-- The first component of the actual left sequence map is the original positive relative inclusion. -/
theorem properCycle_affine_half_ray_left_fst (d : ℕ) :
    (properCycle_affine_half_ray_sequence d).f ≫ biprod.fst ≫
        (properCycle_affine_half_ray_upper_iso d).hom =
      (properCycle_affine_half_ray_left_iso d).hom ≫
        (relativeChainFunctor ℚ).map (properCycle_equator_to_upper_half_ray_pair d) := by
  let X := TopCat.of (ℝ × (Fin d → ℝ))
  have hEP : {z : X | z.2 ≠ 0} ⊆ {z : X | 0 ≤ z.1 ∧ z.2 = 0}ᶜ :=
    fun _ hz hp => hz hp.2
  have hn := properCycle_subset_subcomplex_relative_naturality X hEP
  dsimp only [properCycle_affine_half_ray_sequence, properCycle_subcomplex_quotient_sequence]
  rw [biprod.lift_fst_assoc]
  unfold properCycle_affine_half_ray_left_iso
  rw [Iso.trans_hom, Category.assoc]
  change _ = properCycle_subcomplex_quotient_map
    (properCycle_affine_half_ray_subcomplex_intersection d).le ≫
      ((properCycle_subset_subcomplex_relative_iso X {z | z.2 ≠ 0}).hom ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom (𝟙 X) hEP))
  rw [← hn, ← Category.assoc, properCycle_subcomplex_quotient_map_comp]

/-- The second component of the actual left sequence map is the original negative relative inclusion. -/
theorem properCycle_affine_half_ray_left_snd (d : ℕ) :
    (properCycle_affine_half_ray_sequence d).f ≫ biprod.snd ≫
        (properCycle_affine_half_ray_lower_iso d).hom =
      -((properCycle_affine_half_ray_left_iso d).hom ≫
        (relativeChainFunctor ℚ).map (properCycle_equator_to_lower_half_ray_pair d)) := by
  let X := TopCat.of (ℝ × (Fin d → ℝ))
  have hEQ : {z : X | z.2 ≠ 0} ⊆ {z : X | z.1 ≤ 0 ∧ z.2 = 0}ᶜ :=
    fun _ hz hp => hz hp.2
  have hn := properCycle_subset_subcomplex_relative_naturality X hEQ
  dsimp only [properCycle_affine_half_ray_sequence, properCycle_subcomplex_quotient_sequence]
  rw [biprod.lift_snd_assoc, Preadditive.neg_comp]
  congr 1
  unfold properCycle_affine_half_ray_left_iso
  rw [Iso.trans_hom, Category.assoc]
  change _ = properCycle_subcomplex_quotient_map
    (properCycle_affine_half_ray_subcomplex_intersection d).le ≫
      ((properCycle_subset_subcomplex_relative_iso X {z | z.2 ≠ 0}).hom ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom (𝟙 X) hEQ))
  rw [← hn, ← Category.assoc, properCycle_subcomplex_quotient_map_comp]

/-- The specified affine half-ray quotient sequence retains the constructed short exact structure. -/
theorem properCycle_affine_half_ray_shortExact (d : ℕ) :
    (properCycle_affine_half_ray_sequence d).ShortExact :=
  properCycle_subcomplex_quotient_sequence_shortExact (TopCat.of (ℝ × (Fin d → ℝ)))
    (properCycle_affine_upper_half_subcomplex d) (properCycle_affine_lower_half_subcomplex d)

end HodgeLean.Foundations.QuotientDuality
