import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportSuspension
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedRealSuspension

/-! # The actual support suspension at the specified Euclidean point
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The general support left comparison specializes to the original affine left comparison with its literal ambient projection.
Source: properCycle_real_support_left_projection; properCycle_affine_half_ray_left_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_left_standard_comparison (d : ℕ) :
    (properCycle_real_support_left_iso (TopCat.of (Fin d → ℝ)) {0}).hom =
      (properCycle_affine_half_ray_left_iso d).hom := by
  apply (cancel_epi (cokernel.π (SSet.chainComplexMap
    (properCycle_affine_upper_half_subcomplex d ⊓ properCycle_affine_lower_half_subcomplex d).ι
      (ModuleCat.of ℚ ℚ)))).mp
  exact (properCycle_real_support_left_projection (TopCat.of (Fin d → ℝ)) {0}).trans
    (properCycle_affine_half_ray_left_projection d).symm

/-- The zero slice over the base origin is the actual product origin, through the identity point map.
Source: Hatcher, Algebraic Topology, section 2.2, pointed relative pairs.
HC no distance; AV milestone no distance. -/
def properCycle_real_point_support_pair_iso (Y : TopCat.{0}) [Zero Y] :
    TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      {z | z.1 = 0 ∧ z.2 ∈ ({0} : Set Y)}ᶜ ≅
    TopPair.ofSubset (X := TopCat.of (ℝ × Y)) ({(0,0)}ᶜ : Set (ℝ × Y)) :=
  TopPair.isoOfSubset (Homeomorph.refl _) (by
    intro z
    change z ≠ (0,0) ↔ ¬ (z.1 = 0 ∧ z.2 = 0)
    exact not_congr Prod.ext_iff)

/-- The general right support comparison specializes to the specified original affine comparison after the actual point-pair identification.
Source: properCycle_affine_half_ray_right_comparison; properCycle_subset_union_quotient_homology_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_right_standard_comparison (d n : ℕ) :
    (properCycle_real_support_right_iso (TopCat.of (Fin d → ℝ)) {0}
        isClosed_singleton n).hom ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_point_support_pair_iso (TopCat.of (Fin d → ℝ))).hom) n =
      (properCycle_affine_half_ray_right_homology_iso d n).hom := by
  dsimp only [properCycle_real_support_right_iso, id_eq,
    properCycle_subset_union_quotient_homology_iso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, asIso_hom,
    properCycle_affine_half_ray_right_homology_iso]
  dsimp only [HomologicalComplex.homologyFunctor]
  simp only [← HomologicalComplex.homologyMap_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  unfold properCycle_affine_half_ray_right_comparison
  congr 1

/-- The general signed support suspension agrees with the original normalized real suspension through the literal point-pair identification.
Source: properCycle_real_support_left_standard_comparison; properCycle_real_support_right_standard_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_standard_comparison (d : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_point_support_pair_iso (TopCat.of (Fin d → ℝ))).inv) (d+1) ≫
      (properCycle_real_support_suspension_iso (TopCat.of (Fin d → ℝ)) {0}
        isClosed_singleton d).hom =
      ModuleCat.ofHom (properCycle_normalized_real_suspension d) := by
  let R := properCycle_real_support_right_iso (TopCat.of (Fin d → ℝ)) {0}
    isClosed_singleton (d+1)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (d+1)
  let J := H.mapIso ((relativeChainFunctor ℚ).mapIso
    (properCycle_real_point_support_pair_iso (TopCat.of (Fin d → ℝ))))
  have hr : R ≪≫ J = properCycle_affine_half_ray_right_homology_iso d (d+1) := by
    apply Iso.ext
    exact properCycle_real_support_right_standard_comparison d (d+1)
  have hi : J.inv ≫ R.inv = (properCycle_affine_half_ray_right_homology_iso d (d+1)).inv :=
    congrArg Iso.inv hr
  have hl : properCycle_real_support_left_iso (TopCat.of (Fin d → ℝ)) {0} =
      properCycle_affine_half_ray_left_iso d :=
    Iso.ext (properCycle_real_support_left_standard_comparison d)
  unfold properCycle_real_support_suspension_iso
  dsimp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
  rw [hl]
  change J.inv ≫ (R.inv ≫ _ ≫ _ ≫ _) = _
  simp only [← Category.assoc]
  rw [hi]
  rfl

/-- The actual general support suspension sends the specified standard product local class to minus the specified base local class.
Source: properCycle_real_support_suspension_standard_comparison; properCycle_normalized_real_suspension_standard.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_standard (d : ℕ) :
    (properCycle_real_support_suspension_iso (TopCat.of (Fin d → ℝ)) {0}
      isClosed_singleton d).hom.hom
      (relativeHomologyMap ℚ (d+1)
        (properCycle_real_point_support_pair_iso (TopCat.of (Fin d → ℝ))).inv
        (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
          (standardLocalClass ℚ (d+1)))) = -standardLocalClass ℚ d := by
  have h := ConcreteCategory.congr_hom
    (properCycle_real_support_suspension_standard_comparison d)
    (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
      (standardLocalClass ℚ (d+1)))
  exact h.trans (properCycle_normalized_real_suspension_standard d)

end HodgeLean.Foundations.QuotientDuality
