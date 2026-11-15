import HodgeLean.Foundations.QuotientDuality.LocalNormalizedOverlapAgreement

/-! Comparing ambient orientation classes through a common open subscheme. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem common_open_orientation_transport
    (S X₁ X₂ Y : Over (Spec ↧ℂ))
    [T2Space (ComplexPoint S)] [T2Space (ComplexPoint X₁)] [T2Space (ComplexPoint X₂)]
    (g₁ : S ⟶ X₁) (g₂ : S ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    [IsOpenImmersion f₁.left] [IsOpenImmersion f₂.left]
    (hsq : g₁ ≫ f₁ = g₂ ≫ f₂) (n : ℕ)
    (o₁ : LocalRationalOrientation (TopCat.of (ComplexPoint X₁)) n)
    (o₂ : LocalRationalOrientation (TopCat.of (ComplexPoint X₂)) n)
    (z : ComplexPoint S)
    (heq : (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap g₁))
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points g₁) n o₁).generator z =
      (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap g₂))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points g₂) n o₂).generator z) :
    HEq (openEmbeddingOrientationFamily (TopCat.ofHom (Point.continuousMap f₁))
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points f₁) n o₁ (Point.map g₁ z))
      (openEmbeddingOrientationFamily (TopCat.ofHom (Point.continuousMap f₂))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points f₂) n o₂ (Point.map g₂ z)) := by
  let p₁ := (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap g₁))
    (HodgeLean.Foundations.ComplexTopology.openImmersion_points g₁) n o₁).generator z
  let p₂ := (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap g₂))
    (HodgeLean.Foundations.ComplexTopology.openImmersion_points g₂) n o₂).generator z
  have hcomp (A B : Over (Spec ↧ℂ)) [T2Space (ComplexPoint A)] (g : S ⟶ A) (f : A ⟶ B)
      [IsOpenImmersion g.left] [IsOpenImmersion f.left]
      (o : LocalRationalOrientation (TopCat.of (ComplexPoint A)) n) :
      openEmbeddingOrientationFamily (TopCat.ofHom (Point.continuousMap f))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points f) n o (Point.map g z) =
      relativeHomologyMap ℚ n
        (imagePointPairMap (TopCat.ofHom (Point.continuousMap (g ≫ f)))
          ((HodgeLean.Foundations.ComplexTopology.openImmersion_points f).injective.comp
            (HodgeLean.Foundations.ComplexTopology.openImmersion_points g).injective) z)
        ((openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap g))
          (HodgeLean.Foundations.ComplexTopology.openImmersion_points g) n o).generator z) := by
    have H := openEmbeddingOrientationPullback_generator (TopCat.ofHom (Point.continuousMap g))
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points g) n o z
    exact (congrArg (relativeHomologyMap ℚ n
      (imagePointPairMap (TopCat.ofHom (Point.continuousMap f))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points f).injective (Point.map g z))) H).symm.trans
      (point_homology_map_comp (TopCat.ofHom (Point.continuousMap g))
        (TopCat.ofHom (Point.continuousMap f))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points g).injective
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points f).injective z n
        ((openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap g))
          (HodgeLean.Foundations.ComplexTopology.openImmersion_points g) n o).generator z))
  have Hmid : HEq
      (relativeHomologyMap ℚ n (imagePointPairMap (TopCat.ofHom (Point.continuousMap (g₁ ≫ f₁)))
        ((HodgeLean.Foundations.ComplexTopology.openImmersion_points f₁).injective.comp
          (HodgeLean.Foundations.ComplexTopology.openImmersion_points g₁).injective) z) p₁)
      (relativeHomologyMap ℚ n (imagePointPairMap (TopCat.ofHom (Point.continuousMap (g₂ ≫ f₂)))
        ((HodgeLean.Foundations.ComplexTopology.openImmersion_points f₂).injective.comp
          (HodgeLean.Foundations.ComplexTopology.openImmersion_points g₂).injective) z) p₂) := by
    have hp : p₁ = p₂ := heq
    rw [hp]
    have hcongr (u v : S ⟶ Y) (hu : Function.Injective (Point.map u))
        (hv : Function.Injective (Point.map v)) (h : u = v)
        (p : orientationGroup (TopCat.of (ComplexPoint S)) n z) :
        HEq (relativeHomologyMap ℚ n (imagePointPairMap (TopCat.ofHom (Point.continuousMap u)) hu z) p)
          (relativeHomologyMap ℚ n (imagePointPairMap (TopCat.ofHom (Point.continuousMap v)) hv z) p) := by
      cases h
      rfl
    exact hcongr (g₁ ≫ f₁) (g₂ ≫ f₂) _ _ hsq p₂
  exact (heq_of_eq (hcomp X₁ Y g₁ f₁ o₁)).trans (Hmid.trans (heq_of_eq (hcomp X₂ Y g₂ f₂ o₂).symm))

#print axioms common_open_orientation_transport
end HodgeLean.Foundations.QuotientDuality
