import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalComponentPointClass
import HodgeLean.Foundations.AlgebraicTopology.RelativeCohomology.ProductTrace

/-! # Absolute transport of the same actual normalized coordinate-point coclass -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The inverse actual point-support chart retains the supplied component isomorphism on the same underlying absolute map. -/
theorem normalComponentPointPairIso_inv_fst_square {Q : Over (Spec ↧ℂ)}
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    [IsIntegral (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap
        (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).hom.left)).left] :
    TopPair.Hom.fst (normalComponentPointPairIso k eQ).inv =
      TopCat.ofHom (Point.continuousMap eQ.hom) ≫
        TopPair.Hom.fst (normalComponentPointPairIso k
          (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))).inv := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change (normalProjectiveSchemeHomeomorph k).symm (Point.map eQ.hom p) =
    (normalProjectiveSchemeHomeomorph k).symm (Point.map (𝟙 _) (Point.map eQ.hom p))
  rw [Point.map_id]

#print axioms normalComponentPointPairIso_inv_fst_square
/-- The absolute class of the same actual coordinate-point coclass pulls back exactly through the supplied component isomorphism. -/
theorem normalComponentPointCoclass_absolute_iso {Q : Over (Spec ↧ℂ)}
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    [IsIntegral (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap
        (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).hom.left)).left] :
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (normalComponentPointCoclass k eQ) =
      s2e_pullback ℚ eQ.hom (2 * k)
        (s2e_classToAbsolute
          (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
          (s2e_componentCycle (s2c_subschemeι
            (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
            ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap
              (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).hom.left)) ℚ) k
          (normalComponentPointCoclass k
            (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))))) := by
  have hQ := RelativeTrace.forget_naturality (normalComponentPointPairIso k eQ).inv
    (2 * k) (normalProjectivePointCoclass k)
  have hP := RelativeTrace.forget_naturality (normalComponentPointPairIso k
    (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))).inv
      (2 * k) (normalProjectivePointCoclass k)
  rw [normalComponentPointPairIso_inv_fst_square, cohomologyMap_comp,
    LinearMap.comp_apply] at hQ
  exact hQ.trans (congrArg
    (cohomologyMap ℚ (2 * k) (TopCat.ofHom (Point.continuousMap eQ.hom))) hP.symm)

#print axioms normalComponentPointCoclass_absolute_iso
end HodgeLean.Foundations.Program.G32Native.EulerModel
