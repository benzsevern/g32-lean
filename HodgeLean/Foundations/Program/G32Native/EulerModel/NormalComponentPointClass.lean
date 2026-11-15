import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalComponentPoint

/-! # The specified point coclass on the actual component-cycle support -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The point-support pair isomorphism retains the literal coordinate-point component cycle. -/
def normalComponentPointPairIso
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    TopPair.ofSubset (X := TopCat.of (Projectivization ℂ (ℂ × (Fin k → ℂ))))
      ({normalProjectiveBase k} : Set _)ᶜ ≅
    TopPair.ofSubset (X := a3b4_an Q.hom)
      (a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ))ᶜ :=
  TopPair.isoOfSubset (normalComponentHomeomorph k eQ)
    (fun p => not_congr (normalComponentHomeomorph_cycle_support k eQ p))

/-- The global point coclass on the actual coordinate-point component support. -/
def normalComponentPointCoclass
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    s2e_supportedClass Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k :=
  relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).inv
    (normalProjectivePointCoclass k)

#print axioms normalComponentPointPairIso
#print axioms normalComponentPointCoclass
/-- The point coclass on the literal component-cycle carrier retains the same globally normalized model class. -/
theorem normalComponentPointCoclass_model
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).hom
      (normalComponentPointCoclass k eQ) = normalProjectivePointCoclass k := by
  unfold normalComponentPointCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Iso.hom_inv_id, relativeCohomologyMap_id, LinearMap.id_apply]

#print axioms normalComponentPointCoclass_model
/-- The point coclass on the actual component-cycle carrier has the specified normalized affine-chart pullback. -/
theorem normalComponentPointCoclass_chart
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    relativeCohomologyMap ℚ (2 * k)
      (normalProjectiveChartPair k ≫ (normalComponentPointPairIso k eQ).hom)
      (normalComponentPointCoclass k eQ) = HodgeLean.RealDefs.normalizedPointCoclass k := by
  rw [relativeCohomologyMap_comp, LinearMap.comp_apply,
    normalComponentPointCoclass_model, normalProjectivePointCoclass_chart]

#print axioms normalComponentPointCoclass_chart
end HodgeLean.Foundations.Program.G32Native.EulerModel
