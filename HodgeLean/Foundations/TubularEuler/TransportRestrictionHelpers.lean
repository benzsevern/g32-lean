import HodgeLean.Foundations.TubularEuler.TransferDefs

/-! # Restriction of the supplied transported class

The actual excision inverse cancels on the original tube neighbourhood.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

theorem transportedClass_neighbourhood_restriction
    (t : NormalTube ι k v j hj) (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    relativeCohomologyMap ℚ (2 * k) (i1_neighbourhoodInclusion k (i1_normalFibre j) t.source)
      (transportedClass ι k v j hj t c) =
    relativeCohomologyMap ℚ (2 * k) (tubePairMap ι k v j hj t) c := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  exact (LinearEquiv.ofBijective _
    (i1_neighbourhoodInclusion_relativeCohomology_bijective k (i1_normalFibre j)
      t.source t.contains_zero (2 * k))).apply_symm_apply _

theorem transportedClass_pair_pullback
    (t : NormalTube ι k v j hj) (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    {P : TopPair} (f : P ⟶ TopPair.ofSubset
      (X := i1_totalSpace k (i1_normalFibre j)) (i1_zeroSupport k (i1_normalFibre j))ᶜ)
    (fN : P ⟶ i1_neighbourhoodPair k (i1_normalFibre j) t.source)
    (hfactor : fN ≫ i1_neighbourhoodInclusion k (i1_normalFibre j) t.source = f) :
    relativeCohomologyMap ℚ (2 * k) f (transportedClass ι k v j hj t c) =
      relativeCohomologyMap ℚ (2 * k) (fN ≫ tubePairMap ι k v j hj t) c := by
  rw [← hfactor, relativeCohomologyMap_comp, LinearMap.comp_apply,
    transportedClass_neighbourhood_restriction,
    relativeCohomologyMap_comp, LinearMap.comp_apply]

#print axioms transportedClass_pair_pullback
#print axioms transportedClass_neighbourhood_restriction

end HodgeLean.Foundations.TubularEuler
