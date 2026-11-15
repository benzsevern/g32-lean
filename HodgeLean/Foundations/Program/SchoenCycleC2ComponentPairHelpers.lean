import HodgeLean.Foundations.Program.SchoenCycleC2OpenSupportHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual map of supported pairs for a component and its open-immersion image. -/
def s2e_componentOpenPairMap
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (j : Q ⟶ V) (i : V ⟶ W)
    [IsClosedImmersion j.left] [IsOpenImmersion i.left]
    [IsClosedImmersion (j ≫ i).left] :
    TopPair.ofSubset (X := a3b4_an V.hom) (a3b4_cycleSupport V.hom (s2e_componentCycle j ℚ))ᶜ ⟶
    TopPair.ofSubset (X := a3b4_an W.hom) (a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ))ᶜ :=
  a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap i))
    (a3b4_cycleSupport V.hom (s2e_componentCycle j ℚ))
    (a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ))
    (fun x hx => (Set.ext_iff.mp (s2e_componentCycle_support_open_preimage j i) x).mpr hx)

/-- Supported pullback along the actual component pair map is bijective. -/
theorem s2e_componentOpenPairMap_bijective
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (j : Q ⟶ V) (i : V ⟶ W)
    [IsClosedImmersion j.left] [IsOpenImmersion i.left]
    [IsClosedImmersion (j ≫ i).left]
    (hf : Topology.IsOpenEmbedding (Point.map i))
    (hcover : a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ) ⊆
      Set.range (Point.map i)) (k : ℕ) :
    Function.Bijective (relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap j i)) := by
  have hT : IsClosed (a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ)) := by
    rw [s2e_componentCycle_analytic_support]
    exact (j ≫ i).left.isClosedEmbedding.isClosed_range.preimage
      (ComplexPoint.continuous_underlying_to_zariski W)
  exact s2e_openEmbedding_supportPairMap_bijective (TopCat.ofHom (Point.continuousMap i)) hf
    _ _ hT hcover
    (fun x => (Set.ext_iff.mp (s2e_componentCycle_support_open_preimage j i) x).symm) (2 * k)

end HodgeLean.Foundations.Program
