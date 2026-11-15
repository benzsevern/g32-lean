import HodgeLean.Adapters.CycleClassDivisorProduct3
import HodgeLean.Adapters.CycleClassFlatComparisonDefs
import HodgeLean.Adapters.CupProductOf

/-! # Supported transport of the relative cup

The pair identification inserts the full-open witness. The product transports
ccm15's relative cup through the supported singular comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Canonical full-open pair identification, with no change of support.
Source: Bredon, Sheaf Theory, II, relative cohomology; `Homeomorph.Set.univ`. -/
def ccm16_fullPairIso (Y : TopCat.{0}) (S : Set Y) :
    TopPair.ofSubset Sᶜ ≅ neighborhoodSupportComplementPair Set.univ S :=
  TopPair.isoOfSubset (Homeomorph.Set.univ Y).symm (fun _ => Iff.rfl)

example : TopPair.Hom.fst (ccm16_fullPairIso (TopCat.of Bool) {true}).hom true =
    ⟨true, Set.mem_univ true⟩ := rfl

/-- Pullback along the canonical pair isomorphism, in the contravariant direction.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of relative cohomology. -/
def ccm16_pairTransport (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair Set.univ S) n ≃ₗ[ℚ]
      RelativeCohomology ℚ (TopPair.ofSubset Sᶜ) n where
  toLinearMap := relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).hom
  invFun := relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).inv
  left_inv a := by
    change ((relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).inv).comp
      (relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).hom)) a = a
    rw [← relativeCohomologyMap_comp, Iso.inv_hom_id, relativeCohomologyMap_id]
    rfl
  right_inv a := by
    change ((relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).hom).comp
      (relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).inv)) a = a
    rw [← relativeCohomologyMap_comp, Iso.hom_inv_id, relativeCohomologyMap_id]
    rfl

example : ccm16_pairTransport (TopCat.of Bool) {true} 0 0 = 0 := map_zero _

end HodgeLean.Adapters
