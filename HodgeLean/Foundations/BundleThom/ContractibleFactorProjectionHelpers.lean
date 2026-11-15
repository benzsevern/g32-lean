import HodgeLean.Foundations.BundleThom.RealNormalCapContractionHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Contractible
import Mathlib.Algebra.Homology.QuasiIso

/-! # Projection along a contractible factor

The projection retains the arbitrary base without a contraction hypothesis on it.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology ContinuousMap
namespace HodgeLean.Foundations.BundleThom

/-- A supplied contraction of the second factor gives a homotopy inverse to first projection.
Source: Hatcher, Algebraic Topology, §0, products and homotopy equivalences. -/
def i1_productProjectionHomotopyEquiv (B Y : Type) [TopologicalSpace B]
    [TopologicalSpace Y] (y : Y)
    (H : ContinuousMap.Homotopy (ContinuousMap.const Y y) (ContinuousMap.id Y)) :
    (B × Y) ≃ₕ B where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := ⟨fun b => (b, y), continuous_id.prodMk continuous_const⟩
  left_inv := ⟨{
    toFun := fun p => (p.2.1, H (p.1, p.2.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun p => by simp
    map_one_left := fun p => by simp }⟩
  right_inv := ContinuousMap.Homotopic.refl _

/-- Projection along any contractible factor induces a rational chain quasi-isomorphism.
Source: Hatcher, Algebraic Topology, §2.1, homotopy invariance of singular homology. -/
theorem i1_productContractibleProjection_quasiIso (B Y : Type) [TopologicalSpace B]
    [TopologicalSpace Y] [ContractibleSpace Y] :
    QuasiIso
      ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ))).map
        (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(B × Y, B)))) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic Y
  let e := i1_productProjectionHomotopyEquiv B Y y H.symm
  exact (singularChainHomotopyEquivOfHomotopyEquiv ℚ e).quasiIso_hom

end HodgeLean.Foundations.BundleThom
