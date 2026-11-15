import HodgeLean.Foundations.RationalHomologyManifold.RelativeSubdivisionHomotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Concrete kernels of supported relative-chain projections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A relative chain vanishes precisely when its ambient representative comes from the subspace.
Source: Hatcher, Algebraic Topology, section 2.1, the relative singular chain quotient.
HC no distance; AV milestone no distance.
-/
theorem relativeChainProjection_zero_iff (P : TopPair.{0}) (n : ℕ)
    (z : ((chainPairFunctor ℚ).obj P).right.X n) :
    (relativeChainProjection ℚ P).f n z = 0 ↔
      ∃ y : ((chainPairFunctor ℚ).obj P).left.X n,
        ((chainPairFunctor ℚ).obj P).hom.f n y = z := by
  let S := ShortComplex.mk (((chainPairFunctor ℚ).obj P).hom.f n)
    ((relativeChainProjection ℚ P).f n) (by
      have h := congrArg (fun f => f.f n) (subspaceChainMap_relativeChainProjection ℚ P)
      exact h)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P n)
  constructor
  · exact fun hz => (S.moduleCat_exact_iff.mp hS) z hz
  · rintro ⟨y, rfl⟩
    exact S.zero_apply y

#print axioms relativeChainProjection_zero_iff
/-- Equality of supported relative chains means that their ambient difference comes from the subspace.
Source: Hatcher, Algebraic Topology, section 2.1, the relative singular chain quotient.
HC no distance; AV milestone no distance.
-/
theorem relativeChainProjection_eq_iff (P : TopPair.{0}) (n : ℕ)
    (z w : ((chainPairFunctor ℚ).obj P).right.X n) :
    (relativeChainProjection ℚ P).f n z = (relativeChainProjection ℚ P).f n w ↔
      ∃ y : ((chainPairFunctor ℚ).obj P).left.X n,
        ((chainPairFunctor ℚ).obj P).hom.f n y = z - w := by
  rw [← sub_eq_zero, ← map_sub, relativeChainProjection_zero_iff]

#print axioms relativeChainProjection_eq_iff
/-- Every actual relative chain has an ambient singular-chain representative.
Source: Hatcher, Algebraic Topology, section 2.1, the relative singular chain quotient.
HC no distance; AV milestone no distance.
-/
theorem relativeChainProjection_surjective (P : TopPair.{0}) (n : ℕ) :
    Function.Surjective ((relativeChainProjection ℚ P).f n) := by
  letI : Epi ((relativeChainProjection ℚ P).f n) :=
    epi_of_isColimit_cofork
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P n)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

#print axioms relativeChainProjection_surjective
end HodgeLean.Foundations.RationalHomologyManifold
