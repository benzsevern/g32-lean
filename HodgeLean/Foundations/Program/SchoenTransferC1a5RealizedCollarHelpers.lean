import HodgeLean.Foundations.Program.SchoenTransferC1a5SimplexCollarHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5TopHelpers

/-! Neighborhood maps on actual standard simplex realizations.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- The actual realized boundary maps into its coordinate neighborhood.
Source: Hatcher §2.1, Theorem 2.20, via the literal realization coordinate homeomorphism. -/
def c1a5_realized_boundary_to_collar (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) ⟶ TopCat.of (c1a5_simplex_collar n) :=
  TopCat.ofHom ((c1a5_coordinate_boundary_to_collar n).comp
    (toContinuousMap (c1a5_boundary_coordinate_homeomorph n)))

example (n : ℕ) := c1a5_realized_boundary_to_collar n

/-- Coordinate neighborhoods map into the literal standard simplex realization.
Source: Mathlib SimplexCategory.toTopHomeo. -/
def c1a5_collar_to_realized_simplex (n : ℕ) :
    TopCat.of (c1a5_simplex_collar n) ⟶ SSet.toTop.obj (Δ[n + 1] : SSet.{0}) :=
  TopCat.ofHom ⟨fun p ↦ ⦋n + 1⦌.toTopHomeo.symm p.val,
    ⦋n + 1⦌.toTopHomeo.symm.continuous.comp continuous_subtype_val⟩

example (n : ℕ) := c1a5_collar_to_realized_simplex n

/-- The neighborhood maps factor exactly the actual realized boundary inclusion.
Source: Mathlib SimplexCategory.toTopHomeo and the actual boundary coordinate homeomorphism. -/
lemma c1a5_realized_boundary_collar_factor (n : ℕ) :
    c1a5_realized_boundary_to_collar n ≫ c1a5_collar_to_realized_simplex n =
      SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι := by
  ext x
  change ⦋n + 1⦌.toTopHomeo.symm ((c1a5_boundary_coordinate_homeomorph n x).val) = _
  change ⦋n + 1⦌.toTopHomeo.symm
    (⦋n + 1⦌.toTopHomeo (SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι x)) = _
  exact Homeomorph.symm_apply_apply _ _

/-- The coordinate neighborhood maps as an open subspace of the actual realization.
Source: Mathlib IsOpen.isOpenEmbedding_subtypeVal and SimplexCategory.toTopHomeo. -/
lemma c1a5_collar_to_realized_simplex_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (c1a5_collar_to_realized_simplex n) :=
  ⦋n + 1⦌.toTopHomeo.symm.isOpenEmbedding.comp
    (c1a5_simplex_collar_isOpen n).isOpenEmbedding_subtypeVal

/-- The coordinate boundary neighborhood inclusion induces integral homology isomorphisms.
Source: Hatcher §2.1, homotopy invariance and the explicit strong neighborhood deformation. -/
lemma c1a5_coordinate_boundary_collar_chains_quasiIso (n : ℕ) :
    QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (c1a5_coordinate_boundary_to_collar n)))
      (ModuleCat.of ℤ ℤ)) := by
  let A := TopCat.of {p : StdSimplex ℝ (Fin (n + 2)) // ∃ i : Fin (n + 2), p.weights i = 0}
  let U := TopCat.of (c1a5_simplex_collar n)
  let i : A ⟶ U := TopCat.ofHom (c1a5_coordinate_boundary_to_collar n)
  let r : U ⟶ A := TopCat.ofHom (c1a5_simplex_collar_retract n)
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  let E : HomotopyEquiv (F.obj A) (F.obj U) :=
    { hom := F.map i
      inv := F.map r
      homotopyHomInvId := Homotopy.ofEq (by
        rw [← F.map_comp]
        have hir : i ≫ r = 𝟙 A := by
          exact congrArg TopCat.ofHom (c1a5_simplex_collar_retract_boundary n)
        rw [hir, F.map_id])
      homotopyInvHomId := by
        have H : TopCat.Homotopy (r ≫ i) (𝟙 U) := (c1a5_simplex_collar_homotopy n).symm
        have h := H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
        change Homotopy (F.map (r ≫ i)) (F.map (𝟙 U)) at h
        rw [F.map_comp, F.map_id] at h
        exact h }
  exact E.quasiIso_hom

/-- The literal realized boundary inclusion into its neighborhood preserves integral homology.
Source: Hatcher §2.1, homotopy invariance; the actual boundary coordinate homeomorphism. -/
lemma c1a5_realized_boundary_collar_chains_quasiIso (n : ℕ) :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map (c1a5_realized_boundary_to_collar n))
      (ModuleCat.of ℤ ℤ)) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have : QuasiIso (F.map (TopCat.ofHom (c1a5_coordinate_boundary_to_collar n))) :=
    c1a5_coordinate_boundary_collar_chains_quasiIso n
  have hw : c1a5_realized_boundary_to_collar n =
      (TopCat.isoOfHomeo (c1a5_boundary_coordinate_homeomorph n)).hom ≫
        TopCat.ofHom (c1a5_coordinate_boundary_to_collar n) := by
    ext x
    rfl
  change QuasiIso (F.map (c1a5_realized_boundary_to_collar n))
  rw [hw, F.map_comp]
  infer_instance

end HodgeLean.Foundations.Program
