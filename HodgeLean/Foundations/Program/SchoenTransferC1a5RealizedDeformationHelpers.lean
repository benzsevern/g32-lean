import HodgeLean.Foundations.Program.SchoenTransferC1a5RealizedCollarHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachedChainsHelpers

/-! Deformation data for neighborhoods of literal realized simplex boundaries.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Retraction from the coordinate neighborhood to the literal realized boundary.
Source: Hatcher §2.1, Theorem 2.20, radial boundary deformation in realization coordinates. -/
def c1a5_collar_to_realized_boundary (n : ℕ) :
    TopCat.of (c1a5_simplex_collar n) ⟶
      SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) :=
  TopCat.ofHom (c1a5_simplex_collar_retract n) ≫
    (TopCat.isoOfHomeo (c1a5_boundary_coordinate_homeomorph n)).inv

example (n : ℕ) := c1a5_collar_to_realized_boundary n

/-- The literal boundary neighborhood retraction fixes the boundary.
Source: the coordinate boundary retraction and its realization homeomorphism. -/
lemma c1a5_realized_boundary_collar_retract (n : ℕ) :
    c1a5_realized_boundary_to_collar n ≫ c1a5_collar_to_realized_boundary n =
      𝟙 (SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet)) := by
  ext x
  change (c1a5_boundary_coordinate_homeomorph n).symm
    (c1a5_simplex_collar_retract n
      (c1a5_coordinate_boundary_to_collar n (c1a5_boundary_coordinate_homeomorph n x))) = x
  have h := ContinuousMap.congr_fun (c1a5_simplex_collar_retract_boundary n)
    (c1a5_boundary_coordinate_homeomorph n x)
  change c1a5_simplex_collar_retract n
    (c1a5_coordinate_boundary_to_collar n (c1a5_boundary_coordinate_homeomorph n x)) =
      c1a5_boundary_coordinate_homeomorph n x at h
  rw [h]
  exact Homeomorph.symm_apply_apply _ _

/-- The radial coordinate homotopy has the literal realized boundary retraction as its endpoint.
Source: Hatcher §2.1, Theorem 2.20, boundary neighborhood deformation. -/
def c1a5_realized_boundary_collar_homotopy (n : ℕ) :
    TopCat.Homotopy (𝟙 (TopCat.of (c1a5_simplex_collar n)))
      (c1a5_collar_to_realized_boundary n ≫ c1a5_realized_boundary_to_collar n) where
  toFun := c1a5_simplex_collar_homotopy n
  continuous_toFun := (c1a5_simplex_collar_homotopy n).continuous
  map_zero_left := (c1a5_simplex_collar_homotopy n).map_zero_left
  map_one_left p := by
    change c1a5_simplex_collar_homotopy n (1, p) =
      c1a5_coordinate_boundary_to_collar n
        (c1a5_boundary_coordinate_homeomorph n
          ((c1a5_boundary_coordinate_homeomorph n).symm (c1a5_simplex_collar_retract n p)))
    rw [Homeomorph.apply_symm_apply]
    exact (c1a5_simplex_collar_homotopy n).map_one_left p

example (n : ℕ) := c1a5_realized_boundary_collar_homotopy n

/-- The literal neighborhood deformation fixes the boundary throughout the interval.
Source: the fixed coordinate boundary deformation and the realization homeomorphism. -/
lemma c1a5_realized_boundary_collar_homotopy_fixed (n : ℕ) (s : unitInterval)
    (a : SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet)) :
    c1a5_realized_boundary_collar_homotopy n (s, c1a5_realized_boundary_to_collar n a) =
      c1a5_realized_boundary_to_collar n a :=
  c1a5_simplex_collar_homotopy_fixed n s (c1a5_boundary_coordinate_homeomorph n a)

/-- Attaching the actual positive-dimensional simplex collar preserves the base's integral homology.
Source: Hatcher §2.1, homotopy invariance for the boundary neighborhood attachment. -/
lemma c1a5_realized_attached_collar_chains_quasiIso (n : ℕ) (B : TopCat.{0})
    (t : SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) ⟶ B) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (pushout.inl t (c1a5_realized_boundary_to_collar n))) :=
  c1a5_attached_collar_chains_quasiIso t _ _
    (c1a5_realized_boundary_collar_retract n)
    (c1a5_realized_boundary_collar_homotopy n)
    (c1a5_realized_boundary_collar_homotopy_fixed n)

end HodgeLean.Foundations.Program
