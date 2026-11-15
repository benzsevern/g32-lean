import HodgeLean.Foundations.Program.G32Native.CompactNearestPoint
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Compact nearest-point minima in local coordinates

At an interior point of the compact carrier, ambient minimization gives the
ordinary local minimum needed for the critical equation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Set Filter Topology
namespace HodgeLean.Foundations.TubularEuler

/-- A distance minimizer in the interior of a compact carrier is a local
squared-distance minimizer in any chart containing that base point.
Source: definition of a local minimum and continuity of a chart inverse;
Lee, Introduction to Smooth Manifolds, second edition, Euclidean normal
neighbourhood construction.
HC no distance; AV milestone no distance. -/
theorem nearestPoint_chart_localMin
    {M B F : Type*} [TopologicalSpace M] [TopologicalSpace B]
    [NormedAddCommGroup F]
    (C : Set M) (e : M → F) (a : OpenPartialHomeomorph M B) (c : C)
    (hc : (c : M) ∈ a.source) (hcC : (c : M) ∈ interior C) (y : F)
    (hmin : ∀ z : C, dist y (e c) ≤ dist y (e z)) :
    IsLocalMin (fun b => ‖e (a.symm b) - y‖ ^ 2) (a c) := by
  have ht : a c ∈ a.target := a.map_source hc
  have hpre : ∀ᶠ b in 𝓝 (a c), a.symm b ∈ interior C :=
    (a.symm.continuousAt ht).eventually
      (isOpen_interior.mem_nhds (by simpa only [a.left_inv hc] using hcC))
  filter_upwards [hpre] with b hb
  rw [a.left_inv hc]
  have hn := hmin ⟨a.symm b, interior_subset hb⟩
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev y (e c),
    norm_sub_rev y (e (a.symm b))] at hn
  nlinarith [norm_nonneg (e c - y), norm_nonneg (e (a.symm b) - y)]

#print axioms nearestPoint_chart_localMin

end HodgeLean.Foundations.TubularEuler
