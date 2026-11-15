import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Defs

/-! # A common nearest-point selection on a compact parametrized set

The selection is defined on one Euclidean ambient space. Local differential
arguments can identify its restrictions without independent choices of maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function Filter Set Topology
namespace HodgeLean.Foundations.TubularEuler
namespace CompactNearest

variable {C F : Type*} [TopologicalSpace C] [CompactSpace C] [Nonempty C]
variable [PseudoMetricSpace F] (e : C → F) (he : Continuous e)

/-- One choice of nearest base point in a compact parametrized set.
Source: Mathlib, `IsCompact.exists_isMinOn`.
For an injective parametrization it fixes every point in the image, as shown by
`nearest_fix` below.
HC no distance; AV milestone no distance. -/
def nearest (y : F) : C :=
  (isCompact_univ.exists_isMinOn univ_nonempty
    ((continuous_const : Continuous (fun _ : C => y)).dist he).continuousOn).choose

/-- The chosen base point minimizes ambient distance over the same compact set.
Source: Mathlib, `IsCompact.exists_isMinOn`.
HC no distance; AV milestone no distance. -/
theorem nearest_min (y : F) (c : C) :
    dist y (e (nearest e he y)) ≤ dist y (e c) :=
  (isCompact_univ.exists_isMinOn univ_nonempty
    ((continuous_const : Continuous (fun _ : C => y)).dist he).continuousOn).choose_spec.2
    (mem_univ c)

#print axioms nearest_min

/-- A nearest-point selection moves by at most twice the ambient displacement
from any fixed point of the parametrized image.
Source: triangle inequality and `nearest_min`.
HC no distance; AV milestone no distance. -/
theorem nearest_dist_bound (y : F) (c : C) :
    dist (e (nearest e he y)) (e c) ≤ 2 * dist y (e c) := by
  calc
    dist (e (nearest e he y)) (e c) ≤
        dist (e (nearest e he y)) y + dist y (e c) := dist_triangle _ _ _
    _ = dist y (e (nearest e he y)) + dist y (e c) := by rw [dist_comm]
    _ ≤ dist y (e c) + dist y (e c) := add_le_add (nearest_min e he y c) le_rfl
    _ = 2 * dist y (e c) := (two_mul _).symm

#print axioms nearest_dist_bound

/-- Nearest base points tend to a specified base point when their ambient
arguments tend to its image, provided the parametrization is an embedding.
Source: `nearest_dist_bound` and Mathlib, `Topology.IsEmbedding.tendsto_nhds_iff`.
HC no distance; AV milestone no distance. -/
theorem nearest_tendsto (hemb : Topology.IsEmbedding e) (c : C) :
    Tendsto (nearest e he) (𝓝 (e c)) (𝓝 c) := by
  apply hemb.tendsto_nhds_iff.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (e c) (half_pos hε)] with y hy
  have hy' : dist y (e c) < ε / 2 := hy
  exact lt_of_le_of_lt (nearest_dist_bound e he y c) (by linarith)

#print axioms nearest_tendsto

/-- An injective parametrization into a metric space is fixed by the same
nearest-point selection used off the image.
Source: `nearest_min` and the separation axiom for a metric space.
HC no distance; AV milestone no distance. -/
theorem nearest_fix {G : Type*} [MetricSpace G] (u : C → G) (hu : Continuous u)
    (hinj : Injective u) (c : C) : nearest u hu (u c) = c := by
  have h := nearest_min u hu (u c) c
  have hz : dist (u c) (u (nearest u hu (u c))) = 0 :=
    le_antisymm (by simpa only [dist_self] using h) dist_nonneg
  exact hinj (eq_of_dist_eq_zero hz).symm

#print axioms nearest_fix

end CompactNearest
end HodgeLean.Foundations.TubularEuler
