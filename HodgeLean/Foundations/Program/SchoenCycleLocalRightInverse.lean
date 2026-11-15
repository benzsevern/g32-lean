import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Continuous

/-! # Neighbourhood images from a local right inverse -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A right inverse germ tending to the specified preimage gives the full image neighbourhood filter.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Bourbaki, General Topology, Chapter I, neighbourhood filters. -/
theorem s2e_map_nhds_eq_of_local_right_inverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Y → X) (x : X) (y : Y)
    (hf : ContinuousAt f x) (hxy : f x = y)
    (hs : Tendsto s (𝓝 y) (𝓝 x)) (he : f ∘ s =ᶠ[𝓝 y] id) :
    Filter.map f (𝓝 x) = 𝓝 y := by
  apply le_antisymm
  · simpa only [Tendsto, hxy] using hf.tendsto
  · calc
      𝓝 y = Filter.map id (𝓝 y) := Filter.map_id.symm
      _ = Filter.map (f ∘ s) (𝓝 y) := Filter.map_congr he.symm
      _ = Filter.map f (Filter.map s (𝓝 y)) := Filter.map_map.symm
      _ ≤ Filter.map f (𝓝 x) := Filter.map_mono hs

/-- An exact right inverse in a target chart gives the full neighbourhood image of the original map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Bourbaki, General Topology, Chapter I, neighbourhood filters. -/
theorem s2e_map_nhds_eq_of_chart_right_inverse
    {T M V : Type*} [TopologicalSpace T] [TopologicalSpace M] [TopologicalSpace V]
    (Q : T → M) (R : V → T) (t : T) (y : M) (v : V)
    (e : OpenPartialHomeomorph M V) (hy : y ∈ e.source) (hey : e y = v)
    (hQ0 : Q t = y) (hQ : Tendsto Q (𝓝 t) (𝓝 y)) (hR : Tendsto R (𝓝 v) (𝓝 t))
    (he : e ∘ Q ∘ R =ᶠ[𝓝 v] id) : Filter.map Q (𝓝 t) = 𝓝 y := by
  have heT : Tendsto e (𝓝 y) (𝓝 v) := by
    simpa only [hey] using (e.continuousAt hy).tendsto
  have hQRsource : ∀ᶠ a in 𝓝 v, Q (R a) ∈ e.source :=
    (hQ.comp hR) (e.open_source.mem_nhds hy)
  have hc : ContinuousAt Q t := by
    change Tendsto Q (𝓝 t) (𝓝 (Q t))
    rwa [hQ0]
  apply s2e_map_nhds_eq_of_local_right_inverse Q (R ∘ e) t y hc hQ0 (hR.comp heT)
  filter_upwards [heT.eventually he, heT.eventually hQRsource, e.open_source.mem_nhds hy]
    with a ha hQa hEa
  apply e.injOn hQa hEa
  simpa only [Function.comp_apply, id_eq] using ha

end HodgeLean.Foundations.Program
