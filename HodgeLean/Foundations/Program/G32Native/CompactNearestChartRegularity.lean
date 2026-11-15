import HodgeLean.Foundations.Program.G32Native.NearestPointChartMinimum
import HodgeLean.Foundations.Program.G32Native.NearestPointSelectionRegularity

/-! # Analytic chart expressions of the common compact nearest-point map

The map is selected once on the compact carrier. Every chart expression below
is obtained from that same map by composition.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function Filter Set Topology
namespace HodgeLean.Foundations.TubularEuler

/-- Near an interior point of an analytically immersed compact carrier, the
single compact nearest-point selection has an analytic expression in any
Hilbert coordinate chart.
Source: `CompactNearest.nearest_tendsto`, `nearestPoint_chart_localMin`,
and `nearestPoint_selection_analytic`; Lee, Introduction to Smooth
Manifolds, second edition, Euclidean normal-neighbourhood construction.
HC no distance; AV milestone no distance. -/
theorem compactNearest_chart_analytic
    {M B F : Type*} [TopologicalSpace M]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (C : Set M) [CompactSpace C] [Nonempty C]
    (e : M → F) (he : Continuous e)
    (hemb : Topology.IsEmbedding (fun z : C => e z))
    (a : OpenPartialHomeomorph M B) (c : C)
    (hc : (c : M) ∈ a.source) (hcC : (c : M) ∈ interior C)
    (hσ : ContDiffAt ℝ ⊤ (fun b => e (a.symm b)) (a c))
    (hinj : Injective (fderiv ℝ (fun b => e (a.symm b)) (a c))) :
    ContDiffAt ℝ ⊤
      (fun y => a ((CompactNearest.nearest (fun z : C => e z)
        (he.comp continuous_subtype_val) y : C) : M)) (e c) := by
  let u : C → F := fun z => e z
  let hu : Continuous u := he.comp continuous_subtype_val
  let r : F → C := CompactNearest.nearest u hu
  let p : F → B := fun y => a (r y)
  let σ : B → F := fun b => e (a.symm b)
  have hσ0 : σ (a c) = e c := congrArg e (a.left_inv hc)
  have hr : Tendsto (fun y => ((r y : C) : M)) (𝓝 (e c)) (𝓝 (c : M)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (CompactNearest.nearest_tendsto u hu hemb c)
  have hp : Tendsto p (𝓝 (e c)) (𝓝 (a c)) :=
    (a.continuousAt hc).tendsto.comp hr
  have hm : ∀ᶠ y in 𝓝 (e c),
      IsLocalMin (fun b => ‖σ b - y‖ ^ 2) (p y) := by
    have hs := hr.eventually (a.open_source.mem_nhds hc)
    have hC := hr.eventually (isOpen_interior.mem_nhds hcC)
    filter_upwards [hs, hC] with y hy hyC
    exact nearestPoint_chart_localMin C e a (r y) hy hyC y
      (CompactNearest.nearest_min u hu y)
  change ContDiffAt ℝ ⊤ p (e c)
  rw [← hσ0]
  apply nearestPoint_selection_analytic σ (a c) p hσ hinj
  · simpa only [hσ0] using hp
  · simpa only [hσ0] using hm

#print axioms compactNearest_chart_analytic

end HodgeLean.Foundations.TubularEuler
