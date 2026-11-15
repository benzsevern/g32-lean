import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.InverseBranch
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.FiberEnumeration
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.FiberSumEnumeration
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.MeromorphicCriticalValues
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusOperations

noncomputable section
open HodgeLean.Foundations.Program Filter Set
open scoped TensorProduct Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§17, 21, local inverse branches and fiber sums. -/
theorem meromorphicFiberSum_holomorphicAt_regular
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C) (hnc : ∃ x y, f x ≠ f y)
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) [DiscreteTopology (b2_latticeMap L F).range]
    (a : C → b2_torus L F)
    (ha : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω a)
    (y : OnePoint ℂ) (hy : y ∉ meromorphicCriticalValues (E := E) f) :
    letI := b4cov_sphChartedSpace
    letI := b4cov_sph_isManifold
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω (meromorphicFiberSum h f hnc a) y := by
  classical
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  have hfin := b4_fiber_finite_aux h (by simp : Module.finrank ℂ ℂ = 1) f f.property.1 hnc y
  let I := {x : C // f x = y}
  letI : Fintype I := hfin.fintype
  let p : I → C := Subtype.val
  have hp : ∀ i, f (p i) = y := fun i ↦ i.property
  have hpr : (f : C → OnePoint ℂ) ⁻¹' {y} = range p := by
    ext x
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨i, hix⟩ ↦ hix ▸ i.property⟩
  have hd : ∀ i, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f (p i) ≠ 0 :=
    fun i hz ↦ hy ⟨p i, hz, hp i⟩
  choose r hr0 hrhol hrr hrl using fun i ↦
    holomorphic_inverse_branch h (by simp : Module.finrank ℂ ℂ = 1) f f.property.1 (p i) (hd i)
  have hr0' : ∀ i, r i y = p i := fun i ↦ hp i ▸ hr0 i
  have hrhol' : ∀ i, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω (r i) y :=
    fun i ↦ hp i ▸ hrhol i
  have hrr' : ∀ i, ∀ᶠ z in 𝓝 y, f (r i z) = z := fun i ↦ hp i ▸ hrr i
  have henum := eventually_fiber_enumeration f f.property.1.continuous y p hpr
    Subtype.val_injective r hr0' (fun i ↦ (hrhol' i).continuousAt) hrl hrr'
  have hsum : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω
      (fun z ↦ ∑ i : I, a (r i z)) y := by
    apply torus_sum_contMDiffAt F Finset.univ (fun i z ↦ a (r i z)) y
    intro i _
    exact (ha (r i y)).comp y (hrhol' i)
  have hreg : ∀ᶠ z in 𝓝 y, z ∉ meromorphicCriticalValues (E := E) f :=
    (meromorphicCriticalValues_finite h f hnc).isClosed.isOpen_compl.mem_nhds hy
  apply hsum.congr_of_eventuallyEq
  filter_upwards [henum, hreg] with z he hz
  exact weightedFiber_sum_of_enumeration (meromorphicMultiplicity (E := E) f) f z
    (b4_fiber_finite_aux h (by simp : Module.finrank ℂ ℂ = 1) f f.property.1 hnc z)
    (fun i ↦ r i z) he.1 he.2
    (meromorphicMultiplicity_eq_one_of_not_criticalValue f z hz) a

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
