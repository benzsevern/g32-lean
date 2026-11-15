import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §4, finite fibers of proper local maps. -/
theorem eventually_fiber_enumeration
    {C Y ι : Type*} [TopologicalSpace C] [T2Space C] [CompactSpace C]
    [TopologicalSpace Y] [T2Space Y] [Fintype ι]
    (f : C → Y) (hf : Continuous f) (y : Y) (a : ι → C)
    (ha : f ⁻¹' {y} = range a) (hai : Function.Injective a)
    (r : ι → Y → C) (hr0 : ∀ i, r i y = a i)
    (hrc : ∀ i, ContinuousAt (r i) y)
    (hrl : ∀ i, ∀ᶠ x in 𝓝 (a i), r i (f x) = x)
    (hrr : ∀ i, ∀ᶠ z in 𝓝 y, f (r i z) = z) :
    ∀ᶠ z in 𝓝 y, Function.Injective (fun i ↦ r i z) ∧
      f ⁻¹' {z} = range (fun i ↦ r i z) := by
  classical
  choose U hUS hUo haU using fun i ↦ mem_nhds_iff.mp (hrl i)
  let W : Set C := ⋃ i, U i
  have hWo : IsOpen W := isOpen_iUnion hUo
  have hK : IsClosed (f '' Wᶜ) := (hWo.isClosed_compl.isCompact.image hf).isClosed
  have hy : y ∉ f '' Wᶜ := by
    rintro ⟨x, hx, hxy⟩
    have hxF : x ∈ f ⁻¹' {y} := hxy
    rw [ha] at hxF
    obtain ⟨i, rfl⟩ := hxF
    exact hx (mem_iUnion.mpr ⟨i, haU i⟩)
  have havoid : ∀ᶠ z in 𝓝 y, z ∉ f '' Wᶜ := hK.isOpen_compl.mem_nhds hy
  have hinj : ∀ᶠ z in 𝓝 y, Function.Injective (fun i ↦ r i z) := by
    have hne : ∀ i j, ∀ᶠ z in 𝓝 y, i ≠ j → r i z ≠ r j z := by
      intro i j
      by_cases hij : i = j
      · exact Eventually.of_forall (fun _ h ↦ (h hij).elim)
      · have hneq : r i y ≠ r j y := by
          rw [hr0 i, hr0 j]
          exact fun h ↦ hij (hai h)
        have hp := (hrc i).prodMk (hrc j)
        exact (hp.eventually ((isClosed_diagonal (X := C)).isOpen_compl.mem_nhds hneq)).mono (fun _ h _ ↦ h)
    filter_upwards [Filter.eventually_all.mpr (fun i ↦ Filter.eventually_all.mpr (hne i))] with z hz
    intro i j he
    by_contra h
    exact hz i j h he
  filter_upwards [havoid, hinj, Filter.eventually_all.mpr hrr] with z hz hi hr
  refine ⟨hi, ?_⟩
  ext x
  constructor
  · intro hfx
    have hxW : x ∈ W := by
      by_contra hx
      exact hz ⟨x, hx, hfx⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxW
    exact ⟨i, (congrArg (r i) hfx).symm.trans (hUS i hxi)⟩
  · rintro ⟨i, rfl⟩
    exact hr i

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
