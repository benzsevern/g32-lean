import HodgeLean.Adapters.NormalConeB4aGysinTransverseDisk
import Mathlib.Topology.DiscreteSubset

/-! # Finiteness of compact transverse intersections -/

noncomputable section
namespace HodgeLean.Adapters

/-- A compact intersection with a support is finite when every intersection point
has an invertible derivative in local normal coordinates. -/
theorem a3b4a_gysin_compact_transverse_intersection_finite
    {M : Type} [TopologicalSpace M] (c : ℕ)
    (S : Set M) (hS : IsClosed S)
    (U : Set (Fin c → ℂ)) (hU : IsOpen U)
    (f : (Fin c → ℂ) → M) (hf : ContinuousOn f U)
    (K : Set (Fin c → ℂ)) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrans : ∀ x ∈ K, f x ∈ S → ∃ (r : ℕ)
      (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ))),
      f x ∈ e.source ∧ (∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) ∧
      ∃ A : Matrix (Fin c) (Fin c) ℂ, A.det ≠ 0 ∧
        HasFDerivAt (fun z => (e (f (z + x))).2)
          (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0) :
    {x | x ∈ K ∧ f x ∈ S}.Finite := by
  have hcompact : IsCompact {x | x ∈ K ∧ f x ∈ S} :=
    hK.of_isClosed_subset ((hf.mono hKU).preimage_isClosed_of_isClosed hK.isClosed hS)
      Set.inter_subset_left
  apply hcompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨r, e, he, heS, A, hA, hd⟩ := htrans x hx.1 hx.2
  let T := {z : Fin c → ℂ | z + x ∈ U}
  have hT : IsOpen T := hU.preimage (continuous_id.add continuous_const)
  have h0T : (0 : Fin c → ℂ) ∈ T := by simpa [T] using hKU hx.1
  have hfT : ContinuousOn (fun z => f (z + x)) T :=
    hf.comp (continuous_id.add continuous_const).continuousOn (fun _ hz => hz)
  obtain ⟨V, _, hV, h0V, hVS, _⟩ := a3b4a_gysin_transverse_disk_normalClass
    e S heS (f x) he hx.2 T hT h0T (fun z => f (z + x)) hfT
    (by rw [zero_add]) A hA hd
  refine ⟨{y | y - x ∈ V}, hV.preimage (continuous_id.sub continuous_const), ?_⟩
  ext y
  constructor
  · intro hy
    have heq := hVS ⟨y - x, hy.1⟩ (by simpa only [sub_add_cancel] using hy.2.2)
    exact sub_eq_zero.mp heq
  · intro hy
    have hyx : y = x := hy
    subst y
    exact ⟨by simpa only [Set.mem_setOf_eq, sub_self] using h0V, hx⟩

/-- Compact trapping and pointwise transversality construct a finite support
for the intersection on the whole coordinate domain. -/
theorem a3b4a_gysin_trapped_transverse_intersection_finset
    {M : Type} [TopologicalSpace M] (c : ℕ)
    (S : Set M) (hS : IsClosed S)
    (U : Set (Fin c → ℂ)) (hU : IsOpen U)
    (f : (Fin c → ℂ) → M) (hf : ContinuousOn f U)
    (K : Set (Fin c → ℂ)) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrans : ∀ x ∈ K, f x ∈ S → ∃ (r : ℕ)
      (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ))),
      f x ∈ e.source ∧ (∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) ∧
      ∃ A : Matrix (Fin c) (Fin c) ℂ, A.det ≠ 0 ∧
        HasFDerivAt (fun z => (e (f (z + x))).2)
          (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (htrap : ∀ x ∈ U, f x ∈ S → x ∈ K) :
    ∃ T : Finset (Fin c → ℂ), (T : Set (Fin c → ℂ)) ⊆ K ∧
      ∀ x ∈ U, f x ∈ S ↔ x ∈ T := by
  classical
  have hfinite := a3b4a_gysin_compact_transverse_intersection_finite
    c S hS U hU f hf K hK hKU htrans
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro x hx
    exact (hfinite.mem_toFinset.mp hx).1
  · intro x hx
    rw [hfinite.mem_toFinset]
    exact ⟨fun hs => ⟨htrap x hx hs, hs⟩, fun hs => hs.2⟩

end HodgeLean.Adapters
