import HodgeLean.Foundations.BundleThom.Defs

/-! # The zero section has closed support

Closedness follows locally from complex linear coordinates, without a
separation assumption on the base.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]

/-- The fibrewise zero locus is closed in the actual bundle total space.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local triviality. -/
theorem i1_zeroSupport_isClosed : IsClosed (i1_zeroSupport k E) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro v hv
  let e := trivializationAt (Fin k → ℂ) E v.proj
  have hve : v ∈ e.source := e.mem_source.mpr (FiberBundle.mem_baseSet_trivializationAt _ _ _)
  have hn : (e v).2 ≠ 0 := by
    intro h
    apply hv
    exact (e.continuousLinearEquivAt ℂ v.proj (e.mem_source.mp hve)).injective
      (h.trans (map_zero _).symm)
  have hopen : IsOpen (e.source ∩ (fun w => (e w).2) ⁻¹' ({0}ᶜ : Set (Fin k → ℂ))) :=
    e.continuousOn.snd.isOpen_inter_preimage e.open_source isClosed_singleton.isOpen_compl
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨hve, hn⟩)
  intro w hw hz
  have hzero : (e w).2 = 0 := by
    change e.continuousLinearEquivAt ℂ w.proj (e.mem_source.mp hw.1) w.2 = 0
    change w.2 = 0 at hz
    rw [hz, map_zero]
  exact hw.2 hzero

example : IsClosed (i1_zeroSupport 1 (Bundle.Trivial ℂ (Fin 1 → ℂ))) :=
  i1_zeroSupport_isClosed 1 _

example : (⟨(2 : ℂ), fun _ : Fin 1 => (3 : ℂ)⟩ :
    TotalSpace (Fin 1 → ℂ) (Bundle.Trivial ℂ (Fin 1 → ℂ))) ∉
      i1_zeroSupport 1 (Bundle.Trivial ℂ (Fin 1 → ℂ)) := by
  intro h
  have he := congrFun h 0
  norm_num at he

end HodgeLean.Foundations.BundleThom
