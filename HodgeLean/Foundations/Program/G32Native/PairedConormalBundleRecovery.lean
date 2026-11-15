import HodgeLean.Foundations.Program.G32Native.PairedConormalContinuousRecovery
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Recovery of bundle continuity from actual fibre observations -/

noncomputable section
set_option maxHeartbeats 200000
open Bundle Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- An injective continuous family of linear observations detects the topology
of a finite-dimensional vector bundle, including maps whose continuity is not given. -/
theorem paired_bundle_continuous_of_observations
    {𝕜 B X P F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [TopologicalSpace B] [TopologicalSpace X]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (E : B → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
    [FiberBundle P E] [VectorBundle 𝕜 P E]
    (J : ∀ b, E b →ₗ[𝕜] F)
    (hJ : Continuous (fun z : TotalSpace P E => J z.proj z.2))
    (hinj : ∀ b, Function.Injective (J b))
    (f : X → TotalSpace P E)
    (hbase : Continuous (fun x => (f x).proj))
    (hobs : Continuous (fun x => J (f x).proj (f x).2)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let e := trivializationAt P E (f x₀).proj
  let U : Set B := e.baseSet
  let A : U → P →L[𝕜] F := fun b => LinearMap.toContinuousLinearMap
    ((J b.1).comp (e.symmₗ 𝕜 b.1))
  have hA : Continuous A := by
    apply continuous_clm_apply.mpr
    intro v
    have ht : Continuous (fun b : U =>
        (⟨b.1, e.symm b.1 v⟩ : TotalSpace P E)) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun b => ⟨b.2, Set.mem_univ _⟩)
    apply (hJ.comp ht).congr
    intro b
    change J b.1 (e.symm b.1 v) = J b.1 (e.symmₗ 𝕜 b.1 v)
    rw [e.symmₗ_apply (R := 𝕜) b.2]
  have hAi (b : U) : Function.Injective (A b) := by
    intro v w h
    apply (e.linearEquivAt 𝕜 b.1 b.2).symm.injective
    change e.symm b.1 v = e.symm b.1 w
    have h' : e.symmₗ 𝕜 b.1 v = e.symmₗ 𝕜 b.1 w := hinj b.1 h
    simpa only [e.symmₗ_apply (R := 𝕜) b.2] using h'
  let V : Set X := {x | (f x).proj ∈ U}
  have hV : IsOpen V := e.open_baseSet.preimage hbase
  have hmem : x₀ ∈ V := mem_baseSet_trivializationAt P E (f x₀).proj
  let b : V → U := fun x => ⟨(f x.1).proj, x.2⟩
  let v : V → P := fun x => (e (f x.1)).2
  have hb : Continuous b := (hbase.comp continuous_subtype_val).subtype_mk _
  have hvobs : Continuous (fun x : V => A (b x) (v x)) := by
    apply (hobs.comp continuous_subtype_val).congr
    intro x
    change J (f x.1).proj (f x.1).2 =
      J (f x.1).proj (e.symmₗ 𝕜 (f x.1).proj (e (f x.1)).2)
    rw [e.symmₗ_apply (R := 𝕜) x.2, e.symm_proj_apply (f x.1) x.2]
  have hv : Continuous v := paired_linear_family_continuous_recovery A hA hAi b hb v hvobs
  have hvV : ContinuousOn (fun x => (e (f x)).2) V :=
    continuousOn_iff_continuous_domRestrict.mpr hv
  exact (FiberBundle.continuousAt_totalSpace P f).mpr
    ⟨hbase.continuousAt, hvV.continuousAt (hV.mem_nhds hmem)⟩

#print axioms paired_bundle_continuous_of_observations
end HodgeLean.Foundations.Program.G32Native
