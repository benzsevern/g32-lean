import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.AbelLocalCurves
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.LocalCurveGeneration
import Mathlib.Topology.Connected.Clopen

noncomputable section
open HodgeLean.Foundations.Program Filter
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

theorem abelSum_surjective (h : Module.finrank ℂ E = 1) (p : C) :
    Function.Surjective (weightedSum (analyticAbel (E := E) (C := C) h p)) := by
  classical
  let a := analyticAbel (E := E) (C := C) h p
  let cov := b3Rest2_covHom (E := E) (C := C)
  let S := (weightedSum a).range
  obtain ⟨n, b, w, hw⟩ := finite_abelDifferential_basis (E := E) (C := C) h p
  have hex (i : Fin n) := abel_local_curve (E := E) (C := C) h p (w i).1 (w i).2
  choose g hg0 hgd hmem using hex
  have hstrict (i : Fin n) : HasStrictDerivAt (g i) (b i) 0 :=
    (hgd i).congr_deriv (hw i).symm
  have hcov := b3Rest2_covHom_spec (E := E) (C := C)
  have hopen : IsOpen (S : Set (b3_Jacobian E C)) :=
    open_subgroup_of_local_curves b cov hcov.1.isOpenMap g hstrict hg0 S hmem
  letI : ConnectedSpace (b3_Jacobian E C) :=
    hcov.2.connectedSpace hcov.1.continuous
  let U : OpenAddSubgroup (b3_Jacobian E C) := ⟨S, hopen⟩
  have hset : (S : Set (b3_Jacobian E C)) = Set.univ :=
    U.isClopen.eq_univ ⟨0, S.zero_mem⟩
  intro t
  have ht : t ∈ (S : Set (b3_Jacobian E C)) := by rw [hset]; exact Set.mem_univ t
  exact ht

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
