import HodgeLean.Foundations.TubularEuler.LinearFrameZeroHelpers
import Mathlib.Topology.ContinuousMap.Basic

/-! # Domains for coordinates of an ambient map

Coordinate domains retain both the original map domain and the ambient chart source.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace Bundle
namespace HodgeLean.Foundations.TubularEuler

theorem raw_map_coordinate_domain
    {N E Y F : Type*} [TopologicalSpace N] [TopologicalSpace E]
    [TopologicalSpace Y] [TopologicalSpace F]
    (P : OpenPartialHomeomorph N E) (a : OpenPartialHomeomorph Y F)
    (U : Opens N) (f : N → Y) (hf : ContinuousOn f U)
    (z : N) (hzP : z ∈ P.source) (hzU : z ∈ U) (hza : f z ∈ a.source) :
    ∃ D : Opens E, P z ∈ D ∧ (D : Set E) ⊆ P.target ∧
      Set.MapsTo P.symm D U ∧ Set.MapsTo (f ∘ P.symm) D a.source := by
  let S : Set E := P.target ∩ P.symm ⁻¹' (U : Set N)
  have hS : IsOpen S := P.isOpen_inter_preimage_symm U.isOpen
  have hcont : ContinuousOn (f ∘ P.symm) S :=
    hf.comp (P.symm.continuousOn.mono (fun _ h => h.1)) (fun _ h => h.2)
  let D : Opens E := ⟨S ∩ (f ∘ P.symm) ⁻¹' a.source,
    hcont.isOpen_inter_preimage hS a.open_source⟩
  refine ⟨D, ?_, (fun _ h => h.1.1), (fun _ h => h.1.2), (fun _ h => h.2)⟩
  change (P z ∈ P.target ∧ P.symm (P z) ∈ U) ∧ f (P.symm (P z)) ∈ a.source
  rw [P.left_inv hzP]
  exact ⟨⟨P.map_source hzP, hzU⟩, hza⟩

theorem raw_normal_coordinates_fix_zero
    {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    (k : ℕ) (E : B → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E)) [e.IsLinear ℂ]
    (b : OpenPartialHomeomorph B (Fin k → ℂ))
    (a : OpenPartialHomeomorph X ((Fin k → ℂ) × (Fin k → ℂ)))
    (i : B → X) (f : TotalSpace (Fin k → ℂ) E → X)
    (hzero : ∀ y, f (zeroSection (Fin k → ℂ) E y) = i y)
    (hmatch : ∀ y ∈ b.source, a (i y) = (b y, (0 : Fin k → ℂ)))
    (q : Fin k → ℂ)
    (hq : (q, (0 : Fin k → ℂ)) ∈
      (e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).target) :
    a (f ((e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm (q, 0))) = (q, 0) := by
  let P := e.toOpenPartialHomeomorph.trans
    (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  let z := P.symm (q, (0 : Fin k → ℂ))
  have hz : z ∈ P.source := P.map_target hq
  have hP : P z = (q, (0 : Fin k → ℂ)) := P.right_inv hq
  have hbase : z.proj ∈ e.baseSet := e.mem_source.mp hz.1
  have hb : z.proj ∈ b.source := by
    have h : (e z).1 ∈ b.source := hz.2.1
    rwa [e.coe_fst' hbase] at h
  have hfibre : z.2 = 0 := by
    apply (linearFrame_zero_iff k E e z hz.1).mp
    exact congrArg Prod.snd hP
  have hz0 : z = zeroSection (Fin k → ℂ) E z.proj :=
    congrArg (TotalSpace.mk z.proj) hfibre
  have hfirst : b z.proj = q := by
    have h := congrArg Prod.fst hP
    change b (e z).1 = q at h
    rwa [e.coe_fst' hbase] at h
  change a (f z) = (q, 0)
  rw [hz0, hzero, hmatch z.proj hb, hfirst]

#print axioms raw_normal_coordinates_fix_zero

#print axioms raw_map_coordinate_domain

end HodgeLean.Foundations.TubularEuler
