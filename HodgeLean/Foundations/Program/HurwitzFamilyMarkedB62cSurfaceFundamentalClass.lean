import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGlobalGenerator
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceOrientation
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cChartGenerator

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory Topology AlgebraicTopology.Singular
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surface_absoluteOrientation (R : Type) [CommRing R]
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [T2Space C] [CompactSpace C] [IsManifold 𝓘(ℂ, ℂ) 1 C] :
    ∃ w : Homology R (TopCat.of C) 2, ∀ x : C,
      (relativeHomologyProjection R (pointComplementPair x) 2).hom w =
        b6m_surfaceLocalClass R x := by
  let P := TopPair.ofSubset (X := TopCat.of C)
    (((⊤ : TopologicalSpace.Opens C) : Set C)ᶜ)
  haveI : IsEmpty P.snd := by
    change IsEmpty ↥(((⊤ : TopologicalSpace.Opens C) : Set C)ᶜ)
    rw [TopologicalSpace.Opens.coe_top, Set.compl_univ]
    infer_instance
  obtain ⟨w, hw⟩ := b6m_surface_globalOrientation R (C := C)
  obtain ⟨a, ha⟩ := (b6m_relativeHomologyProjection_bijective_of_isEmpty R P 2).2 w
  refine ⟨a, fun x => ?_⟩
  have h := b6m_relativeHomologyProjection_support R (TopCat.of C)
    (Set.singleton_subset_iff.mpr (TopologicalSpace.Opens.mem_top x)) 2 a
  rw [ha] at h
  exact h.symm.trans (hw x)

theorem b6m_surfaceLocalClass_smul_bijective (R : Type) [CommRing R]
    {C : Type} [TopologicalSpace C] [T1Space C] [ChartedSpace ℂ C] (x : C) :
    Function.Bijective (fun r : R => r • b6m_surfaceLocalClass R x) :=
  b6m_localClassOfChart_one_smul_bijective R (b6m_surfaceChart x) x
    (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ x)

theorem b6m_surface_fundamental_generator (R : Type) [CommRing R]
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [IsManifold 𝓘(ℂ, ℂ) 1 C] :
    ∃ w : Homology R (TopCat.of C) 2,
      (∀ x : C, (relativeHomologyProjection R (pointComplementPair x) 2).hom w =
        b6m_surfaceLocalClass R x) ∧ Function.Bijective (fun r : R => r • w) := by
  obtain ⟨w, hw⟩ := b6m_surface_absoluteOrientation R (C := C)
  refine ⟨w, hw, b6m_absolute_topHomology_generated_by_point_generators R
    (E := ℂ) Complex.finrank_real_complex w ?_⟩
  intro x
  rw [hw x]
  exact b6m_surfaceLocalClass_smul_bijective R x

end HodgeLean.Foundations.Program
