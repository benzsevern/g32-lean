import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cChartOrientation

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory Topology Filter AlgebraicTopology.Singular
open scoped Manifold ContDiff

def b6m_surfaceCoordinateEquiv : ℂ ≃L[ℂ] (Fin 1 → ℂ) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm

variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]

def b6m_surfaceChart (x : C) : OpenPartialHomeomorph C (Fin 1 → ℂ) :=
  (chartAt ℂ x).trans b6m_surfaceCoordinateEquiv.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem b6m_surfaceChart_source (x : C) :
    (b6m_surfaceChart x).source = (chartAt ℂ x).source := by
  simp [b6m_surfaceChart, OpenPartialHomeomorph.trans_source]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surfaceChart_localClass_eq (R : Type) [CommRing R]
    [IsManifold 𝓘(ℂ, ℂ) 1 C] (z z' q : C)
    (hq : q ∈ (b6m_surfaceChart z).source)
    (hq' : q ∈ (b6m_surfaceChart z').source) :
    b6m_localClassOfChart R 1 (b6m_surfaceChart z) q hq =
      b6m_localClassOfChart R 1 (b6m_surfaceChart z') q hq' := by
  let E := b6m_surfaceCoordinateEquiv
  let T : ℂ →L[ℂ] ℂ := tangentCoordChange 𝓘(ℂ, ℂ) z z' q
  let L := E.toContinuousLinearMap.comp (T.comp E.symm.toContinuousLinearMap)
  have hoverlap : q ∈ (extChartAt 𝓘(ℂ, ℂ) z).source ∩
      (extChartAt 𝓘(ℂ, ℂ) z').source := by
    simpa only [extChartAt_source, b6m_surfaceChart_source, Set.mem_inter_iff] using And.intro hq hq'
  have hraw : HasFDerivAt (fun v => chartAt ℂ z' ((chartAt ℂ z).symm v)) T
      (chartAt ℂ z q) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℂ, ℂ)) hoverlap
    simp only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [] with v
    rfl
  have hT : Function.Injective T := by
    intro a b hab
    have h := congrArg (tangentCoordChange 𝓘(ℂ, ℂ) z' z q) hab
    have hback : q ∈ (extChartAt 𝓘(ℂ, ℂ) z).source ∩
        (extChartAt 𝓘(ℂ, ℂ) z').source ∩
        (extChartAt 𝓘(ℂ, ℂ) z).source := ⟨hoverlap, hoverlap.1⟩
    simpa only [T, tangentCoordChange_comp hback,
      tangentCoordChange_self hoverlap.1] using h
  have hL : Function.Injective L := E.injective.comp (hT.comp E.symm.injective)
  have hraw' : HasFDerivAt (fun v => chartAt ℂ z' ((chartAt ℂ z).symm v)) T
      (E.symm (E (chartAt ℂ z q))) := by simpa using hraw
  have hderiv := E.hasFDerivAt.comp (E (chartAt ℂ z q))
    (hraw'.comp (E (chartAt ℂ z q)) E.symm.hasFDerivAt)
  apply b6m_localClassOfChart_eq_of_hasFDerivAt_transition R 1
    (b6m_surfaceChart z) (b6m_surfaceChart z') q hq hq' L hL
  apply (piHasFDerivAt_iff_normed 1 _ L _).mpr
  exact hderiv

def b6m_surfaceLocalClass (R : Type) [CommRing R] (x : C) :
    RelativeHomology R (pointComplementPair x) 2 :=
  b6m_localClassOfChart R 1 (b6m_surfaceChart x) x
    (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ x)

theorem b6m_surfaceLocalClass_neighborhood (R : Type) [CommRing R]
    [IsManifold 𝓘(ℂ, ℂ) 1 C] (x : C) :
    ∃ U : TopologicalSpace.Opens C, x ∈ U ∧
      ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of C) (U : Set C)ᶜ) 2,
        ∀ (y : C) (hy : y ∈ U), relativeHomologyMap R 2
          (supportInclusionPairMap (TopCat.of C) (Set.singleton_subset_iff.mpr hy)) c =
            b6m_surfaceLocalClass R y := by
  let e := b6m_surfaceChart x
  have hx : x ∈ e.source := by
    simpa only [e, b6m_surfaceChart_source] using mem_chart_source ℂ x
  refine ⟨chartOrientationNeighborhood 1 e x hx,
    mem_chartOrientationNeighborhood 1 e x hx,
    b6m_chartOrientationNeighborhoodClass R 1 e x hx, ?_⟩
  intro y hy
  rw [b6m_chartOrientationNeighborhoodClass_restrict R 1 e x hx y hy]
  exact b6m_surfaceChart_localClass_eq R x y y
    (chartOrientationNeighborhood_subset_source 1 e x hx hy)
    (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ y)

theorem b6m_surface_globalOrientation (R : Type) [CommRing R]
    [T2Space C] [CompactSpace C] [IsManifold 𝓘(ℂ, ℂ) 1 C] :
    ∃ w : RelativeHomology R (TopPair.ofSubset
        (((⊤ : TopologicalSpace.Opens C) : Set C)ᶜ : Set (TopCat.of C))) 2,
      ∀ y : C, relativeHomologyMap R 2
        (supportInclusionPairMap (TopCat.of C)
          (Set.singleton_subset_iff.mpr (TopologicalSpace.Opens.mem_top y))) w =
            b6m_surfaceLocalClass R y :=
  b6m_global_class_exists_of_local_classes R (E := ℂ) Complex.finrank_real_complex
    (b6m_surfaceLocalClass R) (b6m_surfaceLocalClass_neighborhood R)

end HodgeLean.Foundations.Program
