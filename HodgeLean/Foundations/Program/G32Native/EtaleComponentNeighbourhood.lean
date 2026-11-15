import HodgeLean.Foundations.Program.G32Native.EtaleComponentGraph
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # An actual ambient neighbourhood making the specified etale component cartesian
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified lifted component is the entire pullback after an actual ambient open restriction.
Source: EGA IV, 17.9.3 and 17.11.1; Hartshorne, Algebraic Geometry, II.4 and II.8,
open components of an etale base change of a closed immersion.
HC no distance; AV milestone no distance. -/
theorem s2e_i1_etale_component_cartesian_neighbourhood
    {Q P W B : Scheme} (i : P ⟶ B) [IsClosedImmersion i]
    (β : W ⟶ B) [Etale β] (g : Q ⟶ P) [IsIso g]
    (j : Q ⟶ W) [IsClosedImmersion j] (h : g ≫ i = j ≫ β) :
    ∃ (U : W.Opens) (j' : Q ⟶ U.toScheme),
      IsClosedImmersion j' ∧ j' ≫ U.ι = j ∧ IsPullback g j' i (U.ι ≫ β) := by
  let s := pullback.lift g j h
  let π := pullback.snd i β
  letI : IsOpenImmersion s := s2e_i1_etale_component_graph_open i β g j h
  obtain ⟨u, hu, heq⟩ := π.isClosedEmbedding.isInducing.isOpen_iff.mp
    s.isOpenMap.isOpen_range
  let U : W.Opens := ⟨u, hu⟩
  have hr : Set.range j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : s x ∈ Set.range s := ⟨x, rfl⟩
    rw [← heq] at hx
    change π (s x) ∈ u at hx
    have hs : π (s x) = j x := congrArg (fun f : Q ⟶ W => f x)
      (pullback.lift_snd g j h)
    exact hs ▸ hx
  let j' := IsOpenImmersion.lift U.ι j hr
  have hj : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : IsClosedImmersion (j' ≫ U.ι) := hj.symm ▸ inferInstance
  letI := hcomp
  refine ⟨U, j', IsClosedImmersion.of_comp j' U.ι, hj, ?_⟩
  have hopen : π ⁻¹ᵁ U.ι.opensRange = s.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    apply TopologicalSpace.Opens.ext
    exact heq
  have hsq : IsPullback j' s U.ι π :=
    IsOpenImmersion.isPullback j' s U.ι π
      ((pullback.lift_snd g j h).trans hj.symm) hopen
  simpa only [s, pullback.lift_fst] using
    hsq.flip.paste_horiz (IsPullback.of_hasPullback i β)

#print axioms s2e_i1_etale_component_cartesian_neighbourhood

end HodgeLean.Foundations.Program.G32Native
