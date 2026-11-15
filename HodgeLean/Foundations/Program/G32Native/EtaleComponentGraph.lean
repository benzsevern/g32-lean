import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # The specified lift as an open component of the actual etale pullback
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An isomorphic source lift into an etale ambient pullback is an actual open immersion.
Source: EGA IV, 17.9.3 and 17.11.1;
Mathlib, Etale.of_comp and IsOpenImmersion.of_flat_of_mono.
HC no distance; AV milestone no distance. -/
theorem s2e_i1_etale_component_graph_open
    {Q P W B : Scheme} (i : P ⟶ B) (β : W ⟶ B) [Etale β]
    (g : Q ⟶ P) [IsIso g] (j : Q ⟶ W) (h : g ≫ i = j ≫ β) :
    IsOpenImmersion (pullback.lift g j h) := by
  let s := pullback.lift g j h
  have hs : s ≫ pullback.fst i β = g := pullback.lift_fst _ _ _
  letI : Etale (s ≫ pullback.fst i β) := hs.symm ▸ inferInstance
  letI : Etale s := Etale.of_comp s (pullback.fst i β)
  letI : Mono s := mono_of_mono_fac hs
  exact IsOpenImmersion.of_flat_of_mono s

#print axioms s2e_i1_etale_component_graph_open

end HodgeLean.Foundations.Program.G32Native
