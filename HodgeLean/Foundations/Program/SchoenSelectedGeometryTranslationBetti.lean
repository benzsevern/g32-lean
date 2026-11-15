import HodgeLean.Adapters.DegreeOneLatticeLoops

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Translations of a path-connected topological additive group act trivially on rational cohomology. -/
theorem s0_translation_pullback
    (J : Type) [AddGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
    [PathConnectedSpace J] (c : J) (n : ℕ) :
    cohomologyMap ℚ n (TopCat.ofHom
      (⟨fun x : J ↦ x + c, continuous_id.add continuous_const⟩ : ContinuousMap J J)) =
        LinearMap.id := by
  let γ := PathConnectedSpace.somePath (0 : J) c
  let H : ContinuousMap.Homotopy (ContinuousMap.id J)
      (⟨fun x : J ↦ x + c, continuous_id.add continuous_const⟩ : ContinuousMap J J) :=
    { toFun := fun p ↦ p.2 + γ p.1
      continuous_toFun := continuous_snd.add (γ.continuous.comp continuous_fst)
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }
  have h := cohomologyMap_eq_of_homotopy (f := 𝟙 (TopCat.of J))
    (g := TopCat.ofHom ⟨fun x : J ↦ x + c, continuous_id.add continuous_const⟩) H n
  exact h.symm.trans (cohomologyMap_id ℚ (TopCat.of J) n)

#print axioms s0_translation_pullback
end HodgeLean.Foundations.Program
