import HodgeLean.RealDefs.ComplexFundamentalClass
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Rational homology equivalences induce rational cohomology equivalences. -/
theorem s2e_relativeCohomologyMap_bijective_of_homology
    {X Y : TopPair.{0}} (f : X ⟶ Y) (n : ℕ)
    (hf : Function.Bijective (relativeHomologyMap ℚ n f)) :
    Function.Bijective (relativeCohomologyMap ℚ n f) := by
  let e := LinearEquiv.ofBijective (relativeHomologyMap ℚ n f) hf
  let eX := relativeCohomologyEquivDualHomology ℚ X n
  let eY := relativeCohomologyEquivDualHomology ℚ Y n
  constructor
  · intro a b h
    apply eY.injective
    ext z
    obtain ⟨w, rfl⟩ := hf.2 z
    simpa only [eY, ← relativeCohomologyEquivDualHomology_relativeCohomologyMap] using
      congrArg (fun c => eX c w) h
  · intro a
    refine ⟨eY.symm ((eX a).comp e.symm.toLinearMap), ?_⟩
    apply eX.injective
    ext z
    simp only [eX, relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      eY, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    change eX a (e.symm (e z)) = eX a z
    rw [e.symm_apply_apply]

/-- A rational supported class extends uniquely from any open neighbourhood
of its entire support. -/
theorem s2e_supportedCohomology_excision
    {M : Type} [TopologicalSpace M] {U A : Set M}
    (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap ℚ n
      (TopPair.ofSubsetHom (A := {u : U | u.1 ∉ A}) (B := Aᶜ)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of M)
        (fun _ ha => ha))) :=
  s2e_relativeCohomologyMap_bijective_of_homology _ n
    (HodgeLean.RealDefs.j5c_excision hU hA hAU n)

end HodgeLean.Foundations.Program
