import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! Relative comparison over an arbitrary coefficient field. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_relative_cohomology_bijective_of_homology
    (K : Type) [Field K] {X Y : TopPair.{0}} (f : X ⟶ Y) (n : ℕ)
    (hf : Function.Bijective (relativeHomologyMap K n f)) :
    Function.Bijective (relativeCohomologyMap K n f) := by
  let e := LinearEquiv.ofBijective (relativeHomologyMap K n f) hf
  let eX := relativeCohomologyEquivDualHomology K X n
  let eY := relativeCohomologyEquivDualHomology K Y n
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

end HodgeLean.Foundations.QuotientDuality
