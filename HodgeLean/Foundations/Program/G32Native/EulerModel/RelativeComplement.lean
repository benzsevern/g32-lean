import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
import Mathlib.Algebra.Homology.HomologySequence

/-! # Forgetting support across a homologically trivial complement -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Vanishing in adjacent subspace degrees makes the relative homology projection invertible. -/
theorem relative_projection_isIso (P : TopPair.{0}) (n : ℕ)
    (hn : IsZero (Homology ℚ P.snd n))
    (hn1 : IsZero (Homology ℚ P.snd (n + 1))) :
    IsIso (relativeHomologyProjection ℚ P (n + 1)) := by
  have hs := relativeChainShortComplex_shortExact ℚ P
  have hm : Mono (relativeHomologyProjection ℚ P (n + 1)) :=
    (hs.homology_exact₂ (n + 1)).mono_g (hn1.eq_of_src _ _)
  have he : Epi (relativeHomologyProjection ℚ P (n + 1)) :=
    (hs.homology_exact₃ (n + 1) n (by simp)).epi_f (hn.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

#print axioms relative_projection_isIso
/-- Vanishing of adjacent complement homology makes forgetting relative cohomology bijective. -/
theorem relative_to_absolute_bijective (P : TopPair.{0}) (n : ℕ)
    (hn : IsZero (Homology ℚ P.snd n))
    (hn1 : IsZero (Homology ℚ P.snd (n + 1))) :
    Function.Bijective (relativeCohomologyToAbsolute ℚ P (n + 1)) := by
  letI := relative_projection_isIso P n hn hn1
  let E := (asIso (relativeHomologyProjection ℚ P (n + 1))).toLinearEquiv
  let CE : RelativeCohomology ℚ P (n + 1) ≃ₗ[ℚ] Cohomology ℚ P.fst (n + 1) :=
    (relativeCohomologyEquivDualHomology ℚ P (n + 1)).trans
      (E.dualMap.trans (cohomologyEquivDualHomology ℚ P.fst (n + 1)).symm)
  have he : relativeCohomologyToAbsolute ℚ P (n + 1) = CE.toLinearMap := by
    ext c
    apply (cohomologyEquivDualHomology ℚ P.fst (n + 1)).injective
    have hCE : cohomologyEquivDualHomology ℚ P.fst (n + 1) (CE c) =
        E.dualMap (relativeCohomologyEquivDualHomology ℚ P (n + 1) c) := by
      simp only [CE, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.coe_coe]
    rw [hCE]
    ext z
    exact cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ P (n + 1) c z
  rw [he]
  exact CE.bijective

#print axioms relative_to_absolute_bijective
end HodgeLean.Foundations.Program.G32Native.EulerModel
