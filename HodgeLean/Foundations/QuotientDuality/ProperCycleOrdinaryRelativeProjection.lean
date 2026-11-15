import HodgeLean.Foundations.QuotientDuality.ProperCycleHomotopyRetractionVanishing
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.Euclidean

/-! # Actual ordinary to relative homology maps across small boundaries -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing of the actual subspace homology in two adjacent degrees makes the original ordinary to relative homology projection bijective.
Source: relativeChainShortComplex_shortExact; relativeSingular_homology_exact_relative.
HC no distance; AV milestone no distance. -/
theorem properCycle_ordinary_relative_projection_bijective (P : TopPair.{0}) (n : ℕ)
    (hn : Subsingleton (Homology ℚ P.snd (n+1)))
    (hp : Subsingleton (Homology ℚ P.snd n)) :
    Function.Bijective (relativeHomologyProjection ℚ P (n+1)).hom := by
  have hzn : IsZero (Homology ℚ P.snd (n+1)) := ModuleCat.isZero_iff_subsingleton.mpr hn
  have hzp : IsZero (Homology ℚ P.snd n) := ModuleCat.isZero_iff_subsingleton.mpr hp
  letI : Mono (relativeHomologyProjection ℚ P (n+1)) :=
    ((relativeChainShortComplex_shortExact ℚ P).homology_exact₂ (n+1)).mono_g
      (hzn.eq_zero_of_src _)
  letI : Epi (relativeHomologyProjection ℚ P (n+1)) :=
    (relativeSingular_homology_exact_relative P n).epi_f (hzp.eq_zero_of_tgt _)
  letI := isIso_of_mono_of_epi (relativeHomologyProjection ℚ P (n+1))
  exact ConcreteCategory.bijective_of_isIso _

end HodgeLean.Foundations.QuotientDuality
