import HodgeLean.Foundations.Program.CompensationAssemblyFibreTrace
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem cq_relative_absolute_restriction_zero (X : TopPair.{0}) (n : ℕ)
    (c : RelativeCohomology ℚ X n) :
    cohomologyMap ℚ n X.map (relativeCohomologyToAbsolute ℚ X n c) = 0 := by
  let S := relativeDualCochainShortComplexNat ℚ X
  change (HomologicalComplex.homologyMap S.f n ≫
    HomologicalComplex.homologyMap S.g n).hom c = 0
  rw [← HomologicalComplex.homologyMap_comp, S.zero,
    HomologicalComplex.homologyMap_zero]
  rfl

theorem cq_relative_cochain_shortExact (X : TopPair.{0}) :
    (relativeDualCochainShortComplexNat ℚ X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => (relativeDualCochainShortComplexNatDegreewiseSplitting ℚ X n).shortExact

theorem cq_relative_restriction_injective_of_isZero (X : TopPair.{0}) (n : ℕ)
    (hZ : IsZero (RelativeCohomology ℚ X n)) :
    Function.Injective (cohomologyMap ℚ n X.map) := by
  have hS := cq_relative_cochain_shortExact X
  have hmono : Mono (HomologicalComplex.homologyMap
      (relativeDualCochainShortComplexNat ℚ X).g n) :=
    (hS.homology_exact₂ n).mono_g (hZ.eq_zero_of_src _)
  exact (ModuleCat.mono_iff_injective _).mp hmono

end HodgeLean.Foundations.Program
