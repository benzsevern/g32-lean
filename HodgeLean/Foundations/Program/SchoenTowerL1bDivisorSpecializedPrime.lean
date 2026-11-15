import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSpecializationLocalization
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorLocalizationPrime

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A stalk prime remains a prime parameter at its associated scheme point. -/
theorem s2v_l1b_divisor_specialized_prime
    (X : Scheme.{0}) [IsIntegral X] (x : X)
    (p : X.presheaf.stalk x) (hp : Prime p)
    (z : Spec (X.presheaf.stalk x)) (hz : z.asIdeal = Ideal.span {p})
    (h : (X.fromSpecStalk x) z ⤳ x) :
    Prime ((X.presheaf.stalkSpecializes h).hom p) := by
  let R := X.presheaf.stalk x
  let L := Localization.AtPrime z.asIdeal
  have hsub : z.asIdeal.primeCompl ≤ nonZeroDivisors R := by
    intro a ha
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro he
    exact ha (he ▸ z.asIdeal.zero_mem)
  have hinj : Function.Injective (algebraMap R L) := IsLocalization.injective L hsub
  have hnunit : ¬ IsUnit (algebraMap R L p) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff L z.asIdeal]
    change ¬ p ∉ z.asIdeal
    rw [hz]
    exact not_not.mpr (Ideal.subset_span (Set.mem_singleton p))
  have hpl : Prime (algebraMap R L p) :=
    (s2v_l1b_divisor_localization_prime_or_unit z.asIdeal.primeCompl hinj p hp).resolve_left hnunit
  let e : L ≃+* (Spec R).presheaf.stalk z := (StructureSheaf.stalkIso R z).toRingEquiv
  have hps : Prime ((StructureSheaf.toStalk R z).hom p) := by
    have H := (MulEquiv.prime_iff e.toMulEquiv).mpr hpl
    change Prime ((StructureSheaf.stalkIso R z) (algebraMap R L p)) at H
    have he := (StructureSheaf.stalkIso R z).commutes p
    change _ = (StructureSheaf.toStalk R z).hom p at he
    exact he ▸ H
  letI := s2v_l1b_divisor_stalk_spectrum_stalkMap_isIso X x z
  let F := (asIso ((X.fromSpecStalk x).stalkMap z)).commRingCatIsoToRingEquiv
  apply (MulEquiv.prime_iff F.toMulEquiv).mp
  have H := congrArg (fun k : R ⟶ (Spec R).presheaf.stalk z => k.hom p)
    (s2v_l1b_divisor_specialization_localization X x z h)
  change Prime (((X.fromSpecStalk x).stalkMap z).hom
    ((X.presheaf.stalkSpecializes h).hom p))
  change (StructureSheaf.toStalk R z).hom p =
    ((X.fromSpecStalk x).stalkMap z).hom ((X.presheaf.stalkSpecializes h).hom p) at H
  rw [← H]
  exact hps

end HodgeLean.Foundations.Program
