import HodgeLean.Foundations.Program.SchoenTowerAdicMapEquiv
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Localizing at a maximal ideal gives a bijective map on the corresponding adic rings. -/
theorem s2t_atPrimeAdicMap_bijective {A S : Type*} [CommRing A] [CommRing S]
    (p : Ideal A) [p.IsMaximal] [Algebra A S] [IsLocalization.AtPrime S p] [IsLocalRing S] :
    Function.Bijective (s2t_adicMap p (p.map (algebraMap A S))
      (algebraMap A S) Ideal.le_comap_map) := by
  apply s2t_adicMap_bijective_of_residues
  intro n
  have hmap := IsLocalization.AtPrime.map_eq_maximalIdeal p S
  let e : (A ⧸ p ^ n) ≃+* (S ⧸ (p.map (algebraMap A S)) ^ n) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).toRingEquiv.trans
      (Ideal.quotEquivOfEq (congrArg (fun J : Ideal S => J ^ n) hmap).symm)
  have heq : Ideal.quotientMap ((p.map (algebraMap A S)) ^ n) (algebraMap A S)
      (s2t_adicMap_pow p _ _ Ideal.le_comap_map n) = e.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [heq]
  exact e.bijective

/-- The adic ring at a maximal ideal identifies with the adic ring of its point-local ring. -/
def s2t_atPrimeAdicEquiv {A S : Type*} [CommRing A] [CommRing S]
    (p : Ideal A) [p.IsMaximal] [Algebra A S] [IsLocalization.AtPrime S p] [IsLocalRing S] :
    AdicCompletion p A ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p S]
  exact RingEquiv.ofBijective (s2t_adicMap p (p.map (algebraMap A S))
    (algebraMap A S) Ideal.le_comap_map) (s2t_atPrimeAdicMap_bijective p)

/-- The canonical localization map is bijective on adic rings with the local maximal
ideal written explicitly. -/
theorem s2t_atPrimeAdicMap_maximal_bijective {A S : Type*} [CommRing A] [CommRing S]
    (p : Ideal A) [p.IsMaximal] [Algebra A S] [IsLocalization.AtPrime S p] [IsLocalRing S]
    (h : p ≤ (IsLocalRing.maximalIdeal S).comap (algebraMap A S)) :
    Function.Bijective (s2t_adicMap p (IsLocalRing.maximalIdeal S) (algebraMap A S) h) := by
  apply s2t_adicMap_bijective_of_residues
  intro n
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).toRingEquiv
  have heq : Ideal.quotientMap ((IsLocalRing.maximalIdeal S) ^ n) (algebraMap A S)
      (s2t_adicMap_pow p _ _ h n) = e.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [heq]
  exact e.bijective

end HodgeLean.Foundations.Program
