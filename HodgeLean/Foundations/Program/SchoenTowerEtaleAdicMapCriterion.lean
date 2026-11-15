import HodgeLean.Foundations.Program.SchoenTowerEtaleAtPrimeCriterion
import HodgeLean.Foundations.Program.SchoenTowerAtPrimeAdic
import HodgeLean.Foundations.Program.SchoenTowerAdicAlgHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A bijective actual adic map at maximal ideals gives étaleness at the source ideal. -/
theorem s2t_isEtaleAt_of_adicMap_bijective {R S : Type*}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [Algebra.FinitePresentation R S]
    (p : Ideal R) (q : Ideal S) [p.IsMaximal] [q.IsMaximal] [q.LiesOver p]
    (h : p ≤ q.comap (algebraMap R S))
    (hbij : Function.Bijective (s2t_adicMap p q (algebraMap R S) h)) :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    ∀ [Algebra.IsSeparable
      (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime q))],
      Algebra.IsEtaleAt R q := by
  intro hsep
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hα : p ≤ (IsLocalRing.maximalIdeal Rp).comap (algebraMap R Rp) :=
    Ideal.map_le_iff_le_comap.mp (IsLocalization.AtPrime.map_eq_maximalIdeal p Rp).le
  have hβ : q ≤ (IsLocalRing.maximalIdeal Sq).comap (algebraMap S Sq) :=
    Ideal.map_le_iff_le_comap.mp (IsLocalization.AtPrime.map_eq_maximalIdeal q Sq).le
  have hF : (IsLocalRing.maximalIdeal Rp) ≤
      (IsLocalRing.maximalIdeal Sq).comap (algebraMap Rp Sq) :=
    Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le (algebraMap Rp Sq))
  let α := s2t_adicMap p (IsLocalRing.maximalIdeal Rp) (algebraMap R Rp) hα
  let β := s2t_adicMap q (IsLocalRing.maximalIdeal Sq) (algebraMap S Sq) hβ
  let f₀ := s2t_adicMap p q (algebraMap R S) h
  let F := s2t_adicAlgHom (IsLocalRing.maximalIdeal Rp) (IsLocalRing.maximalIdeal Sq) hF
  have hαbij := s2t_atPrimeAdicMap_maximal_bijective p hα
  have hβbij := s2t_atPrimeAdicMap_maximal_bijective q hβ
  have hcomm (x : AdicCompletion p R) : F (α x) = β (f₀ x) := by
    change s2t_adicMap (IsLocalRing.maximalIdeal Rp) (IsLocalRing.maximalIdeal Sq)
      (algebraMap Rp Sq) hF (s2t_adicMap p (IsLocalRing.maximalIdeal Rp)
        (algebraMap R Rp) hα x) =
      s2t_adicMap q (IsLocalRing.maximalIdeal Sq) (algebraMap S Sq) hβ
        (s2t_adicMap p q (algebraMap R S) h x)
    rw [s2t_adicMap_comp, s2t_adicMap_comp]
    have heq : (algebraMap Rp Sq).comp (algebraMap R Rp) =
        (algebraMap S Sq).comp (algebraMap R S) :=
      (IsScalarTower.algebraMap_eq R Rp Sq).symm.trans (IsScalarTower.algebraMap_eq R S Sq)
    exact congrArg (fun F : AdicCompletion p R →+* AdicCompletion (IsLocalRing.maximalIdeal Sq) Sq => F x) (s2t_adicMap_congr p (IsLocalRing.maximalIdeal Sq)
      _ _ _ _ heq)
  have hFbij : Function.Bijective F := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hαbij.surjective x
      obtain ⟨b, rfl⟩ := hαbij.surjective y
      apply congrArg α
      apply hbij.injective
      apply hβbij.injective
      rw [← hcomm, ← hcomm]
      exact hxy
    · intro z
      obtain ⟨a, ha⟩ := hβbij.surjective z
      obtain ⟨b, hb⟩ := hbij.surjective a
      refine ⟨α b, ?_⟩
      rw [hcomm, hb, ha]
  exact s2t_isEtaleAt_of_localAdicAlgEquiv p q (AlgEquiv.ofBijective F hFbij)

end HodgeLean.Foundations.Program
