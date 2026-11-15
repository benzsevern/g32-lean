import HodgeLean.Foundations.Program.SchoenTowerEtaleLocalCriterion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open Algebra

namespace HodgeLean.Foundations.Program

/-- A finite-presentation map is étale at a prime when its actual local map is flat
and formally unramified. -/
theorem s2t_isEtaleAt_of_local_flat_unramified {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    ∀ [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
      [Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)],
      Algebra.IsEtaleAt R q := by
  intro hflat hunram
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq
        ⟨algebraMap _ _ x, by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  haveI : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  haveI : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  haveI : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  haveI : Algebra.FinitePresentation Rp Sp := by
    haveI : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  letI : Algebra.FormallyEtale Rp Sq :=
    s2t_formallyEtale_of_flat_unramified_localization (R := Rp) (P := Sp)
      (algebraMapSubmonoid Sp q.primeCompl)
  letI : Algebra.FormallyEtale R Rp := .of_isLocalization p.primeCompl
  exact Algebra.FormallyEtale.comp R Rp Sq

/-- The actual local adic algebra comparison gives étaleness at the source prime. -/
theorem s2t_isEtaleAt_of_localAdicAlgEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [Algebra.FinitePresentation R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    ∀ [Algebra.IsSeparable
      (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime q))]
      (e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) ≃ₐ[Localization.AtPrime p]
        AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)),
      Algebra.IsEtaleAt R q := by
  intro hsep e
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  letI := Localization.AtPrime.algebraOfLiesOver p q
  letI : Algebra.EssFiniteType S Sq := .of_isLocalization Sq q.primeCompl
  letI : Algebra.EssFiniteType R Sq := .comp R S Sq
  letI : Algebra.EssFiniteType Rp Sq := .of_comp R Rp Sq
  letI : Module.Flat Rp Sq := s2t_flat_of_localAdicAlgEquiv e
  letI : Algebra.FormallyUnramified Rp Sq := s2t_unramified_of_localAdicAlgEquiv e
  exact s2t_isEtaleAt_of_local_flat_unramified p q

end HodgeLean.Foundations.Program
