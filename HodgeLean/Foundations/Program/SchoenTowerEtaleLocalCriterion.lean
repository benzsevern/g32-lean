import HodgeLean.Foundations.Program.SchoenTowerAdicFlatCriterion
import Mathlib.RingTheory.Smooth.Fiber

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-- A flat unramified local algebra with an explicit finite-presentation localization
is formally étale. -/
theorem s2t_formallyEtale_of_flat_unramified_localization {R P S : Type*}
    [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S] [Algebra R S]
    [IsScalarTower R P S] [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R P] [Module.Flat R S] [Algebra.FormallyUnramified R S]
    (M : Submonoid P) [IsLocalization M S] : Algebra.FormallyEtale R S := by
  letI : Algebra.EssFiniteType P S := .of_isLocalization S M
  letI : Algebra.EssFiniteType R S := .comp R P S
  letI : Algebra.FormallyEtale (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  letI : Algebra.FormallySmooth R S :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := R) (P := P) M
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- The local adic algebra comparison yields formal étaleness for an explicit
finite-presentation localization with separable residue fields. -/
theorem s2t_formallyEtale_of_localAdicAlgEquiv_presentation {R P S : Type*}
    [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S] [Algebra R S]
    [IsScalarTower R P S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R P]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    (M : Submonoid P) [IsLocalization M S]
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal S) S) : Algebra.FormallyEtale R S := by
  letI : Algebra.EssFiniteType P S := .of_isLocalization S M
  letI : Algebra.EssFiniteType R S := .comp R P S
  letI : Module.Flat R S := s2t_flat_of_localAdicAlgEquiv e
  letI : Algebra.FormallyUnramified R S := s2t_unramified_of_localAdicAlgEquiv e
  exact s2t_formallyEtale_of_flat_unramified_localization M

end HodgeLean.Foundations.Program
