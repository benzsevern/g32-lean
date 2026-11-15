import HodgeLean.Foundations.Program.SchoenCyclePrescribedDifferentialEtale
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program
universe u

/-- Étaleness of prescribed localized polynomial coordinates transfers to the actual localization algebra, preserving each chosen function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_actual_localization_coordinate_etale
    (R S T σ : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : S) [IsLocalization.Away g T] (c : σ → S)
    (h : (aeval (R := R) (fun i => algebraMap S (Localization.Away g) (c i))).toRingHom.Etale) :
    (aeval (R := R) (fun i => algebraMap S T (c i))).toRingHom.Etale := by
  let E := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) T
  have he : (E.restrictScalars R).toAlgHom.comp
      (aeval (R := R) (fun i => algebraMap S (Localization.Away g) (c i))) =
      aeval (R := R) (fun i => algebraMap S T (c i)) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact E.commutes (c i)
  rw [← he]
  exact RingHom.Etale.stableUnderComposition _ E.toRingHom h (RingHom.Etale.of_bijective E.bijective)

#print axioms s2e_actual_localization_coordinate_etale
end HodgeLean.Foundations.Program
