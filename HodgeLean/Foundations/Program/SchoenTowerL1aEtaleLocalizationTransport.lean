import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Etale localization transport through actual presentations

Implication from compatible source and target ring identifications to
etaleness of the corresponding actual principal restriction.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
universe u

/-- Etaleness on a principal restriction transports through commuting actual
source and target ring isomorphisms, with the transported denominator.
Source: Hartshorne, Algebraic Geometry, III.10, etaleness under isomorphism. -/
theorem s2v_l1a_etale_localization_transport
    {R R' D D' : Type u} [CommRing R] [CommRing R'] [CommRing D] [CommRing D']
    (f : R →+* D) (f' : R' →+* D') (eR : R ≃+* R') (eD : D ≃+* D')
    (hcomm : eD.toRingHom.comp f = f'.comp eR.toRingHom) (d : D')
    (hEt : ((algebraMap D' (Localization.Away d)).comp f').Etale) :
    ((algebraMap D (Localization.Away (eD.symm d))).comp f).Etale := by
  have hm : (Submonoid.powers (eD.symm d)).map eD.toMonoidHom = Submonoid.powers d := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (eD.apply_symm_apply d)
  let e := IsLocalization.ringEquivOfRingEquiv
    (Localization.Away (eD.symm d)) (Localization.Away d) eD hm
  have H := RingHom.Etale.respectsIso.2 _ eR hEt
  have H' := RingHom.Etale.respectsIso.1 _ e.symm H
  have heq : e.symm.toRingHom.comp
      (((algebraMap D' (Localization.Away d)).comp f').comp eR.toRingHom) =
        (algebraMap D (Localization.Away (eD.symm d))).comp f := by
    ext r
    apply e.injective
    change e (e.symm (algebraMap D' (Localization.Away d) (f' (eR r)))) =
      e (algebraMap D (Localization.Away (eD.symm d)) (f r))
    rw [e.apply_symm_apply, IsLocalization.ringEquivOfRingEquiv_eq]
    exact congrArg (algebraMap D' (Localization.Away d))
      (DFunLike.congr_fun hcomm r).symm
  rw [heq] at H'
  exact H' 

end HodgeLean.Foundations.Program
