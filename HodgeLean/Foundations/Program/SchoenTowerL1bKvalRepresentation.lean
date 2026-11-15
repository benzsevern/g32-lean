import HodgeLean.Foundations.Program.SchoenTowerL1bKvalMaps

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified representation of the actual stalk embeds in the retained covering field. -/
theorem s2v_l1b_kval_represented_stalk_injective
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (x : X) (κ : X.functionField ⟶ CommRingCat.of K)
    (R : Type) [CommRing R] (eR : R ≃+* X.presheaf.stalk x) :
    Function.Injective ((s2v_l1b_kval_stalkMap X x κ).comp eR.toRingHom) :=
  (κ.hom.injective.comp (IsFractionRing.injective (X.presheaf.stalk x)
    X.functionField)).comp eR.injective

/-- A nonzero branch section has a nonzero germ in every represented stalk on its open. -/
theorem s2v_l1b_kval_represented_germ_ne_zero
    (X : Scheme.{0}) [IsIntegral X] (x : X) (U : X.Opens) (hx : x ∈ U)
    (R : Type) [CommRing R] (eR : R ≃+* X.presheaf.stalk x)
    (g : Γ(X, U)) (hg : g ≠ 0) :
    eR.symm ((X.presheaf.germ U x hx).hom g) ≠ 0 := by
  intro h
  apply hg
  apply germ_injective_of_isIntegral X x hx
  have h' := congrArg eR h
  simpa only [eR.apply_symm_apply, map_zero] using h'

end HodgeLean.Foundations.Program
