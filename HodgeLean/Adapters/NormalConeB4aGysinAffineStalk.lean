import HodgeLean.Adapters.NormalConeB4aGysinBridgeDefs

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- The affine stalk equivalence sends the actual germ map to localization
of the affine section ring. -/
theorem a3b4a_gysin_affine_stalk_equiv
    {X : Scheme.{0}} (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ∃ e : X.presheaf.stalk x ≃+* Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal,
      ∀ s : Γ(X, U), e (X.presheaf.germ U x hx s) =
        algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) s := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  let e := IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
  exact ⟨e.toRingEquiv, fun s => e.commutes s⟩

/-- The evaluation kernel of a complex point is its affine prime ideal. -/
theorem a3b4a_gysin_affine_point_kernel
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of ℂ)}
    (U : X.Opens) (hU : IsAffineOpen U) (w : ComplexPoint (Over.mk q))
    (hw : w.underlying ∈ U) :
    RingHom.ker (Point.evaluationHom U ⟨w, hw⟩).hom =
      (hU.primeIdealOf ⟨w.underlying, hw⟩).asIdeal := by
  have hker : RingHom.ker w.stalkHom.hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk w.underlying) := by
    rw [RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot (R := ℂ),
      IsLocalRing.maximalIdeal_comap]
    rfl
  change RingHom.ker (w.stalkHom.hom.comp (X.presheaf.germ U w.underlying hw).hom) = _
  have hp := congrArg PrimeSpectrum.asIdeal
    (hU.primeIdealOf_eq_map_closedPoint ⟨w.underlying, hw⟩)
  change (hU.primeIdealOf ⟨w.underlying, hw⟩).asIdeal =
    (IsLocalRing.maximalIdeal (X.presheaf.stalk w.underlying)).comap
      (X.presheaf.germ U w.underlying hw).hom at hp
  rw [hp, ← hker]
  rfl

end HodgeLean.Adapters
