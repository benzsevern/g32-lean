import HodgeLean.Foundations.Program.SchoenTowerAffineLocalGenerators
import HodgeLean.Foundations.Program.SchoenTowerFiniteSupportCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra s2t_complexStalkAlgebra

/-- Restriction of global regular functions as a complex algebra homomorphism.
Source: Mathlib, `Scheme.Hom.appLE_map`. -/
def s2t_globalRestrictionAlgHom (X : Over (Spec ↧ℂ)) (U : X.left.Opens) :
    Γ(X.left, ⊤) →ₐ[ℂ] Γ(X.left, U) where
  toRingHom := (X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  commutes' c := by
    have h := X.hom.appLE_map (U := ⊤) (V := ⊤) (V' := U) (by simp)
      (homOfLE (show U ≤ ⊤ from le_top)).op
    change (X.hom.appLE ⊤ ⊤ (by simp) ≫
      X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op)
        ((Scheme.ΓSpecIso ↧ℂ).inv c) =
      X.hom.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv c)
    exact congrArg (fun f : Γ(Spec ↧ℂ, ⊤) ⟶ Γ(X.left, U) =>
      f ((Scheme.ΓSpecIso ↧ℂ).inv c)) h

example (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (a : Γ(X.left, ⊤)) :
    s2t_globalRestrictionAlgHom X U a =
      X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a := rfl

/-- An étale polynomial coordinate on a principal localization gives an actual affine-line
morphism on the corresponding scheme open, with its prescribed pointwise value.
Source: Stacks Project, Tag 054L; `LocalEtaleCoordinates.toAffineSpaceOver`. -/
theorem s2t_principal_etale_coordinate (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    [SmoothOfRelativeDimension 1 X.hom] (g r : Γ(X.left, ⊤))
    (p : ComplexPoint X) (hp : Point.evaluate ⊤ r p ≠ 0)
    (hEt : letI := (Polynomial.aeval (R := ℂ) g).toRingHom.toAlgebra
      Algebra.Etale (Polynomial ℂ) (Localization.Away r)) :
    ∃ f : openScheme X (X.left.basicOpen r) ⟶
      Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ),
      Etale f.left ∧ ∀ z,
        affineSpaceEquiv (Fin 1) (Point.map f z) 0 =
          Point.evaluate ⊤ g (Point.map (openInclusion X (X.left.basicOpen r)) z) := by
  let A := Γ(X.left, ⊤)
  let U := X.left.basicOpen r
  let R := Γ(X.left, U)
  have hU : IsAffineOpen U := (isAffineOpen_top X.left).basicOpen r
  have hx : p.underlying ∈ U :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r p (show p ∈ Point.overOpen ⊤ from trivial)).mpr hp
  let ρ := s2t_globalRestrictionAlgHom X U
  let ψ := ρ.comp (Polynomial.aeval (R := ℂ) g)
  letI : Algebra (Polynomial ℂ) A := (Polynomial.aeval (R := ℂ) g).toRingHom.toAlgebra
  letI : Algebra (Polynomial ℂ) R := ψ.toRingHom.toAlgebra
  letI : IsScalarTower (Polynomial ℂ) A R := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization.Away r R := (isAffineOpen_top X.left).isLocalization_basicOpen r
  letI : Algebra.Etale (Polynomial ℂ) (Localization.Away r) := hEt
  let e := IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) R
  letI : Algebra.Etale (Polynomial ℂ) R := Algebra.Etale.of_equiv (e.restrictScalars (Polynomial ℂ))
  have hψ : ψ.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let δ := ψ.comp (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toAlgHom
  have hδ : δ.toRingHom.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).bijective) hψ
  let D : LocalEtaleCoordinates X 1 p.underlying := ⟨U, hU, hx, δ, hδ⟩
  letI : IsAffine D.neighborhood.toScheme := D.isAffine
  letI : Etale (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen)) :=
    HasRingHomProperty.Spec_iff.mpr D.coordinateRingHomOnOpen_etale
  have hf : Etale D.toAffineSpace := by
    dsimp only [LocalEtaleCoordinates.toAffineSpace]
    have h₁ : Etale D.neighborhood.toScheme.toSpecΓ := inferInstance
    have h₂ : Etale (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen) ≫
        (AffineSpace.SpecIso (Fin 1) ↧ℂ).inv) := Etale.etale_comp
          (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen))
          (AffineSpace.SpecIso (Fin 1) ↧ℂ).inv
    exact @Etale.etale_comp _ _ _ _ _ h₁ h₂
  refine ⟨D.toAffineSpaceOver, hf, ?_⟩
  intro z
  change D.analyticCoordinates z 0 = _
  rw [D.analyticCoordinates_apply_eq_evaluate]
  have hδX : δ (MvPolynomial.X (0 : Fin 1)) = ρ g := by
    change ρ (Polynomial.aeval (R := ℂ) g
      (MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) (MvPolynomial.X 0))) = _
    rw [MvPolynomial.eval₂_X, Polynomial.aeval_X]
  have hres : D.coordinateRingHomOnOpen (MvPolynomial.X (0 : Fin 1)) = U.ι.appTop g := by
    change U.topIso.inv (δ (MvPolynomial.X 0)) = _
    rw [hδX]
    apply U.topIso.commRingCatIsoToRingEquiv.injective
    change U.topIso.hom (U.topIso.inv (ρ g)) = U.topIso.hom (U.ι.appTop g)
    rw [Iso.inv_hom_id_apply]
    exact (congrArg (fun f : A ⟶ R => f g) (Scheme.Opens.ι_appTop_topIso_hom U)).symm
  rw [hres]
  exact (Point.evaluate_map (openInclusion X U) ⊤ g z).symm

end HodgeLean.Foundations.Program
