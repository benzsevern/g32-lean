import HodgeLean.Foundations.Program.SchoenTowerCurvePointCoordinates
import HodgeLean.Foundations.Program.SchoenTowerCoordinateUnramified

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program

/-- The complex algebra structure on a stalk induced by global sections and the structure map.
Source: Mathlib, `TopCat.Presheaf.algebra_section_stalk`; `AlgebraicGeometry.overSpecAlgebra`. -/
@[instance_reducible]
def s2t_complexStalkAlgebra (X : Over (Spec ↧ℂ)) (x : X.left) :
    Algebra ℂ (X.left.presheaf.stalk x) :=
  ((X.left.presheaf.germ ⊤ x trivial).hom.comp
    (@algebraMap ℂ Γ(X.left, ⊤) _ _ (overSpecAlgebra X ⊤))).toAlgebra

attribute [local instance] overSpecAlgebra s2t_complexStalkAlgebra

example (X : Over (Spec ↧ℂ)) (x : X.left) (c : ℂ) :
    algebraMap ℂ (X.left.presheaf.stalk x) c =
      X.left.presheaf.germ ⊤ x trivial (algebraMap ℂ Γ(X.left, ⊤) c) := rfl

/-- Taking the germ of a scalar section agrees with the complex structure on the stalk.
Source: Mathlib, `Scheme.Hom.appLE_map` and `TopCat.Presheaf.germ_res`. -/
theorem s2t_germ_algebraMap (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (x : X.left) (hx : x ∈ U) (c : ℂ) :
    X.left.presheaf.germ U x hx (algebraMap ℂ Γ(X.left, U) c) =
      algebraMap ℂ (X.left.presheaf.stalk x) c := by
  have h : X.hom.appLE ⊤ U (by simp) ≫ X.left.presheaf.germ U x hx =
      X.hom.appLE ⊤ ⊤ (by simp) ≫ X.left.presheaf.germ ⊤ x trivial := by
    rw [← X.hom.appLE_map (U := ⊤) (V := ⊤) (V' := U) (by simp)
      (homOfLE (show U ≤ ⊤ from le_top)).op]
    rw [Category.assoc, X.left.presheaf.germ_res (homOfLE le_top) x hx]
  change (X.hom.appLE ⊤ U (by simp) ≫ X.left.presheaf.germ U x hx)
      ((Scheme.ΓSpecIso ↧ℂ).inv c) =
    (X.hom.appLE ⊤ ⊤ (by simp) ≫ X.left.presheaf.germ ⊤ x trivial)
      ((Scheme.ΓSpecIso ↧ℂ).inv c)
  exact congrArg (fun f : Γ(Spec ↧ℂ, ⊤) ⟶ X.left.presheaf.stalk x =>
    f ((Scheme.ΓSpecIso ↧ℂ).inv c)) h

/-- The germ map from an open section ring as a complex algebra homomorphism.
Source: Mathlib, `TopCat.Presheaf.germ`; `s2t_germ_algebraMap`. -/
def s2t_germAlgHom (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (x : X.left) (hx : x ∈ U) :
    Γ(X.left, U) →ₐ[ℂ] X.left.presheaf.stalk x where
  toRingHom := (X.left.presheaf.germ U x hx).hom
  commutes' := s2t_germ_algebraMap X U x hx

example (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (x : X.left) (hx : x ∈ U)
    (a : Γ(X.left, U)) : s2t_germAlgHom X U x hx a = X.left.presheaf.germ U x hx a := rfl

/-- A smooth complex curve has a formally étale polynomial coordinate in each actual stalk.
Source: Stacks Project, Tag 054L; `nonempty_localEtaleCoordinates`. -/
theorem s2t_curve_stalk_polynomial_coordinates (X : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension 1 X.hom] (x : X.left) :
    ∃ f : Polynomial ℂ →ₐ[ℂ] X.left.presheaf.stalk x,
      letI := f.toRingHom.toAlgebra
      Algebra.FormallyEtale (Polynomial ℂ) (X.left.presheaf.stalk x) := by
  let D := localEtaleCoordinates X 1 x
  let e := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  let ψ := D.coordinateAlgHom.comp e.symm.toAlgHom
  let f := (s2t_germAlgHom X D.neighborhood x D.mem).comp ψ
  refine ⟨f, ?_⟩
  letI : Algebra (Polynomial ℂ) Γ(X.left, D.neighborhood) := ψ.toRingHom.toAlgebra
  letI : Algebra Γ(X.left, D.neighborhood) (X.left.presheaf.stalk x) :=
    (s2t_germAlgHom X D.neighborhood x D.mem).toRingHom.toAlgebra
  letI : Algebra (Polynomial ℂ) (X.left.presheaf.stalk x) := f.toRingHom.toAlgebra
  letI : IsScalarTower (Polynomial ℂ) Γ(X.left, D.neighborhood) (X.left.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hψ : ψ.toRingHom.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective e.symm.bijective) D.etale
  letI : Algebra.Etale (Polynomial ℂ) Γ(X.left, D.neighborhood) := hψ.toAlgebra
  letI : IsLocalization.AtPrime (X.left.presheaf.stalk x)
      (D.isAffine.primeIdealOf ⟨x, D.mem⟩).asIdeal := D.isAffine.isLocalization_stalk ⟨x, D.mem⟩
  letI : Algebra.FormallyEtale Γ(X.left, D.neighborhood) (X.left.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (D.isAffine.primeIdealOf ⟨x, D.mem⟩).asIdeal.primeCompl
  exact Algebra.FormallyEtale.comp (Polynomial ℂ) Γ(X.left, D.neighborhood) _

/-- Each stalk of a smooth complex curve has a nonzero differential generator.
Source: Stacks Project, Tag 054L; the first exact sequence of differentials. -/
theorem s2t_curve_stalk_differential_generator (X : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension 1 X.hom] (x : X.left) :
    ∃ t : X.left.presheaf.stalk x,
      KaehlerDifferential.D ℂ (X.left.presheaf.stalk x) t ≠ 0 ∧
      Submodule.span (X.left.presheaf.stalk x)
        {KaehlerDifferential.D ℂ (X.left.presheaf.stalk x) t} = ⊤ := by
  obtain ⟨f, hf⟩ := s2t_curve_stalk_polynomial_coordinates X x
  letI : Algebra (Polynomial ℂ) (X.left.presheaf.stalk x) := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Polynomial ℂ) (X.left.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Algebra.FormallyEtale (Polynomial ℂ) (X.left.presheaf.stalk x) := hf
  exact ⟨algebraMap (Polynomial ℂ) (X.left.presheaf.stalk x) Polynomial.X,
    s2t_polynomial_coordinate_differential_ne_zero,
    s2t_polynomial_coordinate_differential_spans⟩

end HodgeLean.Foundations.Program
