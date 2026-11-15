import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesUniqueness
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Maps from an arbitrary integral scheme into the actual paired Rees spectrum
agree when their base maps agree and the selected coefficient section is nonzero.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `AlgebraicGeometry.ext_of_isAffine` and `Scheme.ΓSpecIso_inv_naturality`. -/
theorem s2v_i2a_pair_rees_scheme_map_unique
    (R : Type) [CommRing R] (X : Scheme.{0}) [IsIntegral X]
    (x y : R) (f : X ⟶ Spec (CommRingCat.of R))
    (hx : f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) ≠ 0)
    (a₁ a₂ : X ⟶ Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)))
    (h₁ : a₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) = f)
    (h₂ : a₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) = f) : a₁ = a₂ := by
  let C := s2t_reesChart (Ideal.span {x, y}) x
  let φ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  have hb (a : X ⟶ Spec (CommRingCat.of C))
      (ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) = f) :
      (((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ a.appTop).hom).comp (algebraMap R C) = φ := by
    have H : CommRingCat.ofHom (algebraMap R C) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ a.appTop) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := by
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
        ← Scheme.Hom.comp_appTop, ha]
    exact congrArg CommRingCat.Hom.hom H
  have heq := s2v_i2a_pair_rees_map_unique R Γ(X, ⊤) φ x y hx
    (((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ a₁.appTop).hom)
    (((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ a₂.appTop).hom) (hb a₁ h₁) (hb a₂ h₂)
  apply AlgebraicGeometry.ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of C)).inv).mp
  exact congrArg CommRingCat.ofHom heq

end HodgeLean.Foundations.Program
