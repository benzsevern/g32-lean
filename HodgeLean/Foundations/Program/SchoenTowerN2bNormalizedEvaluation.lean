import HodgeLean.Foundations.Program.SchoenNormalizedProjChart
import HodgeLean.Foundations.Program.SchoenTowerN2bHomogeneousEvaluation
import Mathlib.AlgebraicGeometry.AffineSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual affine spectrum morphism evaluates sections through its coefficient map. -/
theorem n2b_toSpec_evaluation {R : Type} [CommRing R]
    (X : Scheme.{0}) (f : R →+* Γ(X, ⊤)) (r : R) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = f r := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop = CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun e => e.hom r) h

/-- The normalized coordinate fraction evaluates to the retained numerator section. -/
theorem n2b_normalized_coordinate_evaluation
    {R κ : Type} [CommRing R] (X : Scheme.{0})
    (q : R →+* Γ(X, ⊤)) (a : κ → Γ(X, ⊤))
    (k : κ) (hk : a k = 1) (t : κ) :
    let φ := eval₂Hom q a
    let hφ : φ (MvPolynomial.X k) = 1 := by rw [eval₂Hom_X', hk]
    let f := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (s2_normalizedChartLift (homogeneousSubmodule κ R) (MvPolynomial.X k) φ hφ))
    f.appTop.hom ((Scheme.ΓSpecIso _).inv.hom
      (Away.mk (homogeneousSubmodule κ R) (isHomogeneous_X R k) 1
        (MvPolynomial.X t) (by simpa only [one_smul, mem_homogeneousSubmodule] using isHomogeneous_X R t))) = a t := by
  dsimp only
  rw [n2b_toSpec_evaluation, s2_normalizedChartLift_mk, eval₂Hom_X']

end HodgeLean.Foundations.Program
