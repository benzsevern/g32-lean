import HodgeLean.Foundations.Program.TorusAlgebraizationB54LocalCarrier

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Point
namespace HodgeLean.Foundations.Program

def b54_globalEvaluation {X : Over (Spec ↧ℂ)} (p : ComplexPoint X) :
    Γ(X.left, ⊤) →+* ℂ := (Scheme.ΓSpecIso ↧ℂ).hom.hom.comp p.left.appTop.hom

def b54_globalScalar (X : Over (Spec ↧ℂ)) : ℂ →+* Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp (Scheme.ΓSpecIso ↧ℂ).inv.hom

theorem b54_globalEvaluation_scalar {X : Over (Spec ↧ℂ)} (p : ComplexPoint X) (c : ℂ) :
    b54_globalEvaluation p (b54_globalScalar X c) = c := by
  change (Scheme.ΓSpecIso ↧ℂ).hom
    (p.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c))) = c
  change ((X.hom.appTop ≫ p.left.appTop) ≫ (Scheme.ΓSpecIso ↧ℂ).hom)
    ((Scheme.ΓSpecIso ↧ℂ).inv c) = c
  rw [← Scheme.Hom.comp_appTop, p.w]
  simp

theorem b54_globalEvaluation_map {X Y : Over (Spec ↧ℂ)} (f : Y ⟶ X)
    (p : ComplexPoint Y) (s : Γ(X.left, ⊤)) :
    b54_globalEvaluation p (f.left.appTop s) = b54_globalEvaluation (map f p) s := by
  change (Scheme.ΓSpecIso ↧ℂ).hom ((f.left.appTop ≫ p.left.appTop) s) = _
  rw [← Scheme.Hom.comp_appTop]
  rfl

theorem b54_globalEvaluation_Spec {A : Type} [CommRing A]
    (f : Spec (.of A) ⟶ Spec ↧ℂ) (p : ComplexPoint (Over.mk f))
    (φ : A →+* ℂ) (hφ : p.left = Spec.map (CommRingCat.ofHom φ)) (a : A) :
    b54_globalEvaluation p ((Scheme.ΓSpecIso (.of A)).inv a) = φ a := by
  change (Scheme.ΓSpecIso ↧ℂ).hom (p.left.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) = φ a
  rw [hφ]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso (.of A)).inv a)
  convert h' using 1
  simp

theorem b54_globalEvaluation_polynomial {X : Over (Spec ↧ℂ)} (p : ComplexPoint X)
    {ι : Type*} (v : ι → Γ(X.left, ⊤)) (P : MvPolynomial ι ℂ) :
    b54_globalEvaluation p (MvPolynomial.eval₂Hom (b54_globalScalar X) v P) =
      MvPolynomial.eval (fun i => b54_globalEvaluation p (v i)) P := by
  have he : (b54_globalEvaluation p).comp (b54_globalScalar X) = RingHom.id ℂ :=
    RingHom.ext (b54_globalEvaluation_scalar p)
  rw [MvPolynomial.map_eval₂Hom, he]
  rfl

end HodgeLean.Foundations.Program
