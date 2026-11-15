import HodgeLean.Foundations.Program.SchoenCycleOpenAffineStalkComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Retained exact section germs pull back along the actual open-to-affine morphism after the marked points are identified, with no chosen stalk transport in the resulting identity.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_open_affine_section_pullback
    (X : Scheme) (W V : X.Opens) (hVW : V ≤ W) (S : CommRingCat)
    (φ : S →+* Γ(X, W)) (f : V.toScheme ⟶ Spec S)
    (hglobal : ∀ s : S, f.appTop ((Scheme.ΓSpecIso S).inv s) =
      V.topIso.inv ((X.presheaf.map (homOfLE hVW).op).hom (φ s)))
    (y : V.toScheme) (x : X) (hy : y.val = x) (p : PrimeSpectrum S) (hp : f y = p)
    (F : (Spec S).presheaf.stalk p →+* X.presheaf.stalk x)
    (hF : ∀ s : S, F (StructureSheaf.toStalk S p s) =
      X.presheaf.germ W x (hy ▸ hVW y.property) (φ s))
    (U : (Spec S).Opens) (hpU : p ∈ U) (s : Γ(Spec S, U))
    (K : X.Opens) (hxK : x ∈ K) (t : Γ(X, K))
    (hvalue : F ((Spec S).presheaf.germ U p hpU s) = X.presheaf.germ K x hxK t) :
    V.toScheme.presheaf.germ (f ⁻¹ᵁ U) y (by change f y ∈ U; rw [hp]; exact hpU) (f.app U s) =
      V.toScheme.presheaf.germ (V.ι ⁻¹ᵁ K) y (by change y.val ∈ K; rw [hy]; exact hxK) (V.ι.app K t) := by
  subst x
  subst p
  rw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  have he := s2e_open_affine_stalk_comparison X W V hVW S φ f hglobal y.val y.property F hF
  exact (congrArg (fun H => H ((Spec S).presheaf.germ U (f y) hpU s)) he).trans
    (congrArg (V.ι.stalkMap y) hvalue)

#print axioms s2e_open_affine_section_pullback
end HodgeLean.Foundations.Program
