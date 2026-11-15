import HodgeLean.Foundations.Program.SchoenCycleAffineStalkMapExt
import Mathlib.AlgebraicGeometry.Restrict

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual map from an open scheme to an affine spectrum has the prescribed original stalk pullback whenever all original affine function pullbacks agree globally.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_open_affine_stalk_comparison
    (X : Scheme) (W V : X.Opens) (hVW : V ≤ W) (S : CommRingCat)
    (φ : S →+* Γ(X, W)) (f : V.toScheme ⟶ Spec S)
    (hglobal : ∀ s : S, f.appTop ((Scheme.ΓSpecIso S).inv s) =
      V.topIso.inv ((X.presheaf.map (homOfLE hVW).op).hom (φ s)))
    (x : X) (hxV : x ∈ V)
    (F : (Spec S).presheaf.stalk (f ⟨x, hxV⟩) →+* X.presheaf.stalk x)
    (hF : ∀ s : S, F (StructureSheaf.toStalk S (f ⟨x, hxV⟩) s) =
      X.presheaf.germ W x (hVW hxV) (φ s)) :
    (f.stalkMap ⟨x, hxV⟩).hom = (V.ι.stalkMap ⟨x, hxV⟩).hom.comp F := by
  let z : V.toScheme := ⟨x, hxV⟩
  have htop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ W := by intro y hy; exact hVW y.property
  have hres : X.presheaf.map (homOfLE hVW).op ≫ V.topIso.inv = V.ι.appLE W ⊤ htop := by
    rw [Scheme.Opens.ι_appLE]
    change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _
    rw [← X.presheaf.map_comp]
    congr 1
  have hg : V.ι.appLE W ⊤ htop ≫ V.toScheme.presheaf.germ ⊤ z trivial =
      X.presheaf.germ W x (hVW hxV) ≫ V.ι.stalkMap z := by
    simp only [Scheme.Hom.appLE, Category.assoc, V.toScheme.presheaf.germ_res']
    exact (V.ι.germ_stalkMap W z (hVW hxV)).symm
  apply s2e_affine_stalk_map_ext S (f z) _ _ _
  intro s
  change f.stalkMap z ((Spec S).presheaf.germ ⊤ (f z) trivial ((Scheme.ΓSpecIso S).inv s)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  change V.toScheme.presheaf.germ ⊤ z trivial (f.appTop ((Scheme.ΓSpecIso S).inv s)) = _
  rw [hglobal s]
  change V.toScheme.presheaf.germ ⊤ z trivial
    (V.topIso.inv ((X.presheaf.map (homOfLE hVW).op).hom (φ s))) = _
  have he := congrArg (fun m : S ⟶ V.toScheme.presheaf.stalk z => m.hom s)
    (congrArg (fun m : Γ(X, W) ⟶ Γ(V.toScheme, ⊤) =>
      CommRingCat.ofHom φ ≫ m ≫ V.toScheme.presheaf.germ ⊤ z trivial) hres)
  rw [Category.assoc, hg] at he
  exact he.trans (congrArg (V.ι.stalkMap z) (hF s)).symm

#print axioms s2e_open_affine_stalk_comparison
end HodgeLean.Foundations.Program
