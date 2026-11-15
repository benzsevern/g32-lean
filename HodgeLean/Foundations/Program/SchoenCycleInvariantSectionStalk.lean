import Mathlib.AlgebraicGeometry.Scheme

/-! # Pullback of actual quotient section germs along invariant morphisms -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback along a morphism over a quotient preserves every pulled-back section germ, even when the point moves.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_invariant_section_stalk_pullback
    {X Y : Scheme} (u : X ⟶ X) (f : X ⟶ Y) (hu : u ≫ f = f)
    (U : Y.Opens) (x : X) (hx : f x ∈ U) (hux : f (u x) ∈ U)
    (s : Γ(Y, U)) :
    u.stalkMap x (f.stalkMap (u x) (Y.presheaf.germ U (f (u x)) hux s)) =
      f.stalkMap x (Y.presheaf.germ U (f x) hx s) := by
  change (f.stalkMap (u x) ≫ u.stalkMap x)
    (Y.presheaf.germ U (f (u x)) hux s) = _
  rw [← Scheme.Hom.stalkMap_comp]
  change (u ≫ f).stalkMap x (Y.presheaf.germ U ((u ≫ f) x) hux s) = _
  have he : ∀ (g : X ⟶ Y), g = f → ∀ hg : g x ∈ U,
      g.stalkMap x (Y.presheaf.germ U (g x) hg s) =
        f.stalkMap x (Y.presheaf.germ U (f x) hx s) := by
    rintro g rfl hg
    rfl
  exact he (u ≫ f) hu hux

end HodgeLean.Foundations.Program
