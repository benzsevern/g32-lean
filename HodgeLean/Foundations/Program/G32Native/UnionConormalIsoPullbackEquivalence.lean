import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Module pullback along a scheme isomorphism is an equivalence -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The inverse scheme isomorphism provides a quasi-inverse to module pullback. -/
lemma unionConormal_isoPullback_isEquivalence
    {X Y : Scheme.{0}} (b : X ⟶ Y) [IsIso b] :
    (Scheme.Modules.pullback b).IsEquivalence := by
  let e₁ : Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback (inv b) ≅ 𝟭 Y.Modules :=
    Scheme.Modules.pullbackComp (inv b) b ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id b) ≪≫ Scheme.Modules.pullbackId Y
  let e₂ : Scheme.Modules.pullback (inv b) ⋙ Scheme.Modules.pullback b ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp b (inv b) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.hom_inv_id b) ≪≫ Scheme.Modules.pullbackId X
  exact Functor.IsEquivalence.mk' (Scheme.Modules.pullback (inv b)) e₁.symm e₂

end HodgeLean.Foundations.Program.G32Native
