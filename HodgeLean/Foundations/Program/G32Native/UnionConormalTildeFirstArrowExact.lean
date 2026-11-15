import HodgeLean.Foundations.Program.G32Native.UnionConormalTildeExact
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Exactness from coordinates of the first arrow alone -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- First-arrow coordinates and a last-object presentation suffice for an epic complex. -/
lemma unionConormal_tilde_exact_of_firstArrow
    (R : CommRingCat.{0}) (M N P : ModuleCat R) [IsNoetherian R P]
    (f : M ⟶ N) (g₀ : N ⟶ P)
    (he : Function.Exact f g₀) (hg₀ : Function.Surjective g₀)
    (S : ShortComplex (Spec R).Modules) [Epi S.g]
    (e : Arrow.mk S.f ≅ Arrow.mk ((tilde.functor R).map f))
    (e₃ : S.X₃ ≅ (tilde.functor R).obj P) : S.Exact := by
  exact unionConormal_tilde_exact_of_noetherian R M N P f g₀ he hg₀ S
    (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) e₃ (Arrow.w e.hom).symm

end HodgeLean.Foundations.Program.G32Native
