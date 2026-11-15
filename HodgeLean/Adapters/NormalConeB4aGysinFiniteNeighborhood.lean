import HodgeLean.Adapters.NormalConeB4aGysinAffineChart
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite flat models near quasi-finite points -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry

/-- A flat morphism has a finite flat neighborhood of a quasi-finite point after
an étale base change.
Source: Mathlib `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`
and stability of flatness under base change and open restriction. -/
theorem a3b4a_gysin_finite_flat_etale_neighborhood
    {X B : Scheme.{0}} (f : X ⟶ B) [LocallyOfFiniteType f] [IsSeparated f] [Flat f]
    (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{0}) (g : U ⟶ B), Etale g ∧ f x ∈ Set.range g ∧
      ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧
        IsFinite (V.ι ≫ pullback.snd f g) ∧ Flat (V.ι ≫ pullback.snd f g) ∧
        pullback.fst f g v.1 = x := by
  obtain ⟨U, g, hg, hxg, V, W, v, hVW, hfin, hv⟩ :=
    exists_etale_isCompl_of_quasiFiniteAt f rfl hx
  exact ⟨U, g, hg, hxg, V, W, v, hVW, hfin, inferInstance, hv⟩

end HodgeLean.Adapters
