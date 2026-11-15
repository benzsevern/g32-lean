import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportSuspension

/-! # Actual support suspension under specified support equalities
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual signed support suspension retains the identity pair transports induced by an equality of the specified supports.
Source: properCycle_real_support_suspension_iso; CategoryTheory.eqToIso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_support_eq
    (Y : TopCat.{0}) (T U : Set Y) (hT : IsClosed T) (hU : IsClosed U)
    (e : T = U) (n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (eqToIso (congrArg (fun V : Set Y => TopPair.ofSubset (X := TopCat.of (ℝ × Y))
        {z | z.1 = 0 ∧ z.2 ∈ V}ᶜ) e)).hom) (n+1) ≫
      (properCycle_real_support_suspension_iso Y U hU n).hom =
      (properCycle_real_support_suspension_iso Y T hT n).hom ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (eqToIso (congrArg (fun V : Set Y => TopPair.ofSubset (X := Y) Vᶜ) e)).hom) n := by
  subst U
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  rfl

/-- The pair transport induced by a support equality is the literal identity ambient subset map.
Source: CategoryTheory.eqToIso; AlgebraicTopology.Singular.TopPair.ofSubsetHom.
HC no distance; AV milestone no distance. -/
theorem properCycle_support_eq_pair_hom
    (Y : TopCat.{0}) (T U : Set Y) (e : T = U)
    (h : Set.MapsTo (𝟙 Y) Tᶜ Uᶜ) :
    (eqToIso (congrArg (fun V : Set Y => TopPair.ofSubset (X := Y) Vᶜ) e)).hom =
      TopPair.ofSubsetHom (𝟙 Y) h := by
  subst U
  ext z : 2 <;> rfl

end HodgeLean.Foundations.QuotientDuality
