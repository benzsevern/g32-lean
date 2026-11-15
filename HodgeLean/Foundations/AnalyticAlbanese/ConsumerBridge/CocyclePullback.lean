import HodgeLean.Foundations.Singular.Cup

/-! # Actual cocycle pullback along continuous maps
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge

/-- Pullback of actual singular cocycles along their original continuous map.
HC no distance; AV milestone no distance. -/
def actualCocyclePullback (R : Type) [CommRing R] {X Y : TopCat}
    (f : X ⟶ Y) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj Y) n) :
    AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj X) n :=
  ⟨AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) n ψ.val, by
    have h := ConcreteCategory.congr_hom
      ((AlgebraicTopology.Singular.singularCochainComplexMap R f).comm n (n + 1)) ψ.val
    change AlgebraicTopology.Simplicial.coboundary R n
      (AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) n ψ.val) =
      AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) (n + 1)
        (AlgebraicTopology.Simplicial.coboundary R n ψ.val) at h
    rw [show AlgebraicTopology.Simplicial.coboundary R n ψ.val = 0 from ψ.property,
      map_zero] at h
    exact h⟩

/-- Actual cocycle pullback represents the original singular cohomology pullback.
HC no distance; AV milestone no distance. -/
theorem actualCocyclePullback_class (R : Type) [CommRing R] {X Y : TopCat}
    (f : X ⟶ Y) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj Y) n) :
    AlgebraicTopology.Singular.cohomologyMap R n f (Singular.cohomologyClass Y n ψ) =
      Singular.cohomologyClass X n (actualCocyclePullback R f n ψ) :=
  Singular.cohomologyMap_class Y f n ψ _ rfl

end HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge
