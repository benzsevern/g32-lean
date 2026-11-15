import HodgeLean.Adapters.IntersectionProductDefs

/-! # Shared basics for Serre's intersection product

Declarations used by more than one of the `IntersectionProduct*` helper files.

Source: Weibel, *An Introduction to Homological Algebra*, §2.4 (`L_0 F ≅ F` for right exact `F`)
and §2.7 (`Tor`). HC no distance; AV milestone no distance.
-/

open CategoryTheory MonoidalCategory

noncomputable section
namespace HodgeLean.Adapters
universe u

variable {A : Type u} [CommRing A]

/-- `Tor_0(M, N) ≅ M ⊗ N`, since the tensor product is right exact.
Source: Weibel, *An Introduction to Homological Algebra*, §2.4 (`L_0 F ≅ F` for right exact `F`)
and §2.7 (`Tor`);
Mathlib, `Functor.leftDerivedZeroIsoSelf`. -/
def a3c_tor0Iso (M N : ModuleCat.{u} A) : ((Tor (ModuleCat.{u} A) 0).obj M).obj N ≅ M ⊗ N :=
  ((tensoringLeft (ModuleCat.{u} A)).obj M).leftDerivedZeroIsoSelf.app N

example (M : ModuleCat.{u} A) : ((Tor (ModuleCat.{u} A) 0).obj M).obj M ≅ M ⊗ M :=
  a3c_tor0Iso M M

end HodgeLean.Adapters
