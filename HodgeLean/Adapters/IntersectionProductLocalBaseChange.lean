import HodgeLean.Adapters.IntersectionProductTorLocal

/-! # Flat base change for local intersection multiplicities

Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9;
Fulton, *Intersection Theory*, second edition, §20.4. -/

open CategoryTheory

noncomputable section
namespace HodgeLean.Adapters

universe u

/-- Flat base change identifies Tor after extending both finite-module arguments. -/
theorem a3i_flat_tor_basechange {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.Flat) (M N : ModuleCat.{u} A) (i : ℕ) :
    Nonempty (((Tor (ModuleCat.{u} B) i).obj
      ((ModuleCat.extendScalars.{u, u, u} f).obj M)).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj N) ≅
      (ModuleCat.extendScalars.{u, u, u} f).obj
        (((Tor (ModuleCat.{u} A) i).obj M).obj N)) := by
  exact a3q_tor_baseChange f hf M N i

end HodgeLean.Adapters
