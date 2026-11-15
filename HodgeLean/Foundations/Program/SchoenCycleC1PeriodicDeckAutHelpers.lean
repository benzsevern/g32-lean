import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Commute.Units

/-! # Automorphisms over the actual base from periodic deck morphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A periodic deck endomorphism defines an actual automorphism over its
specified projection, retaining the original underlying scheme morphism. -/
theorem s2e_c1_periodic_deckAut
    {X Y : Scheme} (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f)
    (m : ℕ) (hm : m ≠ 0) (hpow : End.of d ^ m = 1) :
    ∃ u : Aut (Over.mk f), u.asIso.hom.left = d := by
  haveI : IsIso d := (isUnit_iff_isIso _).mp (IsUnit.of_pow_eq_one hpow hm)
  let D : Over.mk f ⟶ Over.mk f := Over.homMk d hd
  haveI : IsIso ((Over.forget Y).map D) := by
    change IsIso d
    infer_instance
  haveI : IsIso D := isIso_of_reflects_iso D (Over.forget Y)
  exact ⟨Aut.of (asIso D), rfl⟩

end HodgeLean.Foundations.Program
