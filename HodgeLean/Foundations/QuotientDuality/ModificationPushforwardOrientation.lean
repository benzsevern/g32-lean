import HodgeLean.Foundations.QuotientDuality.LocalOrientationSheaf
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality

/-! A local degree-one equation normalizes the pushed class at every target point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem singletonFibre_pushforward_local_orientation
    (X Y : TopCat.{0}) [T2Space Y] [PreconnectedSpace Y]
    (n : ℕ) (oY : LocalRationalOrientation Y n) (c : Homology ℚ X n)
    (f : X ⟶ Y) (x : X) (hf : ∀ z, f z = f x → z = x)
    (hlocal : relativeHomologyMap ℚ n (singletonFibrePairMap f x (f x) hf)
      (localOrientation X n c x) = oY.generator (f x)) :
    ∀ y, localOrientation Y n (homologyMap ℚ n f c) y = oY.generator y := by
  obtain ⟨q, hq⟩ := local_values_constant Y n oY (homologyMap ℚ n f c)
  have hy : localOrientation Y n (homologyMap ℚ n f c) (f x) = oY.generator (f x) :=
    (localOrientation_map n x (f x) (singletonFibrePairMap f x (f x) hf) c).symm.trans hlocal
  have hq1 : q = 1 := (oY.generates (f x)).1 (by
    change q • oY.generator (f x) = (1 : ℚ) • oY.generator (f x)
    exact (hq (f x)).symm.trans (hy.trans (one_smul ℚ _).symm))
  intro y
  exact (hq y).trans (by rw [hq1, one_smul])

#print axioms singletonFibre_pushforward_local_orientation
end HodgeLean.Foundations.QuotientDuality
