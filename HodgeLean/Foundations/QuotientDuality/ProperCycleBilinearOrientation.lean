import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Span.Basic

/-! # Interchanging the fixed orientation in an actual bilinear pairing
HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.QuotientDuality

/-- A bilinear pairing between two oriented rational lines is bijective in either variable once it is bijective in one variable.
Source: Bourbaki, Algebra, chapter II, sections 1 and 2, linear maps on one-dimensional spaces.
HC no distance; AV milestone no distance. -/
lemma properCycle_bilinear_orientation_swap
    {A B C : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [AddCommGroup C] [Module ℚ C]
    (F : A →ₗ[ℚ] B →ₗ[ℚ] C) (a : A) (b : B)
    (ha : Function.Bijective (LinearMap.toSpanSingleton ℚ A a))
    (hb : Function.Bijective (LinearMap.toSpanSingleton ℚ B b))
    (hF : Function.Bijective (F a)) :
    Function.Bijective (F.flip b) := by
  have hb0 : b ≠ 0 := by
    intro hz
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (hb.1 (by simp [hz]))
  have hab0 : F a b ≠ 0 := fun hz => hb0 (hF.1 (hz.trans (map_zero (F a)).symm))
  constructor
  · intro u v huv
    obtain ⟨r, hr⟩ := ha.2 u
    obtain ⟨s, hs⟩ := ha.2 v
    change r • a = u at hr
    change s • a = v at hs
    have he : r • F a b = s • F a b := by
      simpa only [← hr, ← hs, LinearMap.flip_apply, map_smul, LinearMap.smul_apply] using huv
    have hrs := smul_left_injective ℚ hab0 he
    rw [← hr, ← hs, hrs]
  · intro v
    obtain ⟨u, hu⟩ := hF.2 v
    obtain ⟨r, hr⟩ := hb.2 u
    change r • b = u at hr
    refine ⟨r • a, ?_⟩
    change F (r • a) b = v
    rw [map_smul, LinearMap.smul_apply]
    rw [← hr, map_smul] at hu
    exact hu

end HodgeLean.Foundations.QuotientDuality
