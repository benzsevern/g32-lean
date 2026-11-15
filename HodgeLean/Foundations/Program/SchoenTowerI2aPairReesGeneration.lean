import HodgeLean.Foundations.Program.SchoenTowerFoundB3
import HodgeLean.Foundations.Program.SchoenTowerI2aReesFields
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The actual paired Rees chart is generated inside its localization by its
specified ratio, with the entire coefficient ring retained.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Algebra.adjoin_singleton_eq_range_aeval`. -/
theorem s2v_i2a_pair_rees_adjoin_ratio
    (R : Type) [CommRing R] (x y : R) :
    s2t_reesChart (Ideal.span {x, y}) x =
      Algebra.adjoin R ({algebraMap R (Localization.Away x) y *
        IsLocalization.Away.invSelf x} : Set (Localization.Away x)) := by
  obtain ⟨t, ht, hyt, hsur⟩ := s2t_pairChart_coordinate R x y
  let C := s2t_reesChart (Ideal.span {x, y}) x
  have hc : C.val.comp (Polynomial.aeval t) = Polynomial.aeval t.val := by
    ext
    simp
  have hr : (Polynomial.aeval t).range = ⊤ := (AlgHom.range_eq_top _).mpr hsur
  rw [Algebra.adjoin_singleton_eq_range_aeval, ← ht, ← hc, AlgHom.range_comp, hr]
  rw [Algebra.map_top, Subalgebra.range_val]

end HodgeLean.Foundations.Program
