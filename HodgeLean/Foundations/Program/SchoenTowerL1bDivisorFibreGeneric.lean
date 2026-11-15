import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A point of coheight one in a proper integral embedded subscheme is its generic point. -/
theorem s2v_l1b_divisor_embedded_coheight_one_generic
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : Topology.IsEmbedding f)
    (hng : ∀ t, f t ≠ genericPoint Y) (t : X)
    (ht : Order.coheight (f t) = 1) : t = genericPoint X := by
  have hs : f (genericPoint X) ⤳ f t := (genericPoint_specializes t).map f.continuous
  have hle : f t ≤ f (genericPoint X) := hs
  by_cases hr : f (genericPoint X) ≤ f t
  · apply hf.injective
    exact (inseparable_iff_eq.mp (inseparable_iff_specializes_and.mpr ⟨hs, hr⟩)).symm
  · have hlt : f t < f (genericPoint X) := lt_of_le_not_ge hle hr
    have hc : Order.coheight (f (genericPoint X)) ≤ 1 := by
      rw [← ht]
      exact Order.coheight_anti hle
    have hc' : Order.coheight (f (genericPoint X)) < 1 := by
      rw [← ht]
      exact Order.coheight_strictAnti hlt (lt_of_le_of_lt hc (by simp))
    exact False.elim (hng _ (eq_genericPoint_of_coheight_zero _
      (ENat.lt_one_iff_eq_zero.mp hc')))

end HodgeLean.Foundations.Program
