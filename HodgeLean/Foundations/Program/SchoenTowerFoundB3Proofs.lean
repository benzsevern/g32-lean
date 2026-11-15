import HodgeLean.Foundations.Program.SchoenTowerFoundB2b
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The two-generator fraction chart has its specified ratio coordinate and equation.
Source: Hartshorne, Algebraic Geometry, II.7, proof of Proposition 7.13;
Stacks Project, Section 10.70 (Tag 052Q). -/
theorem s2t_pairChart_coordinate_aux (R : Type) [CommRing R] (x y : R) :
    ∃ t : s2t_reesChart (Ideal.span {x, y}) x,
      t.val = algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x ∧
      algebraMap R _ y = algebraMap R _ x * t ∧
      Function.Surjective (Polynomial.aeval t :
        Polynomial R →ₐ[R] s2t_reesChart (Ideal.span {x, y}) x) := by
  let t : s2t_reesChart (Ideal.span {x, y}) x :=
    ⟨algebraMap R _ y * IsLocalization.Away.invSelf x,
      Algebra.subset_adjoin (Set.mem_range_self
        (⟨y, Ideal.subset_span (by simp)⟩ : Ideal.span {x, y}))⟩
  refine ⟨t, rfl, ?_, ?_⟩
  · apply Subtype.ext
    change algebraMap R (Localization.Away x) y =
      algebraMap R _ x * (algebraMap R _ y * IsLocalization.Away.invSelf x)
    calc
      _ = algebraMap R _ y * (algebraMap R _ x * IsLocalization.Away.invSelf x) := by
        rw [IsLocalization.Away.mul_invSelf, mul_one]
      _ = _ := by ring
  · intro z
    have hle : s2t_reesChart (Ideal.span {x, y}) x ≤
        (Polynomial.aeval (t.val)).range := by
      apply Algebra.adjoin_le
      rintro _ ⟨v, rfl⟩
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp v.property
      refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X, ?_⟩
      change Polynomial.aeval t.val (Polynomial.C a + Polynomial.C b * Polynomial.X) = _
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap R (Localization.Away x) a + algebraMap R (Localization.Away x) b *
        (algebraMap R _ y * IsLocalization.Away.invSelf x) = _
      rw [← hab, map_add, map_mul, map_mul, add_mul]
      have hx : algebraMap R (Localization.Away x) x * IsLocalization.Away.invSelf x = 1 :=
        IsLocalization.Away.mul_invSelf x
      linear_combination -(algebraMap R (Localization.Away x) a) * hx
    obtain ⟨p, hp⟩ := hle z.property
    refine ⟨p, Subtype.ext ?_⟩
    change (s2t_reesChart (Ideal.span {x, y}) x).val (Polynomial.aeval t p) = _
    rw [← Polynomial.aeval_algHom_apply]
    exact hp

end HodgeLean.Foundations.Program
