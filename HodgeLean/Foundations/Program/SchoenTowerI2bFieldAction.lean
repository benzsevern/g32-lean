import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Field.Subfield.Basic

/-! Field generation and the action on integral elements.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A base-linear field action is determined by a field generator.
Source: the universal property of subfield generation. -/
theorem s2v_i2b_field_action_ext
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (d e : K ≃ₐ[R] K) (hv : d v = e v) : d = e := by
  have he : d.toRingHom = e.toRingHom :=
    RingHom.eq_of_eqOn_of_field_closure_eq_top hgen (by
      intro x hx
      rcases hx with ⟨r, rfl⟩ | hx
      · exact (d.commutes r).trans (e.commutes r).symm
      · have hxv : x = v := Set.mem_singleton_iff.mp hx
        subst x
        exact hv)
  ext x
  exact DFunLike.congr_fun he x

/-- The induced action on integral elements respects composition.
Source: functoriality of integral closure. -/
theorem s2v_i2b_integral_action_mul
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (d e : K ≃ₐ[R] K) :
    (d * e).mapIntegralClosure = d.mapIntegralClosure * e.mapIntegralClosure := by
  ext x
  rfl

/-- A scalar eigenvalue determines every iterate on the generator.
Source: induction on powers of a base-linear automorphism. -/
theorem s2v_i2b_field_action_pow_generator
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (d : K ≃ₐ[R] K) (v : K) (a : R)
    (hv : d v = algebraMap R K a * v) (n : ℕ) :
    (d ^ n) v = algebraMap R K a ^ n * v := by
  induction n with
  | zero => simp only [pow_zero, AlgEquiv.one_apply, one_mul]
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, d.commutes, hv]
    rw [pow_succ']
    ring

/-- A root-of-unity eigenvalue bounds the order on the generated field.
Source: subfield generation and the power calculation on a generator. -/
theorem s2v_i2b_field_action_pow_eq_one
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (d : K ≃ₐ[R] K) (a : R) (hv : d v = algebraMap R K a * v)
    (m : ℕ) (ha : a ^ m = 1) : d ^ m = 1 := by
  apply s2v_i2b_field_action_ext v hgen
  rw [s2v_i2b_field_action_pow_generator d v a hv, ← map_pow, ha, map_one, one_mul]
  rfl

/-- Restriction to integral elements respects every iterate.
Source: functoriality of integral closure. -/
theorem s2v_i2b_integral_action_pow
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (d : K ≃ₐ[R] K) (n : ℕ) :
    (d ^ n).mapIntegralClosure = d.mapIntegralClosure ^ n := by
  induction n with
  | zero => ext x; rfl
  | succ n ih => rw [pow_succ, s2v_i2b_integral_action_mul, ih, pow_succ]

end HodgeLean.Foundations.Program
