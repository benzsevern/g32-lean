import HodgeLean.Foundations.Program.SchoenTowerI2bFieldAction
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Eigenvalues of a base-linear binomial field action.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A binomial generator is an eigenvector once the field action fixes its power.
Source: the description of roots of unity as powers of a primitive root. -/
theorem s2v_i2b_binomial_generator_eigenvalue
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[F] K) (v : K) (hv0 : v ≠ 0)
    (hv : d (v ^ m) = v ^ m) :
    ∃ k : ℕ, k < m ∧ d v = algebraMap F K (ζ ^ k) * v := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hroot : IsPrimitiveRoot (algebraMap F K ζ) m :=
    hζ.map_of_injective (algebraMap F K).injective
  have hratio : (d v / v) ^ m = 1 := by
    rw [div_pow, ← map_pow, hv, div_self (pow_ne_zero m hv0)]
  obtain ⟨k, hk, he⟩ := hroot.eq_pow_of_pow_eq_one hratio
  refine ⟨k, hk, ?_⟩
  apply (div_eq_iff hv0).mp
  rw [map_pow]
  exact he.symm

/-- Exact order of the generated-field action forces its scalar eigenvalue to be primitive.
Source: subfield generation and the divisibility characterization of primitive roots. -/
theorem s2v_i2b_eigenvalue_primitive_of_order
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (d : K ≃ₐ[R] K) (a : R) (hv : d v = algebraMap R K a * v)
    (m : ℕ) (ha : a ^ m = 1) (horder : orderOf d = m) :
    IsPrimitiveRoot a m := by
  refine ⟨ha, ?_⟩
  intro n hn
  have hd := s2v_i2b_field_action_pow_eq_one v hgen d a hv n hn
  rw [← horder]
  exact orderOf_dvd_of_pow_eq_one hd

end HodgeLean.Foundations.Program
