import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # Recovering actual local ideals from all finite neighbourhoods -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- An ideal in a Noetherian local ring is detected modulo every power of the
maximal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, Ideal.iInf_pow_eq_bot_of_isLocalRing. -/
theorem s2e_local_ideal_mem_of_all_power_neighbourhoods
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) (r : R)
    (hr : ∀ N : ℕ, r ∈ J ⊔ IsLocalRing.maximalIdeal R ^ N) : r ∈ J := by
  by_cases hJ : J = ⊤
  · rw [hJ]
    exact Submodule.mem_top
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let I := (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)
  have hI : I ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (Ideal.Quotient.mk J)).ne
  have hz : Ideal.Quotient.mk J r ∈ ⨅ N : ℕ, I ^ N := by
    rw [Ideal.mem_iInf]
    intro N
    have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) (hr N)
    simpa only [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow] using hm
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing I hI, Ideal.mem_bot] at hz
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hz

end HodgeLean.Foundations.Program
