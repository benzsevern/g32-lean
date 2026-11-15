import HodgeLean.Foundations.Program.G32Native.QuotientCodimensionParameters
import Mathlib.Algebra.Module.SpanRankOperations

/-! # Minimal equation count for a regular local quotient -/
noncomputable section
set_option maxHeartbeats 200000
open IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native

/-- For a regular local quotient, codimension equals the dimension of the
ideal's residue fibre, retaining the actual ideal rather than its support.
Source: Stacks Project, Tag 00NR; Atiyah–Macdonald, Introduction to
Commutative Algebra, Proposition 2.8. -/
theorem paired_c3_regular_quotient_generator_rank
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)]
    (hI : I ≤ maximalIdeal R) (r : ℕ)
    (hcodim : ringKrullDim (R ⧸ I) + r = ringKrullDim R) :
    Module.finrank (R ⧸ maximalIdeal R)
      (I ⧸ maximalIdeal R • (⊤ : Submodule R I)) = r := by
  rw [← spanFinrank_eq_finrank_quotient I I.fg_of_isNoetherianRing]
  obtain ⟨n, z, hrn, hz, hIz⟩ :=
    g32l4_regular_quotient_parameters_of_codimension I r hcodim
  let f : Fin r → R := fun j => z (Fin.castLE hrn j)
  have hgen : I = Ideal.span (Set.range f) := by
    rw [hIz]
    congr 1
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.castLE hrn j, j.isLt, rfl⟩
  apply le_antisymm
  · rw [hgen]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans ?_
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp only [Set.ncard_univ, Nat.card_fin]; exact le_rfl)
  · have hlow := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
      (hI.trans (by simpa only [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))))
    obtain ⟨q, hq⟩ := exists_ringKrullDim_eq_natCast (R ⧸ I)
    rw [← hcodim, hq] at hlow
    have hnat : q + r ≤ q + I.spanFinrank := by exact_mod_cast hlow
    omega

#print axioms paired_c3_regular_quotient_generator_rank
end HodgeLean.Foundations.Program.G32Native
