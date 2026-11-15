import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientPieces
import Mathlib.RingTheory.Ideal.Quotient.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped DirectSum
namespace HodgeLean.Foundations.Program

/-- Homogeneous projection descends to the actual ring quotient by a homogeneous ideal. -/
def s2_homogeneousQuotientProjection {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) (n : ℕ) :
    (A ⧸ I.toIdeal) →+ (A ⧸ I.toIdeal) :=
  QuotientAddGroup.lift I.toIdeal.toAddSubgroup
    ((Ideal.Quotient.mk I.toIdeal).toAddMonoidHom.comp (GradedRing.proj 𝒜 n)) (by
      intro a ha
      change Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n : A) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.isHomogeneous n ha))

/-- The descended projection selects exactly the corresponding actual quotient piece. -/
theorem s2_homogeneousQuotientProjection_of_mem {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    {m : ℕ} {x : A ⧸ I.toIdeal} (hx : x ∈ s2_homogeneousQuotientPiece 𝒜 I m) (n : ℕ) :
    s2_homogeneousQuotientProjection 𝒜 I n x = if n = m then x else 0 := by
  classical
  obtain ⟨a, ha, rfl⟩ := hx
  change Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n : A) = _
  by_cases h : n = m
  · subst n
    rw [if_pos rfl, DirectSum.decompose_of_mem_same 𝒜 ha]
    rfl
  · rw [if_neg h, DirectSum.decompose_of_mem_ne 𝒜 ha (Ne.symm h), map_zero]

/-- Quotient projection recovers each coordinate of the actual direct-sum recomposition. -/
theorem s2_homogeneousQuotientProjection_recompose {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    (z : ⨁ m, s2_homogeneousQuotientPiece 𝒜 I m) (n : ℕ) :
    s2_homogeneousQuotientProjection 𝒜 I n
      (DirectSum.coeAddMonoidHom (s2_homogeneousQuotientPiece 𝒜 I) z) = (z n : A ⧸ I.toIdeal) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, ZeroMemClass.coe_zero]
  | of m x =>
    rw [DirectSum.coeAddMonoidHom_of,
      s2_homogeneousQuotientProjection_of_mem 𝒜 I x.property,
      DirectSum.coe_of_apply]
    by_cases h : n = m
    · subst n; simp only [if_pos rfl, ite_true]
    · rw [if_neg h, if_neg (Ne.symm h)]; rfl
  | add x y hx hy =>
    simp only [map_add, DFinsupp.add_apply, AddMemClass.coe_add, hx, hy]
    rfl

end HodgeLean.Foundations.Program
