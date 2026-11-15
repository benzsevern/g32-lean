import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual homogeneous pieces in the quotient by a homogeneous ideal. -/
def s2_homogeneousQuotientPiece {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    (n : ℕ) : AddSubgroup (A ⧸ I.toIdeal) :=
  (𝒜 n).map (Ideal.Quotient.mk I.toIdeal).toAddMonoidHom

/-- The actual quotient pieces retain graded multiplication. -/
instance s2_homogeneousQuotientPiece_gradedMonoid {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    SetLike.GradedMonoid (s2_homogeneousQuotientPiece 𝒜 I) where
  one_mem := ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mk I.toIdeal)⟩
  mul_mem i j a b ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mk I.toIdeal) a b⟩

end HodgeLean.Foundations.Program
