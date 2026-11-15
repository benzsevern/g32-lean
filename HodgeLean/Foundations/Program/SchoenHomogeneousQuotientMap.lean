import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientGrading
import Mathlib.RingTheory.GradedAlgebra.RingHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual quotient ring map preserves the inherited homogeneous pieces. -/
def s2_homogeneousQuotientMap {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    𝒜 →+*ᵍ s2_homogeneousQuotientPiece 𝒜 I :=
  { Ideal.Quotient.mk I.toIdeal with map_mem := fun {_} {a} ha => ⟨a, ha, rfl⟩ }

end HodgeLean.Foundations.Program
