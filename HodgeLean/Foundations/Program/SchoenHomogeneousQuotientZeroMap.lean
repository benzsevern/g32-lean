import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientGrading
import Mathlib.Algebra.Field.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The actual quotient map restricted to homogeneous degree zero. -/
def s2_homogeneousQuotientZeroMap {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    𝒜 0 →+* s2_homogeneousQuotientPiece 𝒜 I 0 := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  exact
    { toFun := fun a => ⟨Ideal.Quotient.mk I.toIdeal a, ⟨a, a.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one (Ideal.Quotient.mk I.toIdeal))
      map_mul' := fun a b => Subtype.ext (map_mul (Ideal.Quotient.mk I.toIdeal) (a : A) (b : A))
      map_zero' := Subtype.ext (map_zero (Ideal.Quotient.mk I.toIdeal))
      map_add' := fun a b => Subtype.ext (map_add (Ideal.Quotient.mk I.toIdeal) (a : A) (b : A)) }

/-- Every actual degree-zero quotient element lifts to the original homogeneous degree zero. -/
theorem s2_homogeneousQuotientZeroMap_surjective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) :
    Function.Surjective (s2_homogeneousQuotientZeroMap 𝒜 I) := by
  intro a
  obtain ⟨b, hb, h⟩ := a.property
  exact ⟨⟨b, hb⟩, Subtype.ext h⟩

/-- The actual degree-zero quotient map is bijective when the original degree zero is a field and the quotient ring is nontrivial. -/
theorem s2_homogeneousQuotientZeroMap_bijective {A K : Type} [CommRing A] [Field K]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    [Nontrivial (A ⧸ I.toIdeal)] (e : 𝒜 0 ≃+* K) :
    Function.Bijective (s2_homogeneousQuotientZeroMap 𝒜 I) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  let B := s2_homogeneousQuotientPiece 𝒜 I 0
  haveI : Nontrivial B := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  let f := (s2_homogeneousQuotientZeroMap 𝒜 I).comp e.symm.toRingHom
  have hf : Function.Injective f := f.injective
  refine ⟨?_, s2_homogeneousQuotientZeroMap_surjective 𝒜 I⟩
  intro a b hab
  apply e.injective
  apply hf
  change (s2_homogeneousQuotientZeroMap 𝒜 I) (e.symm (e a)) =
    (s2_homogeneousQuotientZeroMap 𝒜 I) (e.symm (e b))
  simpa only [RingEquiv.symm_apply_apply] using hab

end HodgeLean.Foundations.Program
