import HodgeLean.Foundations.Program.SchoenCycleMappedCotangentEquiv
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Local algebra coordinates identify the actual maximal-ideal cotangent modules over the prescribed scalar field.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
def s2e_local_algebra_cotangent_equiv
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsLocalRing A] [IsLocalRing B] (e : A ≃ₐ[k] B) :
    (IsLocalRing.maximalIdeal A).Cotangent ≃ₗ[k] (IsLocalRing.maximalIdeal B).Cotangent := by
  let I := IsLocalRing.maximalIdeal A
  have h : I.map e.toRingHom = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  exact (s2e_mapped_ideal_cotangent_equiv I e).trans
    ((Ideal.Cotangent.equivOfEq _ _ h).restrictScalars k)

#print axioms s2e_local_algebra_cotangent_equiv

/-- Actual local cotangent coordinates send each represented class to the class of its actual algebra image.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_local_algebra_cotangent_toCotangent
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃ₐ[k] B) (x : IsLocalRing.maximalIdeal A) :
    ∃ hx : e x.val ∈ IsLocalRing.maximalIdeal B,
      s2e_local_algebra_cotangent_equiv e ((IsLocalRing.maximalIdeal A).toCotangent x) =
        (IsLocalRing.maximalIdeal B).toCotangent ⟨e x.val, hx⟩ := by
  have hx : e x.val ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv]
    exact Ideal.mem_map_of_mem e.toRingHom x.property
  refine ⟨hx, ?_⟩
  rfl

#print axioms s2e_local_algebra_cotangent_toCotangent
end HodgeLean.Foundations.Program
