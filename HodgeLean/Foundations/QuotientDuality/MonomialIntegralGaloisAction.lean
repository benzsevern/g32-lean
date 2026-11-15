import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! Restriction of field automorphisms to a normal integral covering algebra. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem integral_cover_galois_action
    {R K A F : Type*} [CommRing R] [Field K] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F]
    [Algebra R K] [Algebra K F] [Algebra R F] [IsScalarTower R K F]
    [Algebra R A] [Algebra A F] [IsScalarTower R A F] [IsFractionRing A F]
    [Algebra.IsIntegral R A] :
    ∃ ρ : (F ≃ₐ[K] F) →* (A ≃ₐ[R] A),
      ∀ g a, algebraMap A F (ρ g a) = g (algebraMap A F a) := by
  letI : IsIntegralClosure A R F := IsIntegralClosure.of_isIntegrallyClosed A R F
  let r (g : F ≃ₐ[K] F) : A ≃ₐ[R] A :=
    AlgEquiv.ofAlgHom (galRestrict' R A A g.toAlgHom)
      (galRestrict' R A A g.symm.toAlgHom)
      (by rw [← galRestrict'_comp]; simp)
      (by rw [← galRestrict'_comp]; simp)
  have hr (g : F ≃ₐ[K] F) (a : A) :
      algebraMap A F (r g a) = g (algebraMap A F a) :=
    algebraMap_galRestrict'_apply R A A g.toAlgHom a
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, hr⟩
  · ext a
    apply IsFractionRing.injective A F
    exact hr 1 a
  · intro g h
    ext a
    apply IsFractionRing.injective A F
    change algebraMap A F (r (g * h) a) = algebraMap A F (r g (r h a))
    rw [hr, hr, hr]
    rfl

#print axioms integral_cover_galois_action
end HodgeLean.Foundations.QuotientDuality
