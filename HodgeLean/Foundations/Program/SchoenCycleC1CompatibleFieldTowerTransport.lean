import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.PowerBasis

noncomputable section
namespace HodgeLean.Foundations.Program

/-- A ring identification compatible with the original base map transports
the intermediate field action while retaining the original base algebra. -/
theorem s2e_c1_compatible_field_tower_transport
    {R A K L : Type*} [CommRing R] [CommRing A] [Field K] [Field L]
    [Algebra R A] [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    (E : A ≃+* L) (hE : ∀ r, E (algebraMap R A r) = algebraMap R L r) :
    ∃ hKA : Algebra K A,
      letI := hKA
      IsScalarTower R K A ∧ ∃ e : A ≃ₐ[K] L, e.toRingEquiv = E := by
  letI : Algebra K A := (E.symm.toRingHom.comp (algebraMap K L)).toAlgebra
  have ht : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq fun r => by
    apply E.injective
    change E (algebraMap R A r) = E (E.symm (algebraMap K L (algebraMap R K r)))
    rw [hE, E.apply_symm_apply, IsScalarTower.algebraMap_apply R K L]
  let e : A ≃ₐ[K] L := { E with
    commutes' := fun k => by
      change E (E.symm (algebraMap K L k)) = algebraMap K L k
      exact E.apply_symm_apply _ }
  exact ⟨inferInstance, ht, e, rfl⟩

end HodgeLean.Foundations.Program
