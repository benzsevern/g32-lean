import HodgeLean.Adapters.NormalConeB4aGysinFibreEvaluation
import HodgeLean.Adapters.NormalConeB4aGysinModelStalk

noncomputable section
namespace HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency.types false in
/-- The local length at a prime of a fibre is the parameter quotient
length at its source prime, measured over the source local ring. -/
theorem a3b4a_gysin_fibre_prime_parameter_length
    {B T : Type*} [CommRing B] [CommRing T] [Algebra B T]
    (p : Ideal B) [p.IsPrime] (Q : Ideal (p.Fiber T)) [Q.IsPrime] :
    let r := Q.comap Algebra.TensorProduct.includeRight.toRingHom
    let L := Localization.AtPrime r
    Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
      Module.length L (L ⧸ p.map (algebraMap B L)) := by
  have h := a3b2_length_eq_of_ringEquiv (Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  let r := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  let L := Localization.AtPrime r
  change Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
    Module.length (L ⧸ p.map (algebraMap B L)) (L ⧸ p.map (algebraMap B L)) at h
  exact h.trans (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end HodgeLean.Adapters
