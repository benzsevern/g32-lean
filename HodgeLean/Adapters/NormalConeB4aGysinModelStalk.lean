import HodgeLean.Adapters.NormalConeB4aGysinLocalModelLength

/-! # Termwise exact source lengths in comparison fibres -/

noncomputable section
namespace HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency.types false in
/-- Every local ring of a comparison fibre has the original source's exact
localized parameter-quotient length, without requiring that fibre to be local. -/
theorem a3b4a_gysin_etale_model_stalk_length
    {A B S T : Type*} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
    [Algebra A B] [Algebra A S] [Algebra A T] [Algebra B T] [Algebra S T]
    [IsScalarTower A B T] [IsScalarTower A S T]
    [Algebra.Etale A B] [Algebra.Etale S T]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal (P.Fiber T)) [Q.IsPrime] :
    let r := Q.comap Algebra.TensorProduct.includeRight.toRingHom
    let q := r.under S
    let L := Localization.AtPrime q
    Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
      Module.length (L ⧸ p.map (algebraMap A L)) (L ⧸ p.map (algebraMap A L)) := by
  let r : Ideal T := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  let q := r.under S
  have : r.LiesOver P := by
    change (Q.comap (Algebra.TensorProduct.includeRight : T →ₐ[B] P.Fiber T)).LiesOver P
    infer_instance
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver P r
  have : IsScalarTower A (Localization.AtPrime P) (Localization.AtPrime r) :=
    IsScalarTower.to₁₃₄ A B (Localization.AtPrime P) (Localization.AtPrime r)
  have hid := congrArg (Ideal.map
    (algebraMap (Localization.AtPrime P) (Localization.AtPrime r)))
      (a3b4a_gysin_etale_base_prime_ideal p P)
  simp_rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hid
  have hsource := a3b4a_gysin_etale_localization_quotient_length q r
    (p.map (algebraMap A S))
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hsource
  have hfibre := a3b2_length_eq_of_ringEquiv
    (Ideal.Fiber.algEquivAux₂ P Q).toRingEquiv
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hfibre
  change Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
    Module.length (Localization.AtPrime r ⧸ P.map (algebraMap B (Localization.AtPrime r)))
      (Localization.AtPrime r ⧸ P.map (algebraMap B (Localization.AtPrime r))) at hfibre
  rw [← hid] at hfibre
  exact hfibre.trans hsource

end HodgeLean.Adapters
