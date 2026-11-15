import HodgeLean.Adapters.NormalConeB4aGysinLocalModel
import HodgeLean.Adapters.NormalConeB4aGysinEtaleQuotientLength

/-! # Exact parameter lengths in local finite comparison fibres -/

noncomputable section
namespace HodgeLean.Adapters

/-- The length of a local finite fibre is the exact parameter-ideal quotient
length in the source localization at its point. -/
theorem a3b4a_gysin_local_fibre_length_eq_source_quotient
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [IsLocalRing (p.Fiber S)]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    let r := q.comap Algebra.TensorProduct.includeRight.toRingHom
    let L := Localization.AtPrime r
    Module.length (p.Fiber S) (p.Fiber S) =
      Module.length (L ⧸ p.map (algebraMap R L)) (L ⧸ p.map (algebraMap R L)) := by
  have hq : q = IsLocalRing.maximalIdeal (p.Fiber S) :=
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime q)
  have hu : q.primeCompl ≤ IsUnit.submonoid (p.Fiber S) := by
    intro x hx
    apply IsLocalRing.notMem_maximalIdeal.mp
    rw [← hq]
    exact hx
  let e := (IsLocalization.atUnits (S := Localization.AtPrime q)
    (p.Fiber S) q.primeCompl hu).toRingEquiv.trans
      (Ideal.Fiber.algEquivAux₂ p q).toRingEquiv
  have hlen := a3b2_length_eq_of_ringEquiv e
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hlen
  exact hlen

/-- Étale source changes preserve every ideal-quotient length at corresponding
localizations, measured over the quotient rings themselves. -/
theorem a3b4a_gysin_etale_localization_quotient_length
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (I : Ideal A) :
    Module.length
      (Localization.AtPrime q ⧸ I.map (algebraMap A (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ I.map (algebraMap A (Localization.AtPrime q))) =
    Module.length
      (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p)))
      (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyEtale.localization_base p.primeCompl
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp A _ _
  have hlen := a3b4a_gysin_quotient_length_eq_of_flat_unramified
    (B := Localization.AtPrime q) (I.map (algebraMap A (Localization.AtPrime p)))
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hlen
  exact hlen

/-- At a prime of an étale base change, the original base prime and the new
base prime generate the same ideal of the localized base. -/
theorem a3b4a_gysin_etale_base_prime_ideal
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    p.map (algebraMap A (Localization.AtPrime q)) =
      q.map (algebraMap B (Localization.AtPrime q)) := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact ((Algebra.isUnramifiedAt_iff_map_eq A p q).mp inferInstance).2

set_option backward.isDefEq.respectTransparency.types false in
/-- In a commuting étale change of base and source, the local finite model's
fibre length is the original source's exact localized parameter-quotient length. -/
theorem a3b4a_gysin_etale_model_fibre_length
    {A B S T : Type*} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
    [Algebra A B] [Algebra A S] [Algebra A T] [Algebra B T] [Algebra S T]
    [IsScalarTower A B T] [IsScalarTower A S T]
    [Algebra.Etale A B] [Algebra.Etale S T] [Module.Finite B T]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [IsLocalRing (P.Fiber T)] (Q : Ideal (P.Fiber T)) [Q.IsPrime] :
    let r := Q.comap Algebra.TensorProduct.includeRight.toRingHom
    let q := r.under S
    let L := Localization.AtPrime q
    Module.length (P.Fiber T) (P.Fiber T) =
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
  have hfibre := a3b4a_gysin_local_fibre_length_eq_source_quotient P Q
  change Module.length (P.Fiber T) (P.Fiber T) =
    Module.length (Localization.AtPrime r ⧸ P.map (algebraMap B (Localization.AtPrime r)))
      (Localization.AtPrime r ⧸ P.map (algebraMap B (Localization.AtPrime r))) at hfibre
  rw [← hid] at hfibre
  exact hfibre.trans hsource

end HodgeLean.Adapters
