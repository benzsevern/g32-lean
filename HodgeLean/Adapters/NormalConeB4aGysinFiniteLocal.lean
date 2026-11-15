import HodgeLean.Adapters.NormalConeB4aGysinLocalModel
import Mathlib.RingTheory.Ideal.GoingUp

noncomputable section
namespace HodgeLean.Adapters

/-- A finite algebra over a local ring is local if its special fibre is local. -/
theorem a3b4a_gysin_finite_local_of_local_fibre
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [IsLocalRing ((IsLocalRing.maximalIdeal R).Fiber S)] : IsLocalRing S := by
  let m := IsLocalRing.maximalIdeal R
  let F := m.Fiber S
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S m
  let q := e.symm ⟨IsLocalRing.maximalIdeal F, inferInstance⟩
  have hq : q.1.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q.1 (by
      rw [← q.1.over_def m]
      infer_instance)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨q.1, hq, ?_⟩
  intro J hJ
  letI := hJ
  have hJm : J.under R = m := IsLocalRing.eq_maximalIdeal inferInstance
  letI : J.LiesOver m := ⟨hJm.symm⟩
  let j := Ideal.primesOver.mk m J
  have heq : e j = (⟨IsLocalRing.maximalIdeal F, inferInstance⟩ : PrimeSpectrum F) := by
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal
      (IsArtinianRing.isMaximal_of_isPrime (e j).asIdeal)
  have hj : j = q := e.injective (heq.trans (e.apply_symm_apply _).symm)
  exact congrArg Subtype.val hj

/-- A finite algebra over a local base is local when its quotient by the
extended maximal ideal is local. -/
theorem a3b4a_gysin_finite_local_of_local_parameter_quotient
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [IsLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))] :
    IsLocalRing S := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let f := Ideal.Quotient.mk I
  let q := IsLocalRing.maximalIdeal (S ⧸ I)
  have hq : (q.comap f).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective f Ideal.Quotient.mk_surjective
  letI : Nontrivial S := f.domain_nontrivial
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨q.comap f, hq, ?_⟩
  intro J hJ
  letI := hJ
  have hJI : I ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact le_of_eq (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) J)).symm
  have hker : RingHom.ker f ≤ J := by
    change RingHom.ker (Ideal.Quotient.mk I) ≤ J
    rwa [Ideal.mk_ker]
  have hJmap : (J.map f).IsMaximal :=
    hJ.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  have hJq : J.map f = q := IsLocalRing.eq_maximalIdeal hJmap
  calc
    J = (J.map f).comap f := by
      rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    _ = q.comap f := congrArg (Ideal.comap f) hJq

end HodgeLean.Adapters
