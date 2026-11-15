import HodgeLean.Adapters.NormalConeB4aGysinFiniteFlatLength
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Flat.Localization

/-! # Finite comparison models with a local special fibre -/

noncomputable section
namespace HodgeLean.Adapters

/-- A fibre of a finite algebra is local when precisely one prime of the
algebra lies over the chosen base prime. -/
theorem a3b4a_gysin_fibre_local_of_unique_prime
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hunique : ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver p → q' = q) :
    IsLocalRing (p.Fiber S) := by
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
  let Q := e (Ideal.primesOver.mk p q)
  have hQ : Q.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime Q.asIdeal
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨Q.asIdeal, hQ, fun J hJ => ?_⟩
  have hprime : J.IsPrime := hJ.isPrime
  let J' := e.symm ⟨J, hprime⟩
  have hJ' : J' = Ideal.primesOver.mk p q := by
    apply Subtype.ext
    exact hunique J'.1 J'.2.1 J'.2.2
  have heq := congrArg e hJ'
  simpa [J', Q] using congrArg PrimeSpectrum.asIdeal heq

/-- Isolating one prime by a principal open gives a local special fibre in
the finite algebra on that open. -/
theorem a3b4a_gysin_localized_fibre_local
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (s : S) (hs : s ∉ q) [Module.Finite R (Localization.Away s)]
    (hunique : ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver p → s ∉ q' → q' = q) :
    IsLocalRing (p.Fiber (Localization.Away s)) := by
  let T := Localization.Away s
  have hd : Disjoint (Submonoid.powers s : Set S) q := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let Q := q.map (algebraMap S T)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers s) T q inferInstance hd
  have : Q.LiesOver q := IsLocalization.liesOver_map_of_isPrime_disjoint
    (Submonoid.powers s) T hd
  have : Q.LiesOver p := Ideal.LiesOver.trans Q q p
  apply a3b4a_gysin_fibre_local_of_unique_prime p Q
  intro J hJ hJp
  have hunder : J.under S = q := hunique (J.under S) inferInstance inferInstance
    (J.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit s))
  calc
    J = (J.under S).map (algebraMap S T) :=
      (IsLocalization.map_under (Submonoid.powers s) T J).symm
    _ = Q := congrArg (Ideal.map (algebraMap S T)) hunder

/-- An étale base change isolates a finite flat factor with local special fibre,
preserving the base residue field and a point over the original source prime.
Source: Mathlib `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`. -/
theorem a3b4a_gysin_exists_finite_flat_local_fibre_model
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : TensorProduct R R' S), IsIdempotentElem e ∧
      Module.Finite R' (Localization.Away e) ∧
      Module.Flat R' (Localization.Away e) ∧
      IsLocalRing (P.Fiber (Localization.Away e)) ∧
      Function.Bijective
        (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      ∃ Q : Ideal (TensorProduct R R' S), Q.IsPrime ∧ Q.LiesOver P ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ Q := by
  obtain ⟨R', _, _, _, P, _, _, e, he, Q, _, _, hQ, heQ, hres, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  have : Module.Finite R' (Localization.Away e) := hfin
  have hlocal : IsLocalRing (P.Fiber (Localization.Away e)) :=
    a3b4a_gysin_localized_fibre_local P Q e heQ huniq
  exact ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance,
    inferInstance, e, he, hfin, inferInstance, hlocal, hres, Q, inferInstance,
    inferInstance, hQ, heQ⟩

end HodgeLean.Adapters
