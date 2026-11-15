import HodgeLean.Adapters.NormalConeB4aGysinDedekindSpread
import HodgeLean.Adapters.NormalConeB4aGysinAffinePoint
import HodgeLean.Adapters.NormalConeB4aGysinExactModel

/-! # Exact finite comparison models over affine Dedekind bases -/

noncomputable section
namespace HodgeLean.Adapters

/-- A flat quasi-finite stalk has a finite type flat principal neighborhood
and a corresponding quasi-finite point preserving every base-ideal quotient length. -/
theorem a3b4a_gysin_exists_dedekind_quasiFinite_neighborhood
    {D R : Type*} [CommRing D] [IsDomain D] [IsDedekindDomain D]
    [CommRing R] [IsNoetherianRing R] [Algebra D R] [Algebra.FiniteType D R]
    (q : Ideal R) [q.IsPrime]
    [Module.Flat D (Localization.AtPrime q)] [Algebra.QuasiFiniteAt D q] :
    ∃ f : R, f ∉ q ∧ Algebra.FiniteType D (Localization.Away f) ∧
      Module.Flat D (Localization.Away f) ∧
      ∃ r : Ideal (Localization.Away f), ∃ hr : r.IsPrime, letI := hr
        r.LiesOver q ∧ Algebra.QuasiFiniteAt D r ∧
        ∀ I : Ideal D,
          Module.length (Localization.AtPrime r ⧸ I.map (algebraMap D (Localization.AtPrime r)))
            (Localization.AtPrime r ⧸ I.map (algebraMap D (Localization.AtPrime r))) =
          Module.length (Localization.AtPrime q ⧸ I.map (algebraMap D (Localization.AtPrime q)))
            (Localization.AtPrime q ⧸ I.map (algebraMap D (Localization.AtPrime q))) := by
  obtain ⟨f, hf, hflat⟩ := a3b4a_gysin_exists_dedekind_flat_neighborhood (D := D) q
  let S := Localization.Away f
  have hfin : Algebra.FiniteType D S :=
    (inferInstance : Algebra.FiniteType D R).trans (inferInstance : Algebra.FiniteType R S)
  have hd : Disjoint (Submonoid.powers f : Set R) q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let r := q.map (algebraMap R S)
  have hr : r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) S q inferInstance hd
  letI := hr
  have hover : r.LiesOver q := IsLocalization.liesOver_map_of_isPrime_disjoint
    (Submonoid.powers f) S hd
  have hqf : Algebra.QuasiFiniteAt D r :=
    Algebra.QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver q
      (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers f) S) r
  refine ⟨f, hf, hfin, hflat, r, hr, hover, hqf, ?_⟩
  intro I
  have hlen := a3b4a_gysin_etale_localization_quotient_length q r (I.map (algebraMap D R))
  rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq] at hlen
  exact hlen

/-- A quasi-finite point with stalkwise flatness over a Dedekind base has a constructed
finite flat comparison model retaining the original parameter-quotient length. -/
theorem a3b4a_gysin_exists_exact_model_over_dedekind_base
    {D R : Type} [CommRing D] [IsDomain D] [IsDedekindDomain D]
    [CommRing R] [IsNoetherianRing R] [Algebra D R] [Algebra.FiniteType D R]
    (p : Ideal D) [p.IsPrime]
    (q : Ideal R) [q.IsPrime] [q.LiesOver p]
    [Module.Flat D (Localization.AtPrime q)] [Algebra.QuasiFiniteAt D q] :
    ∃ f : R, f ∉ q ∧
      ∃ (D' : Type) (_ : CommRing D') (_ : Algebra D D') (_ : Algebra.Etale D D')
        (P : Ideal D') (_ : P.IsPrime) (_ : P.LiesOver p)
        (e : TensorProduct D D' (Localization.Away f)), IsIdempotentElem e ∧
        Module.Finite D' (Localization.Away e) ∧
        Module.Flat D' (Localization.Away e) ∧
        IsLocalRing (P.Fiber (Localization.Away e)) ∧
        Function.Bijective
          (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
        (∃ Q : Ideal (TensorProduct D D' (Localization.Away f)), Q.IsPrime ∧ Q.LiesOver P ∧
          (Q.comap Algebra.TensorProduct.includeRight.toRingHom).comap
            (algebraMap R (Localization.Away f)) = q ∧ e ∉ Q) ∧
        Module.length (P.Fiber (Localization.Away e)) (P.Fiber (Localization.Away e)) =
          Module.length
            (Localization.AtPrime q ⧸ p.map (algebraMap D (Localization.AtPrime q)))
            (Localization.AtPrime q ⧸ p.map (algebraMap D (Localization.AtPrime q))) := by
  obtain ⟨f, hf, hfinS, hflatS, r, hr, hover, hqf, hlength⟩ :=
    a3b4a_gysin_exists_dedekind_quasiFinite_neighborhood (D := D) q
  let S := Localization.Away f
  letI : Algebra.FiniteType D S := hfinS
  letI : Module.Flat D S := hflatS
  letI := hr
  letI : r.LiesOver q := hover
  letI : Algebra.QuasiFiniteAt D r := hqf
  have : r.LiesOver p := Ideal.LiesOver.trans r q p
  obtain ⟨D', _, _, _, P, _, _, e, he, hfin, hflat, hlocal, hres, hpoint, hlen⟩ :=
    a3b4a_gysin_exists_exact_local_model p r
  refine ⟨f, hf, D', inferInstance, inferInstance, inferInstance, P,
    inferInstance, inferInstance, e, he, hfin, hflat, hlocal, hres, ?_,
    hlen.trans (hlength p)⟩
  obtain ⟨Q, hQprime, hQover, hQeq, heQ⟩ := hpoint
  refine ⟨Q, hQprime, hQover, ?_, heQ⟩
  rw [hQeq]
  exact (r.over_def q).symm

end HodgeLean.Adapters
