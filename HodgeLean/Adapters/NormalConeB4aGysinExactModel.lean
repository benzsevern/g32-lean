import HodgeLean.Adapters.NormalConeB4aGysinLocalModelLength
import HodgeLean.Adapters.NormalConeB4aGysinLengthNeighborhood

/-! # Constructed finite local models with exact source parameter length -/

noncomputable section
namespace HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency.types false in
/-- A quasi-finite point in a flat family has an étale finite flat comparison
model whose local special fibre has exactly the original parameter-quotient length. -/
theorem a3b4a_gysin_exists_exact_local_model
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
      (∃ Q : Ideal (TensorProduct R R' S), Q.IsPrime ∧ Q.LiesOver P ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ Q) ∧
      Module.length (P.Fiber (Localization.Away e)) (P.Fiber (Localization.Away e)) =
        Module.length
          (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
          (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
  obtain ⟨R', _, _, _, P, _, _, e, he, hfin, hflat, hlocal, hres,
    Q, hQprime, hQover, hQ, heQ⟩ :=
    a3b4a_gysin_exists_finite_flat_local_fibre_model p q
  have : Q.IsPrime := hQprime
  have : Q.LiesOver P := hQover
  let C := TensorProduct R R' S
  let T := Localization.Away e
  letI : Algebra S C := Algebra.TensorProduct.rightAlgebra
  have : Algebra.Etale S C :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight R S R')
  have : Module.Finite R' T := hfin
  have : IsLocalRing (P.Fiber T) := hlocal
  have hd : Disjoint (Submonoid.powers e : Set C) Q := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let r := Q.map (algebraMap C T)
  have : r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers e) T Q inferInstance hd
  have : r.LiesOver Q := IsLocalization.liesOver_map_of_isPrime_disjoint
    (Submonoid.powers e) T hd
  have : r.LiesOver P := Ideal.LiesOver.trans r Q P
  let F := (PrimeSpectrum.primesOverOrderIsoFiber R' T P) (Ideal.primesOver.mk P r)
  have hr : F.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = r := by
    exact congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber R' T P).symm_apply_apply
      (Ideal.primesOver.mk P r))
  have hcontract : r.under C = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers e) T hQprime hd
  have hsource : (F.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom).under S = q := by
    rw [hr]
    calc
      r.under S = (r.under C).under S := (Ideal.under_under (A := S) (B := C) r).symm
      _ = Q.under S := congrArg (Ideal.under S) hcontract
      _ = q := hQ
  have hpoint : ∃ Q : Ideal C, Q.IsPrime ∧ Q.LiesOver P ∧
      Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ Q :=
    ⟨Q, hQprime, hQover, hQ, heQ⟩
  clear hQ
  subst q
  have hlen := a3b4a_gysin_etale_model_fibre_length
    (A := R) (B := R') (S := S) (T := T) p P F.asIdeal
  exact ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance,
    inferInstance, e, he, hfin, hflat, hlocal, hres,
    hpoint, hlen⟩

/-- A flat family near a quasi-finite point has a finite comparison neighborhood
whose fibre-length sums equal the exact parameter length at that source point. -/
theorem a3b4a_gysin_exists_exact_length_neighborhood
    {R S : Type} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : TensorProduct R R' S), IsIdempotentElem e ∧
      Module.Finite R' (Localization.Away e) ∧
      Module.Flat R' (Localization.Away e) ∧
      (∃ Q : Ideal (TensorProduct R R' S), Q.IsPrime ∧ Q.LiesOver P ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ Q) ∧
      ∃ U : Set (PrimeSpectrum R'), IsOpen U ∧ ⟨P, inferInstance⟩ ∈ U ∧
        ∀ (b : PrimeSpectrum R'), b ∈ U → ∀ [IsAlgClosed b.asIdeal.ResidueField],
          Module.length
            (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
            (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) =
          ∑ᶠ x : PrimeSpectrum (b.asIdeal.Fiber (Localization.Away e)),
            Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal) := by
  obtain ⟨R', _, _, _, P, _, _, e, he, hfin, hflat, hlocal, hres, hpoint, hlen⟩ :=
    a3b4a_gysin_exists_exact_local_model p q
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have : Module.Finite R' (Localization.Away e) := hfin
  have : Module.Flat R' (Localization.Away e) := hflat
  have : IsLocalRing (P.Fiber (Localization.Away e)) := hlocal
  have : IsAlgClosed P.ResidueField := IsAlgClosed.of_ringEquiv p.ResidueField P.ResidueField
    (AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p))
      hres).toRingEquiv
  have : Module.FinitePresentation R' (Localization.Away e) :=
    Module.finitePresentation_of_finite R' (Localization.Away e)
  obtain ⟨U, hU, hPU, hsum⟩ := a3b4a_gysin_local_fibre_length_eq_sum_nearby
    (A := Localization.Away e) (⟨P, inferInstance⟩ : PrimeSpectrum R')
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance,
    inferInstance, e, he, hfin, hflat, hpoint, U, hU, hPU, ?_⟩
  intro b hb _
  exact hlen.symm.trans (hsum b hb)

end HodgeLean.Adapters
