import HodgeLean.Adapters.NormalConeB4aGysinEtaleRegularOpen

noncomputable section
namespace HodgeLean.Adapters
open scoped TensorProduct

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Regular parameters at a quasi-finite source point construct a finite
flat étale comparison model with the original exact parameter quotient length. -/
theorem a3b4a_gysin_exists_exact_model_of_regular_parameters
    {A S : Type} [CommRing A] [IsNoetherianRing A] [CommRing S] [Algebra A S]
    [Algebra.FiniteType A S]
    (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt A q]
    (xs : List A) (hspan : Ideal.ofList xs = p)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime q)
      (xs.map (algebraMap A (Localization.AtPrime q)))) :
    ∃ (B T : Type) (_ : CommRing B) (_ : CommRing T)
      (_ : Algebra A B) (_ : Algebra A T) (_ : Algebra B T) (_ : Algebra S T)
      (_ : IsScalarTower A B T) (_ : IsScalarTower A S T)
      (_ : Algebra.Etale A B) (_ : Algebra.Etale S T)
      (_ : Module.Finite B T) (_ : Module.Flat B T)
      (P : Ideal B) (_ : P.IsPrime) (_ : P.LiesOver p)
      (_ : IsLocalRing (P.Fiber T)) (r : Ideal T) (_ : r.IsPrime) (_ : r.LiesOver P),
      r.under S = q ∧
      Module.length (P.Fiber T) (P.Fiber T) =
        Module.length (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q)))
          (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
  obtain ⟨B₀, _, _, _, P₀, _, _, e₀, he₀, Q₀, _, _, hQ₀, heQ₀, _, hfin₀, huniq₀⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let D := TensorProduct A B₀ S
  let T₀ := Localization.Away e₀
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.Etale S D :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight A S B₀)
  haveI : Module.Finite B₀ T₀ := hfin₀
  haveI : IsLocalRing (P₀.Fiber T₀) :=
    a3b4a_gysin_localized_fibre_local P₀ Q₀ e₀ heQ₀ huniq₀
  have hd₀ : Disjoint (Submonoid.powers e₀ : Set D) Q₀ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime e₀).mpr heQ₀
  let r₀ := Q₀.map (algebraMap D T₀)
  haveI : r₀.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers e₀) T₀ Q₀ inferInstance hd₀
  haveI : r₀.LiesOver Q₀ := IsLocalization.liesOver_map_of_isPrime_disjoint
    (Submonoid.powers e₀) T₀ hd₀
  haveI : r₀.LiesOver P₀ := Ideal.LiesOver.trans r₀ Q₀ P₀
  have hr₀ : r₀.under S = q := by
    rw [← Ideal.under_under (A := S) (B := D), ← r₀.over_def Q₀]
    exact hQ₀
  haveI : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing A B₀
  haveI : Algebra.Etale S T₀ := inferInstance
  obtain ⟨f, hf, hfree⟩ := a3b4a_gysin_etale_model_free_neighborhood p P₀ r₀ xs hspan (by
    have htransport (q' : Ideal S) [q'.IsPrime] (heq : q' = q) :
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime q')
          (xs.map (algebraMap A (Localization.AtPrime q'))) := by
      subst q'
      exact hreg
    exact htransport _ hr₀)
  let B := Localization.Away f
  let M := Algebra.algebraMapSubmonoid T₀ (Submonoid.powers f)
  let T := Localization M
  letI := hfree
  haveI : IsLocalization.Away (algebraMap B₀ T₀ f) T := by
    change IsLocalization (Submonoid.powers (algebraMap B₀ T₀ f)) T
    rw [← Algebra.algebraMapSubmonoid_powers]
    exact (inferInstance : IsLocalization M T)
  haveI : Algebra.Etale T₀ T := Algebra.Etale.of_isLocalizationAway (algebraMap B₀ T₀ f)
  haveI : Algebra.Etale S T := Algebra.Etale.comp S T₀ T
  haveI : Algebra.Etale A B := inferInstance
  haveI : IsScalarTower A B T := IsScalarTower.to₁₃₄ A B₀ B T
  haveI : Module.Finite B T := Module.Finite.of_isLocalization B₀ T₀ (Submonoid.powers f)
  let eM := (IsLocalizedModule.iso (Submonoid.powers f)
    (IsScalarTower.toAlgHom B₀ T₀ T).toLinearMap).extendScalarsOfIsLocalization
      (Submonoid.powers f) B
  haveI : Module.Free B T := Module.Free.of_equiv eM
  haveI : Module.Flat B T := inferInstance
  have hdP : Disjoint (Submonoid.powers f : Set B₀) P₀ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let P := P₀.map (algebraMap B₀ B)
  haveI : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) B P₀ inferInstance hdP
  haveI : P.LiesOver P₀ := IsLocalization.liesOver_map_of_isPrime_disjoint
    (Submonoid.powers f) B hdP
  haveI : P.LiesOver p := Ideal.LiesOver.trans P P₀ p
  have hdf : Disjoint (M : Set T₀) r₀ := by
    rw [show M = Submonoid.powers (algebraMap B₀ T₀ f) from
      Algebra.algebraMapSubmonoid_powers f]
    apply (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr
    exact fun hs => hf ((r₀.mem_of_liesOver P₀ f).mpr hs)
  let r := r₀.map (algebraMap T₀ T)
  haveI : r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T r₀ inferInstance hdf
  haveI : r.LiesOver r₀ := IsLocalization.liesOver_map_of_isPrime_disjoint M T hdf
  have hrB₀ : r.under B₀ = P₀ := by
    rw [← Ideal.under_under (A := B₀) (B := T₀), ← r.over_def r₀, ← r₀.over_def P₀]
  have hPunder : P = r.under B := by
    calc
      P = ((r.under B).under B₀).map (algebraMap B₀ B) := by
        rw [Ideal.under_under, hrB₀]
      _ = r.under B := IsLocalization.map_under (Submonoid.powers f) B (r.under B)
  haveI : r.LiesOver P := ⟨hPunder⟩
  have hr : r.under S = q := by
    rw [← Ideal.under_under (A := S) (B := T₀), ← r.over_def r₀, hr₀]
  have hlocal : IsLocalRing (P.Fiber T) := by
    apply a3b4a_gysin_fibre_local_of_unique_prime P r
    intro J hJ hJP
    letI := hJ
    letI := hJP
    have hJunder : (J.under T₀).LiesOver P₀ := ⟨by
      rw [Ideal.under_under, ← Ideal.under_under (A := B₀) (B := B),
        ← J.over_def P, ← P.over_def P₀]⟩
    letI := hJunder
    have heq : J.under T₀ = r₀ := a3b4a_gysin_unique_prime_over_local_fibre P₀ _ r₀
    calc
      J = (J.under T₀).map (algebraMap T₀ T) := (IsLocalization.map_under M T J).symm
      _ = r := congrArg (Ideal.map (algebraMap T₀ T)) heq
  letI := hlocal
  let Q := (PrimeSpectrum.primesOverOrderIsoFiber B T P) (Ideal.primesOver.mk P r)
  have hQr : Q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = r :=
    congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber B T P).symm_apply_apply
      (Ideal.primesOver.mk P r))
  have hlength := a3b4a_gysin_etale_model_fibre_length (S := S) p P Q.asIdeal
  have hparam_length (q' : Ideal S) [q'.IsPrime] (heq : q' = q) :
      Module.length (Localization.AtPrime q' ⧸ p.map (algebraMap A (Localization.AtPrime q')))
        (Localization.AtPrime q' ⧸ p.map (algebraMap A (Localization.AtPrime q'))) =
      Module.length (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q)))
        (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
    subst q'
    rfl
  have hlength' := hlength.trans
    (hparam_length _ ((congrArg (Ideal.under S) hQr).trans hr))
  exact ⟨B, T, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, P, inferInstance, inferInstance,
    hlocal, r, inferInstance, inferInstance, hr, hlength'⟩

end HodgeLean.Adapters
