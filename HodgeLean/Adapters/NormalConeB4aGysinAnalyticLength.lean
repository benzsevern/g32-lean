import HodgeLean.Adapters.NormalConeB4aGysinAnalyticParameter

/-! # Exact finite fibre lengths along analytic parameter lifts -/

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry ComplexAlgHom

/-- Around a rational point of an étale comparison base, analytic parameter
lifts conserve the exact local fibre length as the sum of nearby local lengths. -/
theorem a3b4a_gysin_exists_analytic_length_neighborhood
    {n : ℕ} (T A : Type) [CommRing T] [Algebra ℂ T]
    [Algebra (complexPolynomialRing n) T]
    [IsScalarTower ℂ (complexPolynomialRing n) T]
    [Algebra.Etale (complexPolynomialRing n) T]
    [CommRing A] [Algebra T A] [Module.FinitePresentation T A] [Module.Flat T A]
    (u : T →ₐ[ℂ] ℂ) (p : Ideal T) [p.IsPrime] (hu : RingHom.ker u = p)
    [IsLocalRing (p.Fiber A)] :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧
      mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) ∈ U ∧
      ∃ F : (Fin n → ℂ) → (T →ₐ[ℂ] ℂ), ContinuousOn F U ∧
        F (mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u)) = u ∧
        (∀ z ∈ U, etaleBaseAlgHom T (F z) = (mvPolynomialAlgHomHomeomorph n).symm z) ∧
        (∀ r : T, AnalyticOnNhd ℂ (fun z => F z r) U) ∧
        ∀ z ∈ U, letI : (RingHom.ker (F z)).IsPrime := RingHom.ker_isPrime (F z)
          Module.length (p.Fiber A) (p.Fiber A) =
            ∑ᶠ x : PrimeSpectrum ((RingHom.ker (F z)).Fiber A),
              Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal) := by
  obtain ⟨ep, _⟩ := a3b4a_gysin_exists_rational_residue_equiv p u hu
  have : IsAlgClosed p.ResidueField :=
    IsAlgClosed.of_ringEquiv ℂ p.ResidueField ep.symm.toRingEquiv
  obtain ⟨V, hV, hpV, hsum⟩ := a3b4a_gysin_local_fibre_length_eq_sum_nearby
    (A := A) (⟨p, inferInstance⟩ : PrimeSpectrum T)
  obtain ⟨U, hU, huU, F, hF, hFu, hbase, han⟩ :=
    a3b4a_gysin_exists_analytic_parameter_lift (n := n) T u
  let κ := fun w : T →ₐ[ℂ] ℂ =>
    (⟨RingHom.ker w, RingHom.ker_isPrime w⟩ : PrimeSpectrum T)
  have hκ : Continuous κ := a3b4a_gysin_continuous_evaluation_prime T
  have hκu : κ u = (⟨p, inferInstance⟩ : PrimeSpectrum T) := PrimeSpectrum.ext hu
  let W := U ∩ F ⁻¹' (κ ⁻¹' V)
  have hW : IsOpen W := hF.isOpen_inter_preimage hU (hV.preimage hκ)
  have huW : mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) ∈ W := by
    refine ⟨huU, ?_⟩
    change κ (F _) ∈ V
    rw [hFu, hκu]
    exact hpV
  refine ⟨W, hW, huW, F, hF.mono Set.inter_subset_left, hFu,
    (fun z hz => hbase z hz.1), (fun r z hz => han r z hz.1), ?_⟩
  intro z hz
  letI : (RingHom.ker (F z)).IsPrime := RingHom.ker_isPrime (F z)
  obtain ⟨ez, _⟩ := a3b4a_gysin_exists_rational_residue_equiv
    (RingHom.ker (F z)) (F z) rfl
  have : IsAlgClosed (RingHom.ker (F z)).ResidueField :=
    IsAlgClosed.of_ringEquiv ℂ (RingHom.ker (F z)).ResidueField ez.symm.toRingEquiv
  exact hsum (κ (F z)) hz.2

end HodgeLean.Adapters
