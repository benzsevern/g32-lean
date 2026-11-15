import HodgeLean.Adapters.NormalConeB4aGysinSpreadFlat

/-! # Affine slices with prescribed local quotient algebras -/

noncomputable section
namespace HodgeLean.Adapters

/-- Quotient and localization commute as algebras over the original base,
at a specified prime containing the quotient ideal. -/
def a3b4a_gysin_quotient_localization_algEquiv
    {D R : Type*} [CommRing D] [CommRing R] [Algebra D R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
    Localization.AtPrime (p.map (Ideal.Quotient.mk I)) ≃ₐ[D]
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  let q := p.map (Ideal.Quotient.mk I)
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have hq : q.comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_of_le_left hIp]
  have hcompl : p.primeCompl.map (Ideal.Quotient.mk I) = q.primeCompl := by
    have he : p.primeCompl = (q.comap (Ideal.Quotient.mk I)).primeCompl := by
      ext r
      change r ∉ p ↔ r ∉ q.comap (Ideal.Quotient.mk I)
      rw [hq]
    rw [he]
    exact Ideal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  let M := Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl
  have : IsLocalization M (Localization.AtPrime q) := by
    change IsLocalization (p.primeCompl.map (Ideal.Quotient.mk I)) (Localization.AtPrime q)
    rw [hcompl]
    infer_instance
  have : IsScalarTower D (R ⧸ I)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
    IsScalarTower.to₁₃₄ D R (R ⧸ I) _
  exact (IsLocalization.algEquiv M (Localization.AtPrime q)
    (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))).restrictScalars D

/-- A flat local parameter slice is represented by an affine quotient with
the same local algebra and a flat principal neighborhood of the selected point. -/
theorem a3b4a_gysin_exists_spread_flat_slice
    {D R : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing R] [IsNoetherianRing R] [Algebra D R]
    (π : D) (hπ : Irreducible π) (p : Ideal R) [p.IsPrime]
    (xs : List (Localization.AtPrime p))
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p))
    [Module.Flat D (Localization.AtPrime p ⧸ Ideal.ofList xs)] :
    ∃ ys : List R, ys.length = xs.length ∧
      (∀ y ∈ ys, y ∈ p) ∧
      (Ideal.ofList ys).map (algebraMap R (Localization.AtPrime p)) = Ideal.ofList xs ∧
      ∃ q : Ideal (R ⧸ Ideal.ofList ys), ∃ hq : q.IsPrime, letI := hq
        q.comap (Ideal.Quotient.mk (Ideal.ofList ys)) = p ∧
        ∃ e : Localization.AtPrime q ≃ₐ[D] (Localization.AtPrime p ⧸ Ideal.ofList xs),
          ∃ f : R ⧸ Ideal.ofList ys, f ∉ q ∧ Module.Flat D (Localization.Away f) := by
  obtain ⟨ys, hlen, hmem, hideal⟩ :=
    a3b4a_gysin_exists_affine_parameter_numerators p xs hxs
  let I := Ideal.ofList ys
  have hIp : I ≤ p := Ideal.span_le.mpr hmem
  let q := p.map (Ideal.Quotient.mk I)
  have hq : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  letI := hq
  have hcomap : q.comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_of_le_left hIp]
  let e := (a3b4a_gysin_quotient_localization_algEquiv (D := D) I p hIp).trans
    (Ideal.quotientEquivAlgOfEq D hideal)
  have : Module.Flat D (Localization.AtPrime q) := Module.Flat.of_linearEquiv e.toLinearEquiv
  obtain ⟨f, hf, hflat⟩ := a3b4a_gysin_exists_flat_principal_neighborhood π hπ q
  exact ⟨ys, hlen, hmem, hideal, q, hq, hcomap, e, f, hf, hflat⟩

end HodgeLean.Adapters
