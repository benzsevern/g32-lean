import HodgeLean.Adapters.NormalConeB4aGysinAffineModel

/-! # Exact comparison models of slices over the affine parameter base -/

noncomputable section
namespace HodgeLean.Adapters

/-- A flat local slice with Artinian parameter fibre at a field-valued point
constructs an affine finite flat comparison model with the original sliced length. -/
theorem a3b4a_gysin_exists_exact_affine_model_of_slice
    {k D R : Type} [Field k] [CommRing D] [IsDomain D] [IsDedekindDomain D]
    [CommRing R] [IsNoetherianRing R] [Algebra k D] [Algebra k R] [Algebra D R]
    [IsScalarTower k D R] [Algebra.FiniteType D R]
    (b : Ideal D) [b.IsPrime] (p : Ideal R) [p.IsPrime] [p.LiesOver b]
    (w : R →ₐ[k] k) (hw : RingHom.ker w = p)
    (xs : List (Localization.AtPrime p))
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p))
    [Module.Flat D (Localization.AtPrime p ⧸ Ideal.ofList xs)]
    [IsArtinianRing ((Localization.AtPrime p ⧸ Ideal.ofList xs) ⧸
      b.map
        (algebraMap D (Localization.AtPrime p ⧸ Ideal.ofList xs)))] :
    ∃ ys : List R, ys.length = xs.length ∧ (∀ y ∈ ys, y ∈ p) ∧
      (Ideal.ofList ys).map (algebraMap R (Localization.AtPrime p)) = Ideal.ofList xs ∧
      ∃ (q : Ideal (R ⧸ Ideal.ofList ys)) (hq : q.IsPrime), letI := hq
        q.comap (Ideal.Quotient.mk (Ideal.ofList ys)) = p ∧
        ∃ f : R ⧸ Ideal.ofList ys, f ∉ q ∧
          ∃ (D' : Type) (_ : CommRing D') (_ : Algebra D D') (_ : Algebra.Etale D D')
            (P : Ideal D') (_ : P.IsPrime) (_ : P.LiesOver b)
            (e : TensorProduct D D' (Localization.Away f)), IsIdempotentElem e ∧
            Module.Finite D' (Localization.Away e) ∧
            Module.Flat D' (Localization.Away e) ∧
            IsLocalRing (P.Fiber (Localization.Away e)) ∧
            Function.Bijective (Ideal.ResidueField.mapₐ b P
              (Algebra.ofId _ _) (P.over_def b)) ∧
            (∃ Q : Ideal (TensorProduct D D' (Localization.Away f)), Q.IsPrime ∧ Q.LiesOver P ∧
              (Q.comap Algebra.TensorProduct.includeRight.toRingHom).comap
                (algebraMap (R ⧸ Ideal.ofList ys) (Localization.Away f)) = q ∧ e ∉ Q) ∧
            Module.length (P.Fiber (Localization.Away e)) (P.Fiber (Localization.Away e)) =
              Module.length
                ((Localization.AtPrime p ⧸ Ideal.ofList xs) ⧸
                  b.map
                    (algebraMap D (Localization.AtPrime p ⧸ Ideal.ofList xs)))
                ((Localization.AtPrime p ⧸ Ideal.ofList xs) ⧸
                  b.map
                    (algebraMap D (Localization.AtPrime p ⧸ Ideal.ofList xs))) := by
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
  let a := (a3b4a_gysin_quotient_localization_algEquiv (D := D) I p hIp).trans
    (Ideal.quotientEquivAlgOfEq D hideal)
  have : Module.Flat D (Localization.AtPrime q) := Module.Flat.of_linearEquiv a.toLinearEquiv
  have hqp : q.LiesOver p := ⟨hcomap.symm⟩
  have : q.LiesOver b := Ideal.LiesOver.trans q p b
  let wQ : (R ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I w (fun r hr => by
    exact (show r ∈ RingHom.ker w from hw.symm ▸ hIp hr))
  have hker : RingHom.ker wQ = q := by
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    rw [hcomap]
    change RingHom.ker (wQ.toRingHom.comp (Ideal.Quotient.mk I)) = p
    exact hw
  let J := b.map (algebraMap D (Localization.AtPrime q))
  let L := Localization.AtPrime p ⧸ Ideal.ofList xs
  let JL := b.map (algebraMap D L)
  have hJ : JL = J.map a.toRingHom := by
    dsimp only [JL, J]
    rw [Ideal.map_map]
    congr 1
    exact a.toAlgHom.comp_algebraMap.symm
  have : IsArtinianRing (Localization.AtPrime q ⧸ J) :=
    (Ideal.quotientEquivAlg J JL a hJ).symm.toRingEquiv.isArtinianRing
  have : Algebra.QuasiFiniteAt D q :=
    a3b4a_gysin_quasiFiniteAt_of_affine_point b q wQ hker
  obtain ⟨f, hf, D', _, _, _, P, _, _, e, he, hfin, hflat, hlocal, hres, hpoint, hlength⟩ :=
    a3b4a_gysin_exists_exact_model_over_dedekind_base b q
  have htransport := a3b2_length_eq_of_ringEquiv
    (Ideal.quotientEquivAlg J JL a hJ).toRingEquiv
  exact ⟨ys, hlen, hmem, hideal, q, hq, hcomap, f, hf, D', inferInstance,
    inferInstance, inferInstance, P, inferInstance, inferInstance, e,
    he, hfin, hflat, hlocal, hres, hpoint, hlength.trans htransport⟩

end HodgeLean.Adapters
