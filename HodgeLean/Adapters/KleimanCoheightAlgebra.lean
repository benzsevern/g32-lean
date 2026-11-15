import HodgeConjecture.Lemmas.RingTheory.TranscendenceDegreeKrullDimension
import HodgeConjecture.Mathlib.RingTheory.SmoothKrullDimension
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Dimension formulas for finite-type algebras over a field

Step 8 of the Kleiman route measures components of a general translated intersection inside the
product of two component closures. This file supplies the commutative algebra: the dimension
formula `ht P + dim S/P = dim S` for a finitely generated domain over a field, the integrality of a
tensor product of finitely generated domains over an algebraically closed field, and the additivity
of Krull dimension under tensor products.
-/

noncomputable section

open Ideal TensorProduct

namespace HodgeLean.Adapters

/-- A quasi-finite algebra with going-down preserves the height of every prime under contraction.
Source: the proof of `Algebra.QuasiFinite.height_eq_height_under`, with going-down in place of
flatness. -/
theorem hc9k8_height_eq_height_under {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] [Algebra.HasGoingDown R S] (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  calc
    P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum S) :=
      PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum S)
    _ = Order.height
        (PrimeSpectrum.comap (algebraMap R S) (⟨P, inferInstance⟩ : PrimeSpectrum S)) := by
      apply Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
        Algebra.QuasiFinite.strictMono_primeSpectrumComap
      intro Q p hp
      have hp' : p.asIdeal < Q.asIdeal.under R := by
        have hp'' : p.asIdeal <
            (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal := hp
        simpa only [PrimeSpectrum.comap_asIdeal] using hp''
      obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        Q.asIdeal.exists_ideal_lt_liesOver_of_lt
          (R := R) (p := p.asIdeal) (q := Q.asIdeal.under R) hp'
      refine ⟨⟨Q', hQ'prime⟩, hQ'Q, ?_⟩
      apply PrimeSpectrum.ext
      simpa [Ideal.under] using hQ'over.over.symm
    _ = (P.under R).height := by
      rw [show (P.under R) =
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S)).asIdeal from rfl]
      exact (PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S))).symm

/-- For a finitely generated domain over a field, the height of a prime plus the dimension of its
quotient is the dimension of the ring.
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6; Noether normalization and going-down. -/
theorem hc9k8_height_add_ringKrullDim_quotient {k S : Type} [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.FiniteType k S] (P : Ideal S) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (S ⧸ P) = ringKrullDim S := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k S
  let : Algebra (MvPolynomial (Fin n) k) S := g.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) S :=
    IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have : FaithfulSMul (MvPolynomial (Fin n) k) S :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Module.Finite (MvPolynomial (Fin n) k) S := hfinite
  have : Algebra.IsIntegral (MvPolynomial (Fin n) k) S := inferInstance
  have hheight : P.height = (P.under (MvPolynomial (Fin n) k)).height :=
    hc9k8_height_eq_height_under P
  have hquot : ringKrullDim (S ⧸ P) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ P.under (MvPolynomial (Fin n) k)) :=
    Algebra.QuasiFinite.ringKrullDim_quotient_eq (k := k) (R := MvPolynomial (Fin n) k) P
  have hdim : ringKrullDim S = n := by
    rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    simp
  rw [hheight, hquot, hdim]
  exact PolynomialCatenary.MvPolynomial.height_add_ringKrullDim_quotient_eq_fin _

/-- A nonzero element of a finitely generated domain over an algebraically closed field survives
some rational point.
Source: Hilbert's Nullstellensatz (Zariski's lemma). -/
theorem hc9k8_exists_algHom_ne_zero {k R : Type} [Field k] [IsAlgClosed k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] (r : R) (hr : r ≠ 0) :
    ∃ φ : R →ₐ[k] k, φ r ≠ 0 := by
  let L := Localization.Away r
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have : Nontrivial L := nontrivial_of_ne (algebraMap R L 0) (algebraMap R L 1)
    (fun h => zero_ne_one (hinj h))
  obtain ⟨m, hm⟩ := Ideal.exists_maximal L
  let K := L ⧸ m
  let : Field K := Ideal.Quotient.field m
  have : Algebra.FiniteType k K := Algebra.FiniteType.trans (S := L) inferInstance
    (Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ L m) Ideal.Quotient.mk_surjective)
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have : Algebra.IsIntegral k K := inferInstance
  have hbij : Function.Bijective (algebraMap k K) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) hbij
  let ψ : R →ₐ[k] K := (Ideal.Quotient.mkₐ k m).comp (IsScalarTower.toAlgHom k R L)
  refine ⟨e.symm.toAlgHom.comp ψ, ?_⟩
  have hu : IsUnit (ψ r) := by
    refine IsUnit.map (Ideal.Quotient.mk m) ?_
    exact IsLocalization.Away.algebraMap_isUnit r
  intro h
  apply hu.ne_zero
  have h2 := congrArg e h
  simpa using h2

/-- The evaluation of a tensor at a `k`-point of the left factor.
Source: `Algebra.TensorProduct.map` and `Algebra.TensorProduct.lid`. -/
noncomputable def hc9k8_evalLeft {k R T : Type} [Field k] [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T] (φ : R →ₐ[k] k) : R ⊗[k] T →ₐ[k] T :=
  (Algebra.TensorProduct.lid k T).toAlgHom.comp
    (Algebra.TensorProduct.map φ (AlgHom.id k T))

example (φ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ) : MvPolynomial (Fin 1) ℂ ⊗[ℂ] ℂ →ₐ[ℂ] ℂ :=
  hc9k8_evalLeft φ

/-- Evaluation at a point of the left factor acts on coordinates in a basis of the right factor.
Source: `Algebra.TensorProduct.basis_repr_tmul`. -/
theorem hc9k8_evalLeft_repr {k R T : Type} [Field k] [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T] {ι : Type} (b : Module.Basis ι k T) (φ : R →ₐ[k] k)
    (f : R ⊗[k] T) (i : ι) :
    b.repr (hc9k8_evalLeft φ f) i =
      φ ((Algebra.TensorProduct.basis R b).repr f i) := by
  induction f using TensorProduct.inductionOn with
  | tmul r t =>
    simp [hc9k8_evalLeft, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
    rw [← Algebra.smul_def, map_smul]
    simp
  | add f g hf hg => simp [hf, hg]

/-- Over an algebraically closed field, the tensor product of a finitely generated domain with a
domain is a domain.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.15; Nullstellensatz. -/
theorem hc9k8_isDomain_tensorProduct {k R T : Type} [Field k] [IsAlgClosed k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] [CommRing T] [IsDomain T]
    [Algebra k T] : IsDomain (R ⊗[k] T) := by
  let b := Module.Free.chooseBasis k T
  let B := Algebra.TensorProduct.basis R b
  have : Nontrivial (R ⊗[k] T) := by
    obtain ⟨φ, -⟩ := hc9k8_exists_algHom_ne_zero (k := k) (1 : R) one_ne_zero
    refine nontrivial_of_ne 0 1 fun h => ?_
    have := congrArg (hc9k8_evalLeft (T := T) φ) h
    simp at this
  have : NoZeroDivisors (R ⊗[k] T) := by
    refine ⟨fun {f g} hfg => ?_⟩
    by_contra! hne
    obtain ⟨i, hi⟩ : ∃ i, B.repr f i ≠ 0 := by
      by_contra! h
      exact hne.1 (B.repr.injective (by ext i; simpa using h i))
    obtain ⟨j, hj⟩ : ∃ j, B.repr g j ≠ 0 := by
      by_contra! h
      exact hne.2 (B.repr.injective (by ext j; simpa using h j))
    obtain ⟨φ, hφ⟩ := hc9k8_exists_algHom_ne_zero (k := k) _ (mul_ne_zero hi hj)
    have h0 := congrArg (hc9k8_evalLeft (T := T) φ) hfg
    rw [map_mul, map_zero, mul_eq_zero] at h0
    rw [map_mul] at hφ
    rcases h0 with h0 | h0
    · apply left_ne_zero_of_mul hφ
      rw [← hc9k8_evalLeft_repr b φ f i, h0]
      simp
    · apply right_ne_zero_of_mul hφ
      rw [← hc9k8_evalLeft_repr b φ g j, h0]
      simp
  exact NoZeroDivisors.to_isDomain _

/-- A finite injective polynomial subalgebra in `n` variables gives Krull dimension `n`.
Source: `PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective`. -/
theorem hc9k8_ringKrullDim_eq_card {k R : Type} [Field k] [CommRing R] [Algebra k R]
    {n : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] R) (hg : Function.Injective g)
    (hfin : g.Finite) : ringKrullDim R = n := by
  let : Algebra (MvPolynomial (Fin n) k) R := g.toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) k) R := hfin
  have : Nontrivial R := hg.nontrivial
  rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  simp

/-- The Krull dimension of a tensor product of finite-type algebras over a field is the sum of
the dimensions.
Source: Noether normalization of both factors; Hartshorne, *Algebraic Geometry*,
Exercise II.3.20. -/
theorem hc9k8_ringKrullDim_tensorProduct {k R T : Type} [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing T] [Algebra k T] [Algebra.FiniteType k T]
    [Nontrivial R] [Nontrivial T] :
    ringKrullDim (R ⊗[k] T) = ringKrullDim R + ringKrullDim T := by
  obtain ⟨r, g₁, hg₁, hf₁⟩ := exists_finite_inj_algHom_of_fg k R
  obtain ⟨s, g₂, hg₂, hf₂⟩ := exists_finite_inj_algHom_of_fg k T
  let G := Algebra.TensorProduct.map g₁ g₂
  have hGfin : G.toRingHom.Finite := RingHom.Finite.tensorProductMap hf₁ hf₂
  have hGinj : Function.Injective G :=
    TensorProduct.map_injective_of_flat_flat g₁.toLinearMap g₂.toLinearMap hg₁ hg₂
  let e := MvPolynomial.tensorEquivSum (R := k) (S := k) (σ := Fin r) (ι := Fin s)
  let G' : MvPolynomial (Fin r ⊕ Fin s) k →ₐ[k] R ⊗[k] T :=
    G.comp (e.symm.restrictScalars k).toAlgHom
  let e' := (Equiv.sumCongr (Equiv.refl (Fin r)) (Equiv.refl (Fin s))).trans finSumFinEquiv
  let G'' : MvPolynomial (Fin (r + s)) k →ₐ[k] R ⊗[k] T :=
    G'.comp (MvPolynomial.renameEquiv k e'.symm).toAlgHom
  have hG''inj : Function.Injective G'' :=
    hGinj.comp ((e.symm.restrictScalars k).injective.comp
      (MvPolynomial.renameEquiv k e'.symm).injective)
  have hG''fin : G''.Finite := by
    have h1 : (e.symm.restrictScalars k).toAlgHom.toRingHom.Finite :=
      (e.symm.restrictScalars k).toRingEquiv.finite
    have h2 : (MvPolynomial.renameEquiv k e'.symm).toAlgHom.toRingHom.Finite :=
      (MvPolynomial.renameEquiv k e'.symm).toRingEquiv.finite
    exact (hGfin.comp h1).comp h2
  rw [hc9k8_ringKrullDim_eq_card G'' hG''inj hG''fin, hc9k8_ringKrullDim_eq_card g₁ hg₁ hf₁,
    hc9k8_ringKrullDim_eq_card g₂ hg₂ hf₂]
  norm_cast

example : ringKrullDim (MvPolynomial (Fin 1) ℂ ⊗[ℂ] MvPolynomial (Fin 1) ℂ) =
    ringKrullDim (MvPolynomial (Fin 1) ℂ) + ringKrullDim (MvPolynomial (Fin 1) ℂ) :=
  hc9k8_ringKrullDim_tensorProduct

end HodgeLean.Adapters
