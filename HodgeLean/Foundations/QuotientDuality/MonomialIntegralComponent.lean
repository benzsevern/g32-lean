import HodgeLean.Foundations.QuotientDuality.MonomialRootCoverRotations
import HodgeLean.Foundations.QuotientDuality.MonomialNormalComponent

/-! Selection of a normal integral root-cover component in the prescribed ambient field. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality
universe w u v

theorem monomial_integral_root_component
    (k : Type w) [Field k] [IsAlgClosed k] [CharZero k]
    (n m : ℕ) (hm : 0 < m) (R : Type u) (L : Type v)
    [CommRing R] [Field L] [Algebra k R] [Algebra k L]
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (f : R →ₐ[k] L) (hf : Function.Injective f) (ε : R) (hε : IsUnit ε)
    (w : Fin n → L) (hw : ∀ j, w j ^ m = f (c (MvPolynomial.X j)))
    (u : L) (hu : u ^ m = f ε) :
    ∃ (A : Type (max u w)) (hA : CommRing A), letI := hA
      ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A)
        (i : R →+* A) (b : ULift.{0} (MvPolynomial (Fin n) k) →+* A)
        (W : Fin n → A) (U : A) (σ : A →+* L),
        i.IsIntegral ∧ b.Etale ∧ Function.Injective σ ∧ σ.comp i = f.toRingHom ∧
        (∀ j, σ (W j) = w j) ∧ σ U = u ∧
        b.comp (rootParameterMap k n m).toRingHom = i.comp c.toRingHom ∧
        (∀ j, W j ^ m = i (c (MvPolynomial.X j))) ∧ U ^ m = i ε ∧ IsUnit U ∧
        (letI : Algebra R A := i.toAlgebra
         Algebra.adjoin R (Set.range W ∪ {U}) = ⊤) := by
  obtain ⟨A₀, hA₀, i₀, b₀, W₀, U₀, τ, hi₀, hb₀, hparam, hWpow, hUpow, hUunit,
    hτi, hτW, hτU, hWcan, hrot, hext, hextSelf, hgen₀⟩ :=
    monomial_root_cover_all_rotations n m hm R L c hc f ε hε w hw u hu
  letI := hA₀
  have hτi' : τ.comp i₀ = f.toRingHom := RingHom.ext hτi
  let p := RingHom.ker τ
  have hp : IsMinimalPrime p := integral_cover_kernel_minimal i₀ hi₀ τ (by
    rw [hτi']
    exact hf)
  obtain ⟨hb, hdom, hnormal⟩ := etale_polynomial_root_component k n A₀ b₀ hb₀ p hp
  let A := A₀ ⧸ p
  letI : IsDomain A := hdom
  letI : IsIntegrallyClosed A := hnormal
  let π : A₀ →+* A := Ideal.Quotient.mk p
  let i : R →+* A := π.comp i₀
  let b : ULift.{0} (MvPolynomial (Fin n) k) →+* A := π.comp b₀
  let W : Fin n → A := fun j => π (W₀ j)
  let U : A := π U₀
  let σ : A →+* L := τ.kerLift
  have hσ (a : A₀) : σ (π a) = τ a := τ.kerLift_mk a
  refine ⟨A, inferInstance, inferInstance, inferInstance, i, b, W, U, σ,
    hi₀.trans _ _ (π.isIntegral_of_surjective Ideal.Quotient.mk_surjective), hb,
    τ.kerLift_injective, ?_, ?_, (hσ U₀).trans hτU, ?_, ?_, ?_, hUunit.map π, ?_⟩
  · ext r
    exact (hσ (i₀ r)).trans (hτi r)
  · intro j
    exact (hσ (W₀ j)).trans (hτW j)
  · exact congrArg (fun t => π.comp t) hparam
  · intro j
    exact (map_pow π (W₀ j) m).symm.trans (congrArg π (hWpow j))
  · exact (map_pow π U₀ m).symm.trans (congrArg π hUpow)

  · letI : Algebra R A₀ := i₀.toAlgebra
    letI : Algebra R A := i.toAlgebra
    let πA : A₀ →ₐ[R] A := { π with commutes' := fun _ => rfl }
    have H := congrArg (fun S : Subalgebra R A₀ => S.map πA) hgen₀
    rw [AlgHom.map_adjoin, Algebra.map_top,
      (AlgHom.range_eq_top πA).mpr Ideal.Quotient.mk_surjective] at H
    have he : πA '' (Set.range W₀ ∪ {U₀}) = Set.range W ∪ {U} := by
      ext x
      constructor
      · rintro ⟨y, (⟨j, rfl⟩ | rfl), rfl⟩
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr rfl
      · rintro (⟨j, rfl⟩ | rfl)
        · exact ⟨W₀ j, Or.inl ⟨j, rfl⟩, rfl⟩
        · exact ⟨U₀, Or.inr rfl, rfl⟩
    rw [he] at H
    exact H

#print axioms monomial_integral_root_component
end HodgeLean.Foundations.QuotientDuality
