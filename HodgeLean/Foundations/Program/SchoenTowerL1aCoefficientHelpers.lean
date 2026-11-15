import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Ideal.Maps

/-! # Coefficient calculations for the L1a charts

Implication from an invariant affine ring presentation to coefficient descent
and the product ideal calculation. The geometric chart construction remains separate.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The highest elementary symmetric coefficient evaluates to the product of the parameters.
Source: fundamental theorem of symmetric polynomials, highest elementary coefficient. -/
theorem s2v_l1a_eval_last_esymm
    {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (h : ℕ) (z : Fin (h + 1) → A) :
    MvPolynomial.eval₂Hom f z (MvPolynomial.esymm (Fin (h + 1)) R (h + 1)) =
      ∏ j, z j := by
  classical
  have hp : Finset.powersetCard (h + 1) (Finset.univ : Finset (Fin (h + 1))) =
      {Finset.univ} := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.powersetCard_self (Finset.univ : Finset (Fin (h + 1)))
  rw [MvPolynomial.esymm, hp, Finset.sum_singleton]
  simp only [map_prod, MvPolynomial.eval₂Hom_X']

/-- Permuting the parameters leaves every elementary symmetric coefficient fixed.
Source: fundamental theorem of symmetric polynomials, permutation invariance. -/
theorem s2v_l1a_esymm_invariant
    {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (h : ℕ) (z : Fin (h + 1) → A)
    (ρ : Equiv.Perm (Fin (h + 1)) → (A →+* A))
    (hρR : ∀ τ, (ρ τ).comp f = f)
    (hρz : ∀ τ j, ρ τ (z j) = z (τ j))
    (k : ℕ) (τ : Equiv.Perm (Fin (h + 1))) :
    ρ τ (MvPolynomial.eval₂Hom f z (MvPolynomial.esymm (Fin (h + 1)) R k)) =
      MvPolynomial.eval₂Hom f z (MvPolynomial.esymm (Fin (h + 1)) R k) := by
  rw [MvPolynomial.map_eval₂Hom, hρR τ]
  simp_rw [hρz τ]
  change MvPolynomial.eval₂ f (z ∘ τ) _ = MvPolynomial.eval₂ f z _
  rw [← MvPolynomial.eval₂_rename, MvPolynomial.rename_esymm]

/-- Invariant coefficients descend uniquely through an injective invariant ring presentation.
Source: Schoen (1988), Lemma 2.2, printed p. 13, symmetric coefficients. -/
theorem s2v_l1a_symmetric_coefficient_descent
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (q : B →+* A) (hq : Function.Injective q)
    (h : ℕ) (z : Fin (h + 1) → A)
    (ρ : Equiv.Perm (Fin (h + 1)) → (A →+* A))
    (hρR : ∀ τ, (ρ τ).comp f = f)
    (hρz : ∀ τ j, ρ τ (z j) = z (τ j))
    (himage : ∀ a : A, a ∈ Set.range q ↔ ∀ τ, ρ τ a = a) :
    ∃! c : Fin (h + 1) → B,
      ∀ j, q (c j) = MvPolynomial.eval₂Hom f z
        (MvPolynomial.esymm (Fin (h + 1)) R (j.val + 1)) := by
  have hex : ∀ j : Fin (h + 1), ∃ b : B,
      q b = MvPolynomial.eval₂Hom f z
        (MvPolynomial.esymm (Fin (h + 1)) R (j.val + 1)) := by
    intro j
    apply (himage _).2
    exact s2v_l1a_esymm_invariant f h z ρ hρR hρz (j.val + 1)
  choose c hc using hex
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  funext j
  exact hq ((hc' j).trans (hc j).symm)

/-- The pullback of the principal highest coefficient ideal is the product of parameter ideals.
Source: Hartshorne, Algebraic Geometry, II.6, products of local divisor equations. -/
theorem s2v_l1a_coefficient_ideal_map
    {A B : Type*} [CommRing A] [CommRing B]
    (q : B →+* A) (h : ℕ) (z : Fin (h + 1) → A) (c : B)
    (hc : q c = ∏ j, z j) :
    Ideal.map q (Ideal.span {c}) = ∏ j, Ideal.span {z j} := by
  rw [Ideal.map_span, Set.image_singleton, hc, Ideal.prod_span_singleton]

end HodgeLean.Foundations.Program
