import HodgeLean.Foundations.AppellHumbertProofs

/-! # The Appell--Humbert lattice-and-forms core (FROZEN SPEC)

This module specifies the implication from Appell--Humbert lattice data to a factor of automorphy,
the Riemann relation, and the implication from positivity to form-side nondegeneracy. It does not
construct a sheaf or line bundle, identify a Chern class in `HQ X 2`, prove algebraization by GAGA,
or claim that an ample bundle supplies the datum. The nondegeneracy conclusion is the linear-algebra
input intended for transport to `Foundations.Symplectic` and `Adapters.TopCupPower`; that transport
is not claimed here. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.AppellHumbert

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The Appell--Humbert factor satisfies the translation cocycle identity.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3. -/
theorem spec_appellHumbert_factor_cocycle (D : Datum (V := V)) (l m : D.lattice) (v : V) :
    factor D (l + m) v = factor D l (v + m) * factor D m v :=
  spec_appellHumbert_factor_cocycle_aux D l m v

example (D : Datum (V := V)) (l m : D.lattice) (v : V) :
    factor D (l + m) v = factor D l (v + m) * factor D m v :=
  spec_appellHumbert_factor_cocycle D l m v

/-- A rational alternating form of type `(1,1)` on a full lattice becomes integral on the lattice
after multiplication by a positive integer, and stays of type `(1,1)`. The lattice is finitely
generated, so a common denominator of the values on a `ℤ`-basis suffices.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and Lemma 1.3.1. -/
theorem spec_rational11_clear_denominators (L : Submodule ℤ V) [DiscreteTopology L]
    (hL : IsZLattice ℝ L) (E : V → V → ℝ)
    (hadd₁ : ∀ x y z, E (x + y) z = E x z + E y z)
    (hsmul₁ : ∀ (r : ℝ) x y, E (r • x) y = r * E x y)
    (hadd₂ : ∀ x y z, E x (y + z) = E x y + E x z)
    (hsmul₂ : ∀ (r : ℝ) x y, E x (r • y) = r * E x y)
    (halt : ∀ x, E x x = 0)
    (hrat : ∀ l m : L, ∃ q : ℚ, E l m = q) (h11 : IsTypeOneOne E) :
    ∃ N : ℕ, 0 < N ∧ (∀ l m : L, ∃ n : ℤ, (N : ℝ) * E l m = n) ∧
      IsTypeOneOne (fun v w ↦ (N : ℝ) * E v w) :=
  spec_rational11_clear_denominators_aux L hL E hadd₁ hsmul₁ hadd₂ hsmul₂ halt hrat h11

example (L : Submodule ℤ V) [DiscreteTopology L]
    (hL : IsZLattice ℝ L) (E : V → V → ℝ)
    (hadd₁ : ∀ x y z, E (x + y) z = E x z + E y z)
    (hsmul₁ : ∀ (r : ℝ) x y, E (r • x) y = r * E x y)
    (hadd₂ : ∀ x y z, E x (y + z) = E x y + E x z)
    (hsmul₂ : ∀ (r : ℝ) x y, E x (r • y) = r * E x y)
    (halt : ∀ x, E x x = 0)
    (hrat : ∀ l m : L, ∃ q : ℚ, E l m = q) (h11 : IsTypeOneOne E) :
    ∃ N : ℕ, 0 < N ∧ (∀ l m : L, ∃ n : ℤ, (N : ℝ) * E l m = n) ∧
      IsTypeOneOne (fun v w ↦ (N : ℝ) * E v w) :=
  spec_rational11_clear_denominators L hL E hadd₁ hsmul₁ hadd₂ hsmul₂ halt hrat h11

end Lattice

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
  [IsScalarTower ℝ ℂ V]

/-- An alternating real-bilinear form is the imaginary part of a Hermitian form exactly when it is
invariant under simultaneous multiplication by `i`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
theorem spec_appellHumbert_riemann_relations (E : V → V → ℝ)
    (hadd₁ : ∀ x y z, E (x + y) z = E x z + E y z)
    (hsmul₁ : ∀ (r : ℝ) x y, E (r • x) y = r * E x y)
    (hadd₂ : ∀ x y z, E x (y + z) = E x y + E x z)
    (hsmul₂ : ∀ (r : ℝ) x y, E x (r • y) = r * E x y)
    (halt : ∀ x, E x x = 0) :
    (∃ H : HermitianForm (V := V), H.imaginary = E) ↔ IsTypeOneOne E :=
  spec_appellHumbert_riemann_relations_aux E hadd₁ hsmul₁ hadd₂ hsmul₂ halt

example (E : V → V → ℝ)
    (hadd₁ : ∀ x y z, E (x + y) z = E x z + E y z)
    (hsmul₁ : ∀ (r : ℝ) x y, E (r • x) y = r * E x y)
    (hadd₂ : ∀ x y z, E x (y + z) = E x y + E x z)
    (hsmul₂ : ∀ (r : ℝ) x y, E x (r • y) = r * E x y)
    (halt : ∀ x, E x x = 0) :
    (∃ H : HermitianForm (V := V), H.imaginary = E) ↔ IsTypeOneOne E :=
  spec_appellHumbert_riemann_relations E hadd₁ hsmul₁ hadd₂ hsmul₂ halt

/-- The imaginary part of a positive-definite Hermitian form is nondegenerate.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Chapter 4. -/
theorem spec_positive_imaginary_nondegenerate (H : HermitianForm (V := V))
    (hH : H.IsPositiveDefinite) : IsNondegenerate H.imaginary :=
  spec_positive_imaginary_nondegenerate_aux H hH

example (H : HermitianForm (V := V)) (hH : H.IsPositiveDefinite) :
    IsNondegenerate H.imaginary := spec_positive_imaginary_nondegenerate H hH

/-- Semipositivity does not suffice: the degenerate semipositive form `H(v,w) = conj(v₀) w₀` on
`ℂ²` is not positive definite, and its imaginary part has the nonzero kernel vector `(0,1)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and Chapter 4. -/
theorem spec_degenerate_semipositive_counterexample :
    (∀ v, 0 ≤ (degenerateForm.toFun v v).re) ∧ ¬ degenerateForm.IsPositiveDefinite ∧
      ¬ IsNondegenerate degenerateForm.imaginary :=
  spec_degenerate_semipositive_counterexample_aux

example : ¬ IsNondegenerate degenerateForm.imaginary :=
  spec_degenerate_semipositive_counterexample.2.2

/-- A nondegenerate form represented by contraction with a 2-vector makes that 2-vector
symplectic, providing the bridge to `Foundations.Symplectic` and its top-wedge theorem.
Source: Bourbaki, *Algèbre*, ch. IX, §5. -/
theorem spec_form_nondegenerate_to_symplectic
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (E : Module.Dual ℝ W → Module.Dual ℝ W → ℝ) (ω : ⋀[ℝ]^2 W)
    (hmodel : ∀ φ ψ, E φ ψ = ψ (Symplectic.contract ω φ))
    (hE : IsNondegenerate E) : Symplectic.IsNondegenerate ω :=
  spec_form_nondegenerate_to_symplectic_aux E ω hmodel hE

example {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (E : Module.Dual ℝ W → Module.Dual ℝ W → ℝ) (ω : ⋀[ℝ]^2 W)
    (hmodel : ∀ φ ψ, E φ ψ = ψ (Symplectic.contract ω φ))
    (hE : IsNondegenerate E) : Symplectic.IsNondegenerate ω :=
  spec_form_nondegenerate_to_symplectic E ω hmodel hE

/-- A concrete non-Riemann alternating form: it is not invariant under the complex structure and
therefore is not the imaginary part of any Hermitian form.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
theorem spec_nonRiemann_form_counterexample :
    let E : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℝ :=
      fun v w ↦ (v 0).re * (w 1).re - (v 1).re * (w 0).re
    (∀ v, E v v = 0) ∧ ¬ IsTypeOneOne E ∧
      ¬ ∃ H : HermitianForm (V := Fin 2 → ℂ), H.imaginary = E :=
  spec_nonRiemann_form_counterexample_aux

example :
    let E : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℝ :=
      fun v w ↦ (v 0).re * (w 1).re - (v 1).re * (w 0).re
    ¬ IsTypeOneOne E := spec_nonRiemann_form_counterexample.2.1

/-- On the standard elliptic lattice, the oriented alternating form takes value one on `(1,i)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1. -/
theorem spec_elliptic_degree_one :
    let E : ℂ → ℂ → ℝ := fun z w ↦ z.re * w.im - z.im * w.re
    IsTypeOneOne E ∧ E 1 Complex.I = 1 :=
  spec_elliptic_degree_one_aux

example :
    let E : ℂ → ℂ → ℝ := fun z w ↦ z.re * w.im - z.im * w.re
    E 1 Complex.I = 1 := spec_elliptic_degree_one.2

end Forms

end HodgeLean.Foundations.AppellHumbert
