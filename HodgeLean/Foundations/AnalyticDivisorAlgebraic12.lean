import HodgeLean.Foundations.AnalyticDivisorAlgebraic12Proofs

/-! # Resultant and discriminant locality at nearby points: frozen specification

This stage transports resultants and discriminants through coefficientwise ring equivalences,
identifies the germs at nearby points of the stage-ten fibre resultant and discriminant
representatives, propagates nonvanishing of these germs over an open preconnected
neighbourhood, and restates the stage-ten clean-root corollaries over germs at an arbitrary point
`p`, without any compatibility premise and without assuming that the polynomial is Weierstrass
at `p`. It claims the implication from monicity at the origin (respectively at `p`) to these
locality statements. It does not claim a sheaf of analytic divisors, glueing, or any
algebraization statement.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic12

open Filter Polynomial Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11

/-- The coefficient germs of the polynomial built at `p` from a representative family are the germs
at `p` of the representatives on the support of `P`, and zero off it. Source: Bourbaki,
*Algebra*, Ch. IV, §1, coefficients of a finite sum of monomials. -/
theorem spec_polynomialAt_coeff {n : ℕ} (P : Polynomial (AnalyticGerm n))
    (a : ℕ → (Fin n → ℂ) → ℂ) (p : Fin n → ℂ) (ha : ∀ j, AnalyticAt ℂ (a j) p) (j : ℕ) :
    ((gaga12_polynomialAt P a p ha).coeff j).1 =
      if j ∈ P.support then @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j) else 0 :=
  spec_polynomialAt_coeff_aux P a p ha j

/-- Coefficientwise transport through a ring equivalence carries the resultant to the resultant.
Degrees are preserved by injectivity, so the default Sylvester sizes agree. Source: Bourbaki,
*Algebra*, Ch. IV, §6, functoriality of the Sylvester determinant. -/
theorem spec_resultant_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P Q : Polynomial R) :
    (P.map e.toRingHom).resultant (Q.map e.toRingHom) = e (P.resultant Q) :=
  spec_resultant_map_ringEquiv_aux e P Q

/-- Coefficientwise transport through a ring equivalence carries the discriminant to the
discriminant, including the constant and zero cases where both sides are `1`. Source: Bourbaki,
*Algebra*, Ch. IV, §6, the discriminant as a polynomial in the coefficients. -/
theorem spec_discr_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) :
    (P.map e.toRingHom).discr = e P.discr :=
  spec_discr_map_ringEquiv_aux e P

/-- The stage-eleven translation equivalence from germs at `p` to germs at zero can be chosen to
carry resultants and discriminants of polynomials over germs at `p` to those of the translated
polynomials. Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Definition 1; Bourbaki, *Algebra*, Ch. IV, §6. -/
theorem spec_germ_translation_resultant_discr (n : ℕ) (p : Fin n → ℂ) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ g : AnalyticGermAt n p,
        analyticGermValue n (e g) = analyticGermAtValue n p g) ∧
      (∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩) ∧
      (∀ A B : Polynomial (AnalyticGermAt n p),
        (A.map e.toRingHom).resultant (B.map e.toRingHom) = e (A.resultant B)) ∧
      ∀ A : Polynomial (AnalyticGermAt n p), (A.map e.toRingHom).discr = e A.discr :=
  spec_germ_translation_resultant_discr_aux n p

/-- If representatives have leading coefficient one on a neighbourhood `U` of `p` and `R` is the
fibre resultant on `U`, then the germ of `R` at `p` is the resultant of the coefficient
polynomials at `p`. Degree drops of the second fibre near `p` are allowed. Source: Bourbaki,
*Algebra*, Ch. IV, §6, functoriality and degree padding of the Sylvester determinant. -/
theorem spec_resultant_germ_at_nearby_point {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic)
    (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (p : Fin n → ℂ) (hU : U ∈ nhds p)
    (hap : ∀ j, AnalyticAt ℂ (a j) p) (hbp : ∀ j, AnalyticAt ℂ (b j) p)
    (hlead : ∀ x ∈ U, a P.natDegree x = 1)
    (hR : ∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
      (g.sum fun j _ ↦ monomial j (b j x))) :
    ((gaga12_polynomialAt P a p hap).resultant (gaga12_polynomialAt g b p hbp)).1 =
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R :=
  spec_resultant_germ_at_nearby_point_aux P g hP a b R U p hU hap hbp hlead hR

/-- If representatives have leading coefficient one on a neighbourhood `U` of `p` and `D` is the
fibre discriminant on `U`, then the germ of `D` at `p` is the discriminant of the coefficient
polynomial at `p`. Source: Bourbaki, *Algebra*, Ch. IV, §6, the discriminant as a polynomial in
the coefficients at fixed degree. -/
theorem spec_discriminant_germ_at_nearby_point {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic)
    (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (p : Fin n → ℂ) (hU : U ∈ nhds p) (hap : ∀ j, AnalyticAt ℂ (a j) p)
    (hlead : ∀ x ∈ U, a P.natDegree x = 1)
    (hD : ∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) :
    (gaga12_polynomialAt P a p hap).discr.1 =
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D :=
  spec_discriminant_germ_at_nearby_point_aux P hP a D U p hU hap hlead hD

/-- A monic germ polynomial and a second germ polynomial have representatives on an open
preconnected neighbourhood of the origin whose leading representative is one there, and whose
fibre resultant has, at every point `p` of the neighbourhood, the resultant of the coefficient
polynomials at `p` as its germ. Source: Bourbaki, *Algebra*, Ch. IV, §6; Gunning--Rossi, II.B,
Definition 1. -/
theorem spec_resultant_representative_nearby {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      AnalyticOnNhd ℂ R U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R = (P.resultant g).1 ∧
      (∀ x ∈ U, a P.natDegree x = 1) ∧
      (∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x))) ∧
      ∀ p ∈ U, ∀ (hap : ∀ j, AnalyticAt ℂ (a j) p) (hbp : ∀ j, AnalyticAt ℂ (b j) p),
        ((gaga12_polynomialAt P a p hap).resultant (gaga12_polynomialAt g b p hbp)).1 =
          @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R :=
  spec_resultant_representative_nearby_aux P g hP

/-- A monic germ polynomial has representatives on an open preconnected neighbourhood of the
origin whose leading representative is one there, and whose fibre discriminant has, at every
point `p` of the neighbourhood, the discriminant of the coefficient polynomial at `p` as its germ.
Source: Bourbaki, *Algebra*, Ch. IV, §6; Gunning--Rossi, II.B, Definition 1. -/
theorem spec_discriminant_representative_nearby {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ AnalyticOnNhd ℂ D U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 ∧
      (∀ x ∈ U, a P.natDegree x = 1) ∧
      (∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) ∧
      ∀ p ∈ U, ∀ hap : ∀ j, AnalyticAt ℂ (a j) p,
        (gaga12_polynomialAt P a p hap).discr.1 =
          @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D :=
  spec_discriminant_representative_nearby_aux P hP

/-- A function analytic on an open preconnected set with a nonzero germ at one point of the set
has a nonzero germ at every point of the set. Source: Gunning--Rossi, *Analytic Functions of
Several Complex Variables*, Ch. I, §A, the identity theorem; Mathlib
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
theorem spec_germ_ne_zero_of_preconnected {n : ℕ}
    (R : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hR : AnalyticOnNhd ℂ R U)
    (q p : Fin n → ℂ) (hq : q ∈ U) (hp : p ∈ U)
    (hne : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds q) R ≠ 0) :
    @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R ≠ 0 :=
  spec_germ_ne_zero_of_preconnected_aux R U hU hconn hR q p hq hp hne

/-- If the resultant germ of a monic polynomial and a second polynomial is nonzero at the origin,
then representatives exist on an open preconnected neighbourhood of the origin such that the
resultant of the coefficient polynomials at every point of the neighbourhood is nonzero.
Source: Gunning--Rossi, Ch. I, §A, the identity theorem; Bourbaki, *Algebra*, Ch. IV, §6. -/
theorem spec_resultant_ne_zero_nearby {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) (hres : P.resultant g ≠ 0) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      ∀ p ∈ U, ∀ (hap : ∀ j, AnalyticAt ℂ (a j) p) (hbp : ∀ j, AnalyticAt ℂ (b j) p),
        (gaga12_polynomialAt P a p hap).resultant (gaga12_polynomialAt g b p hbp) ≠ 0 :=
  spec_resultant_ne_zero_nearby_aux P g hP hres

/-- If the discriminant germ of a monic polynomial is nonzero at the origin, then representatives
exist on an open preconnected neighbourhood of the origin such that the discriminant of the
coefficient polynomial at every point of the neighbourhood is nonzero. Source: Gunning--Rossi,
Ch. I, §A, the identity theorem; Bourbaki, *Algebra*, Ch. IV, §6. -/
theorem spec_discriminant_ne_zero_nearby {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) (hdiscr : P.discr ≠ 0) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      ∀ p ∈ U, ∀ hap : ∀ j, AnalyticAt ℂ (a j) p,
        (gaga12_polynomialAt P a p hap).discr ≠ 0 :=
  spec_discriminant_ne_zero_nearby_aux P hP hdiscr

/-- The stage-ten common-root corollary at a point `p`: for a monic polynomial over germs at `p`,
there are representatives near `p` such that nonvanishing of the resultant representative rules
out a common fibre root. Weierstrass-ness at `p` is not assumed. Source: de Jong--Pfister,
*Local Analytic Geometry*, Ch. 3; Gunning--Rossi, II.B, Definition 1, translation of germs. -/
theorem spec_resultant_nonzero_fibre_avoids_common_root_at {n : ℕ}
    (p : Fin n → ℂ) (A B : Polynomial (AnalyticGermAt n p)) (hA : A.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds p ∧ AnalyticOnNhd ℂ R U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j) = (A.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (b j) = (B.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R = (A.resultant B).1 ∧
      ∀ x ∈ U, R x ≠ 0 → ∀ w : ℂ,
        (A.sum fun j _ ↦ monomial j (a j x)).eval w ≠ 0 ∨
          (B.sum fun j _ ↦ monomial j (b j x)).eval w ≠ 0 :=
  spec_resultant_nonzero_fibre_avoids_common_root_at_aux p A B hA

/-- The stage-ten simple-root corollary at a point `p`: for a monic polynomial over germs at `p`,
there are representatives near `p` such that nonvanishing of the discriminant representative
makes every fibre root simple. Weierstrass-ness at `p` is not assumed. Source: de Jong--Pfister,
*Local Analytic Geometry*, Ch. 3--4; Gunning--Rossi, II.B, Definition 1. -/
theorem spec_discriminant_nonzero_fibre_simple_roots_at {n : ℕ}
    (p : Fin n → ℂ) (A : Polynomial (AnalyticGermAt n p)) (hA : A.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds p ∧ AnalyticOnNhd ℂ D U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j) = (A.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D = A.discr.1 ∧
      ∀ x ∈ U, D x ≠ 0 → ∀ w : ℂ,
        (A.sum fun j _ ↦ monomial j (a j x)).eval w = 0 →
          (A.sum fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 :=
  spec_discriminant_nonzero_fibre_simple_roots_at_aux p A hA

-- Degenerate convention checks used when freezing the statements above.

-- `p = 0`: the coefficient polynomial at the origin has the coefficient germs of `P`.
example {n : ℕ} (P : Polynomial (AnalyticGerm n)) (a : ℕ → (Fin n → ℂ) → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (haP : ∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) (j : ℕ) :
    ((gaga12_polynomialAt P a 0 ha).coeff j).1 = (P.coeff j).1 := by
  classical
  rw [spec_polynomialAt_coeff]
  split_ifs with hj
  · exact haP j
  · rw [Polynomial.notMem_support_iff.mp hj]
    rfl

-- `n = 0`: the whole one-point space is an open preconnected neighbourhood.
example : IsOpen (Set.univ : Set (Fin 0 → ℂ)) ∧ IsPreconnected (Set.univ : Set (Fin 0 → ℂ)) :=
  ⟨isOpen_univ, isPreconnected_univ⟩

-- Degree one, a unit and a zero second polynomial.
example : (X : ℂ[X]).discr = 1 := by
  apply discr_of_degree_eq_one
  simp

example : (X : ℂ[X]).resultant 1 = 1 := by simp

example : (X : ℂ[X]).resultant 0 = 0 := by simp

-- A fibre degree drop of the second polynomial is invisible after padding when the first is monic.
example : (X : ℂ[X]).resultant (C 1) (X : ℂ[X]).natDegree 1 = (X : ℂ[X]).resultant (C 1) :=
  AnalyticDivisorAlgebraic10.spec_resultant_fixed_degree_of_monic X (C 1) monic_X 1 (by simp)

-- Without monicity the degree drop matters: `Res(0, X) = 0` but `Res(0, 1) = 1`.
example : (0 : ℂ[X]).resultant X = 0 ∧ (0 : ℂ[X]).resultant 1 = 1 := by
  constructor <;> simp [resultant_zero_left_deg]

-- The non-Weierstrass translate `X + z₀` at `p` is monic, so the corollaries at `p` apply to it.
example (p : Fin 1 → ℂ) :
    ∃ (a : ℕ → (Fin 1 → ℂ) → ℂ) (D : (Fin 1 → ℂ) → ℂ) (U : Set (Fin 1 → ℂ)),
      U ∈ nhds p ∧ ∀ x ∈ U, D x ≠ 0 → ∀ w : ℂ,
        ((X + C (gaga11_coordinateGermAt p) : Polynomial (AnalyticGermAt 1 p)).sum
          fun j _ ↦ monomial j (a j x)).eval w = 0 →
        ((X + C (gaga11_coordinateGermAt p) : Polynomial (AnalyticGermAt 1 p)).sum
          fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 := by
  obtain ⟨a, D, U, hU, _hD, _ha, _haA, _hDA, hroot⟩ :=
    spec_discriminant_nonzero_fibre_simple_roots_at p _ (monic_X_add_C _)
  exact ⟨a, D, U, hU, hroot⟩

-- Mathlib conventions and empty products.
example : ((0 : ℂ[X]).resultant 0) = 1 := by simp

example : (0 : ℂ[X]).discr = 1 := by simp only [← C_0, discr_C]

example : (∏ i ∈ (∅ : Finset ℕ), (i : ℂ)) = 1 := by simp

-- Ring-equivalence transport at the identity.
example (P Q : ℂ[X]) :
    (P.map (RingEquiv.refl ℂ).toRingHom).resultant (Q.map (RingEquiv.refl ℂ).toRingHom) =
      P.resultant Q := spec_resultant_map_ringEquiv (RingEquiv.refl ℂ) P Q

end HodgeLean.Foundations.AnalyticDivisorAlgebraic12
