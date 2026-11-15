import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.MonomialRotation
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.PointedRootCover
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.NormalGeneratorInertia
import HodgeLean.Foundations.FieldTheory.CyclicKummerChecks
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Auxiliary tame monomial chart and inertia contracts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace AlgebraicGeometry.TameMonomialCover

/-- Pair rescaling preserves the other monomial exponents on both charts.
Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15; SchoenTowerI2aProofs.s2v_i2a_blowup_exponents_aux. -/
theorem pair_rescaling_aux
    (K : Type*) [Field K] (n m a b : ℕ) (hm : 0 < m)
    (hab : a + b = m) (α : Fin n → ℕ)
    (ε t x y : K) (z : Fin n → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (ht : t ^ m = ε * x ^ a * y ^ b * ∏ j, z j ^ α j) :
    (t / x) ^ m = ε * (y / x) ^ b * ∏ j, z j ^ α j ∧
    (t / y) ^ m = ε * (x / y) ^ a * ∏ j, z j ^ α j := by
  constructor
  · rw [div_pow, ht, ← hab, pow_add, div_pow]
    field_simp [hx, hy]
  · rw [div_pow, ht, ← hab, pow_add, div_pow]
    field_simp [hx, hy]

/-- A vanishing coordinate supplies a subgroup fixing every integral-element evaluation.
Source: Schoen (1988), Lemma 2.5, printed p. 15, and Sublemma 2.9, printed p. 19; SchoenTowerI2aProofs.s2v_i2a_normalized_monomial_inertia_aux. -/
theorem integralClosure_inertia_aux
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    (n m : ℕ) (hm : 0 < m)
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε *
      ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (ζ : k) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (hd : d v = algebraMap k K ζ * v)
    (p : integralClosure R K →ₐ[k] k) (j : Fin n)
    (hp : p (algebraMap R (integralClosure R K) (c (MvPolynomial.X j))) = 0) :
    Subgroup.zpowers (d.mapIntegralClosure ^ α j) ≤
      { carrier := {g : integralClosure R K ≃ₐ[R] integralClosure R K |
            ∀ b, p (g b) = p b}
        one_mem' := fun _ => rfl
        mul_mem' := fun hg hk b => (hg _).trans (hk b)
        inv_mem' := fun {g} hg b => by
          have H := hg (g⁻¹ b)
          simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using H.symm } := by
  let q : R := ε * ∏ k, (c (MvPolynomial.X k)) ^ α k
  have hvq : v ^ m = algebraMap R K q := by
    simpa only [q, map_mul, map_prod, map_pow] using hv
  have hvne : v ≠ 0 :=
    Helpers.etale_monomial_generator_ne_zero hinj n m hm c hc α ε hε v hv
  have hζR : IsPrimitiveRoot (algebraMap k R ζ) m :=
    hζ.map_of_injective (algebraMap k R).injective
  have hBinomial : Irreducible ((Polynomial.X : Polynomial R) ^ m - Polynomial.C q) :=
    Helpers.binomial_irreducible hinj m hm (algebraMap k R ζ) hζR d v hvne
      (by rw [← IsScalarTower.algebraMap_apply k R K]; exact hd) q hvq
  have hperiod : d ^ m = 1 := Helpers.aut_pow_eq_one v hgen d
    (algebraMap k R ζ) (by rw [← IsScalarTower.algebraMap_apply k R K]; exact hd)
    m (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hperiodN : d.mapIntegralClosure ^ m = 1 :=
    Helpers.integralClosure_pow_eq_one d m hperiod
  by_cases hdiv : m ∣ α j
  · obtain ⟨k, hk⟩ := hdiv
    rw [hk, pow_mul, hperiodN, one_pow]
    exact Subgroup.zpowers_le.mpr (Subgroup.one_mem _)
  · have hα : α j ≠ 0 := by
      intro hz
      apply hdiv
      rw [hz]
      exact dvd_zero m
    have hpq : p (algebraMap R (integralClosure R K) q) = 0 := by
      let f : R →+* k := p.toRingHom.comp (algebraMap R (integralClosure R K))
      change f (ε * ∏ k, (c (MvPolynomial.X k)) ^ α k) = 0
      rw [map_mul, map_prod]
      have hprod : ∏ k, f ((c (MvPolynomial.X k)) ^ α k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        rw [map_pow, show f (c (MvPolynomial.X j)) = 0 from hp, zero_pow hα]
      rw [hprod, mul_zero]
    have hvResidue := Helpers.binomial_residue_zero m hm q v hvq p.toRingHom hpq
    obtain ⟨wroot, uroot, hwint, huint, pLift, hwroot, huroot, hvroot, hpLift⟩ :=
      Helpers.etale_integral_root_choices n m hm R K c hc hinj α ε v hv p
    let f : K →ₐ[R] AlgebraicClosure K := IsScalarTower.toAlgHom R K (AlgebraicClosure K)
    have hpLiftBase : pLift (algebraMap R (integralClosure R (AlgebraicClosure K))
        (c (MvPolynomial.X j))) = 0 := by
      rw [← f.mapIntegralClosure.commutes (c (MvPolynomial.X j))]
      exact (hpLift _).trans hp
    have hwResidue : pLift ⟨wroot j, hwint j⟩ = 0 :=
      Helpers.binomial_residue_zero m hm (c (MvPolynomial.X j)) (wroot j) (hwroot j)
        pLift.toRingHom hpLiftBase
    have hRootIntegral := Helpers.root_adjoin_integral wroot uroot hwint huint
    obtain ⟨qRoot, hqRoots, hqUnit⟩ :=
      Helpers.root_adjoin_evaluation wroot uroot hwint huint pLift
    have hqRootZero : qRoot ⟨wroot j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩ = 0 :=
      (hqRoots j).trans hwResidue
    have hinjL : Function.Injective (algebraMap R (AlgebraicClosure K)) := by
      intro x y hxy
      apply hinj
      apply (algebraMap K (AlgebraicClosure K)).injective
      simpa only [← IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)] using hxy
    obtain ⟨A, hA, hdom, hnormal, i, σ, qA, W, U, G,
      hσinj, hσi, hσW, hσU, hGi, hGW, hGU, hqG, hvalue⟩ :=
      Helpers.pointed_normal_root_cover n m hm R (AlgebraicClosure K) c hc hinjL ε hε
        wroot hwroot hwint uroot huroot pLift.toRingHom j hwResidue ζ hζ
    letI := hA
    letI : IsDomain A := hdom
    letI : IsIntegrallyClosed A := hnormal
    letI : Algebra R A := i.toAlgebra
    let σA : A →ₐ[R] AlgebraicClosure K := { σ with commutes' := RingHom.congr_fun hσi }
    let GA : A ≃ₐ[R] A := { G with commutes' := hGi }
    let V : A := U * ∏ k, W k ^ α k
    have hV : σA V = f v := by
      change σ (U * ∏ k, W k ^ α k) = f v
      rw [map_mul, map_prod]
      simp_rw [map_pow, hσW]
      rw [hσU]
      exact hvroot.symm
    let z : R := algebraMap k R ζ
    have hGW' (k : Fin n) : GA (W k) =
        if k = j then algebraMap R A z * W k else W k := by
      change G (W k) = _
      rw [hGW]
      have H : c (MvPolynomial.C ζ) = z := c.commutes ζ
      rw [H]
      rfl
    have hGV : GA V = algebraMap R A (z ^ α j) * V :=
      Helpers.monomial_rotation n W U α j z GA hGW' hGU
    have hdz : d v = algebraMap R K z * v := by
      rw [← IsScalarTower.algebraMap_apply k R K]
      exact hd
    have hdPower : (d ^ α j) v = algebraMap R K (z ^ α j) * v := by
      rw [map_pow]
      exact Helpers.aut_pow_generator d v z hdz (α j)
    have hfixed := Helpers.normal_generator_inertia v hgen f σA hσinj V hV
      (z ^ α j) (d ^ α j) hdPower GA hGV p.toRingHom qA
      (fun a => RingHom.congr_fun hqG a) (by
        intro a b hab
        exact (hvalue a (f.mapIntegralClosure b) hab).trans (hpLift b))
    apply Subgroup.zpowers_le.mpr
    intro b
    have H : (d.mapIntegralClosure ^ α j) b = (d ^ α j).mapIntegralClosure b :=
      Subtype.ext (Helpers.integralClosure_pow_apply d (α j) b)
    rw [H]
    exact hfixed b


-- A positive paired exponent check, independent of the general contract.
example : ((6 : ℚ) / 2) ^ 2 = (3 : ℚ) ^ 2 ∧
    ((6 : ℚ) / 3) ^ 2 = (2 : ℚ) ^ 2 := by
  norm_num

-- On the tame double cover x = t², the sign involution fixes x and every
-- evaluation at the ramification point, but moves t.
example :
    let σ := Polynomial.algEquivAevalNegX (R := ℂ)
    σ (Polynomial.X ^ 2) = Polynomial.X ^ 2 ∧
      σ Polynomial.X ≠ Polynomial.X ∧
      ∀ p : Polynomial ℂ, (σ p).eval 0 = p.eval 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp [Polynomial.algEquivAevalNegX_apply]
  · intro h
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    norm_num [Polynomial.algEquivAevalNegX_apply] at hc
  · intro p
    change (p.comp (-Polynomial.X)).eval 0 = p.eval 0
    simp [Polynomial.eval_comp]

end AlgebraicGeometry.TameMonomialCover
