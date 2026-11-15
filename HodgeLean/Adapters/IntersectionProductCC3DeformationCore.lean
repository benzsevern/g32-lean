import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.ReesAlgebra

/-! # Affine algebra for diagonal deformation

The parameter is `t`; the special fibre is at zero and the original fibre at one.
The seven theorem bodies specify the first stage of the route note.
-/

noncomputable section

open LaurentPolynomial

namespace HodgeLean.Adapters

universe u
variable {R : Type u} [CommRing R]

/-- The extended Rees algebra `R[t, I/t]` inside the Laurent polynomial ring.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3cc3_deformationAlgebra (I : Ideal R) : Subalgebra R (LaurentPolynomial R) :=
  Algebra.adjoin R ({T 1} ∪ (fun a : R => C a * T (-1)) '' (I : Set R))

private def a3cc3_coefficientAlgebra (I : Ideal R) :
    Subalgebra R (LaurentPolynomial R) where
  carrier := {f | ∀ n : ℤ, f.coeff n ∈ I ^ (-n).toNat}
  zero_mem' n := Ideal.zero_mem _
  one_mem' n := by
    rw [AddMonoidAlgebra.one_def]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst n
      simp
    · exact Ideal.zero_mem _
  add_mem' hf hg n := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Ideal.add_mem _ (hf n) (hg n)
  mul_mem' {f g} hf hg n := by
    rw [AddMonoidAlgebra.coeff_mul]
    change (∑ j ∈ f.coeff.support, ∑ k ∈ g.coeff.support,
      if j + k = n then f.coeff j * g.coeff k else 0) ∈ I ^ (-n).toNat
    apply Ideal.sum_mem
    intro j hj
    apply Ideal.sum_mem
    intro k hk
    split_ifs with h
    · subst n
      apply Ideal.pow_le_pow_right
      show (-(j + k)).toNat ≤ (-j).toNat + (-k).toNat
      omega
      rw [pow_add]
      exact Ideal.mul_mem_mul (hf j) (hg k)
    · exact Ideal.zero_mem _
  algebraMap_mem' r n := by
    rw [LaurentPolynomial.algebraMap_apply, C_apply]
    split_ifs with h
    · subst n
      simp
    · exact Ideal.zero_mem _

private lemma a3cc3_negativeMonomial_mem (I : Ideal R) (k : ℕ) (a : R)
    (ha : a ∈ I ^ k) :
    C a * T (-(k : ℤ)) ∈ a3cc3_deformationAlgebra I := by
  induction k generalizing a with
  | zero =>
      simpa using (a3cc3_deformationAlgebra I).algebraMap_mem a
  | succ k ih =>
      rw [pow_succ'] at ha
      induction ha using Submodule.mul_induction_on' with
      | mem_mul_mem r hr s hs =>
          have hr' : C r * T (-1) ∈ a3cc3_deformationAlgebra I :=
            Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_image_of_mem _ hr))
          have hs' := ih s hs
          have hprod := (a3cc3_deformationAlgebra I).mul_mem hr' hs'
          rw [mul_mul_mul_comm, ← map_mul, ← T_add] at hprod
          simpa only [Int.natCast_succ, Int.neg_add, add_comm] using hprod
      | add x hx y hy hmx hmy =>
          simpa [map_add, add_mul] using
            (a3cc3_deformationAlgebra I).add_mem hmx hmy

private lemma a3cc3_monomial_mem (I : Ideal R) (n : ℤ) (a : R)
    (ha : a ∈ I ^ (-n).toNat) :
    C a * T n ∈ a3cc3_deformationAlgebra I := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hT : T (k : ℤ) ∈ a3cc3_deformationAlgebra I := by
      simpa using (a3cc3_deformationAlgebra I).pow_mem
        (Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_singleton _))) k
    exact (a3cc3_deformationAlgebra I).mul_mem
      ((a3cc3_deformationAlgebra I).algebraMap_mem a) hT
  · have hn' : n = -((-n).toNat : ℤ) := by omega
    rw [hn']
    exact a3cc3_negativeMonomial_mem I _ a ha

private lemma a3cc3_deformationAlgebra_eq_coefficientAlgebra (I : Ideal R) :
    a3cc3_deformationAlgebra I = a3cc3_coefficientAlgebra I := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x (rfl | ⟨a, ha, rfl⟩)
    · intro n
      change (Finsupp.single 1 1) n ∈ I ^ (-n).toNat
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst n
        simp
      · exact Ideal.zero_mem _
    · intro n
      change (C a * T (-1)).coeff n ∈ I ^ (-n).toNat
      rw [← single_eq_C_mul_T]
      change (Finsupp.single (-1) a) n ∈ I ^ (-n).toNat
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst n
        simpa using ha
      · exact Ideal.zero_mem _
  · intro f hf
    rw [show f = f.coeff.sum (fun n a ↦ C a * T n) by
      ext m
      simp [← single_eq_C_mul_T]]
    apply Subalgebra.sum_mem
    intro n hn
    exact a3cc3_monomial_mem I n (f.coeff n) (hf n)

/-- The deformation parameter as an element of the extended Rees algebra.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3cc3_parameter (I : Ideal R) : a3cc3_deformationAlgebra I :=
  ⟨T 1, Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_singleton _))⟩

/-- Evaluation on the fibre over one.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3cc3_evalOne (I : Ideal R) : a3cc3_deformationAlgebra I →+* R :=
  (LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)).comp
    (a3cc3_deformationAlgebra I).val

/-- The zero fibre as a quotient by the actual deformation parameter.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
abbrev a3cc3_specialFiber (I : Ideal R) :=
  a3cc3_deformationAlgebra I ⧸ Ideal.span {a3cc3_parameter I}

/-- The ordinary Rees quotient modeling the normal cone ring.
Source: Fulton, *Intersection Theory*, second edition, §4.1 and §5.1. -/
abbrev a3cc3_normalConeRing (I : Ideal R) :=
  reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))

/-- Negative Laurent degrees record powers of the ideal; nonnegative degrees are unrestricted.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
theorem a3cc3_mem_deformationAlgebra_iff (I : Ideal R) (f : LaurentPolynomial R) :
    f ∈ a3cc3_deformationAlgebra I ↔ ∀ n : ℤ, f.coeff n ∈ I ^ (-n).toNat := by
  rw [a3cc3_deformationAlgebra_eq_coefficientAlgebra]
  rfl

/-- The parameter acts injectively without a domain assumption on the coefficient ring.
Source: Fulton, *Intersection Theory*, second edition, §5.1, extended Rees ring description. -/
theorem a3cc3_parameter_mul_injective (I : Ideal R) :
    Function.Injective (fun f : a3cc3_deformationAlgebra I => a3cc3_parameter I * f) := by
  intro f g h
  apply Subtype.ext
  apply (isUnit_T (R := R) 1).mul_left_cancel
  exact congrArg Subtype.val h

/-- Finitely many ideal generators and the parameter generate the deformation algebra.
Source: Fulton, *Intersection Theory*, second edition, §5.1, affine construction. -/
theorem a3cc3_deformationAlgebra_finiteType [IsNoetherianRing R] (I : Ideal R) :
    Algebra.FiniteType R (a3cc3_deformationAlgebra I) := by
  classical
  let phi : R →ₗ[R] LaurentPolynomial R :=
    { toFun := fun a ↦ C a * T (-1)
      map_add' := fun a b ↦ by simp [add_mul]
      map_smul' := fun r a ↦ by simp [Algebra.smul_def, mul_assoc] }
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  have himage : (phi '' (I : Set R)) = (Submodule.map phi I : Set (LaurentPolynomial R)) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  rw [show a3cc3_deformationAlgebra I =
      Algebra.adjoin R ({T 1} ∪ phi '' (I : Set R)) by rfl]
  rw [himage, ← hs, Submodule.map_span, Algebra.adjoin_union, Algebra.adjoin_span,
    ← Algebra.adjoin_union]
  exact Algebra.FiniteType.adjoin_of_finite
    (Set.Finite.union (Set.finite_singleton _) (s.finite_toSet.image phi))

/-- Powers of the parameter clear denominators into the deformation algebra.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
theorem a3cc3_deformation_clear_denominators (I : Ideal R) (f : LaurentPolynomial R) :
    ∃ (n : ℕ) (g : a3cc3_deformationAlgebra I),
      f * T (n : ℤ) = (g : LaurentPolynomial R) := by
  obtain ⟨n, p, hp⟩ := f.exists_T_pow
  refine ⟨n, ⟨p.toLaurent, (a3cc3_mem_deformationAlgebra_iff I _).mpr ?_⟩, hp.symm⟩
  intro m
  by_cases hm : 0 ≤ m
  · have : (-m).toNat = 0 := by omega
    rw [this, pow_zero]
    simpa using (show p.toLaurent.coeff m ∈ (⊤ : Ideal R) by simp)
  · have hcoeff : p.toLaurent.coeff m = 0 := by
      by_contra hne
      have hsupp : m ∈ p.toLaurent.coeff.support := (Finsupp.mem_support_iff).2 hne
      rw [support_coeff_toLaurent] at hsupp
      obtain ⟨k, hk, hkm⟩ := Finset.mem_map.mp hsupp
      have hm0 : (0 : ℤ) ≤ m := hkm ▸ Int.natCast_nonneg k
      omega
    rw [hcoeff]
    exact Ideal.zero_mem _

/-- The original affine ring is the image of evaluation at one.
Source: Fulton, *Intersection Theory*, second edition, §5.1, generic fibre description. -/
theorem a3cc3_evalOne_surjective (I : Ideal R) :
    Function.Surjective (a3cc3_evalOne I) := by
  intro r
  refine ⟨⟨C r, (a3cc3_deformationAlgebra I).algebraMap_mem r⟩, ?_⟩
  simp [a3cc3_evalOne]

/-- The fibre over one has exactly the parameter-minus-one relation.
Source: Fulton, *Intersection Theory*, second edition, §5.1, generic fibre description. -/
theorem a3cc3_evalOne_ker (I : Ideal R) :
    RingHom.ker (a3cc3_evalOne I) = Ideal.span {a3cc3_parameter I - 1} := by
  apply le_antisymm
  · intro f hf
    let J : Ideal (a3cc3_deformationAlgebra I) := Ideal.span {a3cc3_parameter I - 1}
    let q := Ideal.Quotient.mk J
    have ht : q (a3cc3_parameter I) = q 1 := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have hall : ∀ (x : LaurentPolynomial R) (hx : x ∈ a3cc3_deformationAlgebra I),
        q ⟨x, hx⟩ = algebraMap R ((a3cc3_deformationAlgebra I) ⧸ J)
          (a3cc3_evalOne I ⟨x, hx⟩) := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
          rcases hx with rfl | ⟨a, ha, rfl⟩
          · change q (a3cc3_parameter I) = _
            simpa [a3cc3_evalOne] using ht
          · let z : a3cc3_deformationAlgebra I :=
              ⟨C a * T (-1), Algebra.subset_adjoin
                (Set.mem_union_right _ (Set.mem_image_of_mem _ ha))⟩
            have hz : a3cc3_parameter I * z = algebraMap R _ a := by
              apply Subtype.ext
              simp [a3cc3_parameter, z, mul_mul_mul_comm, ← T_add]
            change q z = _
            calc
              q z = q (a3cc3_parameter I) * q z := by rw [ht]; simp
              _ = q (a3cc3_parameter I * z) := (map_mul q _ _).symm
              _ = q (algebraMap R _ a) := congrArg q hz
              _ = algebraMap R ((a3cc3_deformationAlgebra I) ⧸ J) a := rfl
              _ = algebraMap R ((a3cc3_deformationAlgebra I) ⧸ J)
                  (a3cc3_evalOne I z) := by simp [a3cc3_evalOne, z]
      | algebraMap r =>
          calc
            q ⟨algebraMap R (LaurentPolynomial R) r, _⟩ =
                algebraMap R ((a3cc3_deformationAlgebra I) ⧸ J) r := by
              exact Ideal.Quotient.mk_algebraMap R J r
            _ = algebraMap R ((a3cc3_deformationAlgebra I) ⧸ J)
                (a3cc3_evalOne I ⟨algebraMap R (LaurentPolynomial R) r, _⟩) := by
              simp [a3cc3_evalOne]
      | add x y hx hy ihx ihy =>
          let sx : a3cc3_deformationAlgebra I := ⟨x, hx⟩
          let sy : a3cc3_deformationAlgebra I := ⟨y, hy⟩
          calc
            q ⟨x + y, _⟩ = q sx + q sy := by
              rw [← map_add]
              congr 1
            _ = algebraMap R _ (a3cc3_evalOne I sx) +
                algebraMap R _ (a3cc3_evalOne I sy) := congrArg₂ (· + ·) ihx ihy
            _ = algebraMap R _ (a3cc3_evalOne I (sx + sy)) := by simp
            _ = algebraMap R _ (a3cc3_evalOne I ⟨x + y, _⟩) := by congr 2
      | mul x y hx hy ihx ihy =>
          let sx : a3cc3_deformationAlgebra I := ⟨x, hx⟩
          let sy : a3cc3_deformationAlgebra I := ⟨y, hy⟩
          calc
            q ⟨x * y, _⟩ = q sx * q sy := by
              rw [← map_mul]
              congr 1
            _ = algebraMap R _ (a3cc3_evalOne I sx) *
                algebraMap R _ (a3cc3_evalOne I sy) := congrArg₂ (· * ·) ihx ihy
            _ = algebraMap R _ (a3cc3_evalOne I (sx * sy)) := by simp
            _ = algebraMap R _ (a3cc3_evalOne I ⟨x * y, _⟩) := by congr 2
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [hall f.1 f.2, hf]
    simp
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = a3cc3_parameter I - 1)
    simp [RingHom.mem_ker, a3cc3_evalOne, a3cc3_parameter]

end HodgeLean.Adapters
