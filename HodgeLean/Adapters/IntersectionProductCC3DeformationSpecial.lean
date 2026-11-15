import HodgeLean.Adapters.NormalConeDefs

noncomputable section
namespace HodgeLean.Adapters

open LaurentPolynomial

/-- Reflection of polynomial degrees across zero. -/
def a3b1_negNatHom : ℕ →+ ℤ where
  toFun n := -(n : ℤ)
  map_zero' := by simp
  map_add' m n := by push_cast; abel

lemma a3b1_negNatHom_injective : Function.Injective a3b1_negNatHom := by
  intro m n h
  change -(m : ℤ) = -(n : ℤ) at h
  exact_mod_cast neg_injective h

/-- A polynomial read with its degree `n` in Laurent degree `-n`. -/
def a3b1_reflectPolynomial (R : Type*) [CommRing R] :
    Polynomial R →+* LaurentPolynomial R :=
  (AddMonoidAlgebra.mapDomainRingHom R a3b1_negNatHom).comp
    (Polynomial.toFinsuppIso R).toRingHom

lemma a3b1_reflectPolynomial_coeff
    (R : Type*) [CommRing R] (f : Polynomial R) (n : ℕ) :
    (a3b1_reflectPolynomial R f).coeff (-(n : ℤ)) = f.coeff n := by
  change (f.toFinsupp.mapDomain a3b1_negNatHom).coeff (a3b1_negNatHom n) =
    f.toFinsupp.coeff n
  simpa [AddMonoidAlgebra.mapDomain] using
    Finsupp.mapDomain_apply_of_injective a3b1_negNatHom_injective f.toFinsupp.coeff n

lemma a3b1_reflectPolynomial_mem_deformation
    (R : Type*) [CommRing R] (I : Ideal R) (f : reesAlgebra I) :
    a3b1_reflectPolynomial R f.1 ∈ a3cc3_deformationAlgebra I := by
  rw [a3cc3_mem_deformationAlgebra_iff]
  intro z
  cases z with
  | ofNat n => simp
  | negSucc n =>
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega,
        a3b1_reflectPolynomial_coeff]
      simpa using ((mem_reesAlgebra_iff I f.1).mp f.2 (n + 1))

/-- Reflection embeds the ordinary Rees algebra into the nonpositive part of the deformation. -/
def a3b1_reesToDeformation (R : Type*) [CommRing R] (I : Ideal R) :
    reesAlgebra I →+* a3cc3_deformationAlgebra I :=
  ((a3b1_reflectPolynomial R).comp (reesAlgebra I).val.toRingHom).codRestrict
    (a3cc3_deformationAlgebra I) (fun f => a3b1_reflectPolynomial_mem_deformation R I f)

lemma a3b1_reesToDeformation_coe
    (R : Type*) [CommRing R] (I : Ideal R) (f : reesAlgebra I) :
    (a3b1_reesToDeformation R I f : LaurentPolynomial R) =
      a3b1_reflectPolynomial R f.1 := rfl

lemma a3b1_coefficient_reflection_vanishes
    (R : Type*) [CommRing R] (I : Ideal R) (r : I) :
    Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I})
      (a3b1_reesToDeformation R I (algebraMap R (reesAlgebra I) r.1)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Ideal.mem_span_singleton]
  refine ⟨a3b1_fractionGenerator R I r, ?_⟩
  apply Subtype.ext
  rw [a3b1_reesToDeformation_coe]
  change a3b1_reflectPolynomial R (Polynomial.C r.1) =
    T 1 * (C r.1 * T (-1))
  rw [show a3b1_reflectPolynomial R (Polynomial.C r.1) = C r.1 by
    change AddMonoidAlgebra.mapDomain a3b1_negNatHom
      ((Polynomial.toFinsuppIso R) (Polynomial.C r.1)) = C r.1
    simp [a3b1_negNatHom]]
  change C r.1 = T 1 * (C r.1 * T (-1))
  rw [mul_comm (T 1), mul_assoc, ← T_add]
  simp

/-- The reflected Rees map after killing the coefficient ideal. -/
def a3b1_normalConeToSpecialFiber (R : Type*) [CommRing R] (I : Ideal R) :
    a3cc3_normalConeRing I →+* a3cc3_specialFiber I :=
  Ideal.Quotient.lift (I.map (algebraMap R (reesAlgebra I)))
    ((Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I})).comp
      (a3b1_reesToDeformation R I)) <| by
    change I.map (algebraMap R (reesAlgebra I)) ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I})).comp
        (a3b1_reesToDeformation R I))
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact a3b1_coefficient_reflection_vanishes R I ⟨r, hr⟩

lemma a3b1_normalConeToSpecialFiber_monomial_one
    (R : Type*) [CommRing R] (I : Ideal R) (a : I) :
    a3b1_normalConeToSpecialFiber R I
        (a3b1_coneMonomial R I 1 ⟨a.1, by simpa using a.2⟩) =
      Ideal.Quotient.mk _ (a3b1_fractionGenerator R I a) := by
  rw [a3b1_coneMonomial, a3b1_normalConeToSpecialFiber, Ideal.Quotient.lift_mk]
  apply congrArg (Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I}))
  apply Subtype.ext
  change a3b1_reflectPolynomial R (Polynomial.monomial 1 a.1) = C a.1 * T (-1)
  rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one, map_mul]
  rw [show a3b1_reflectPolynomial R (Polynomial.C a.1) = C a.1 by
    change AddMonoidAlgebra.mapDomain a3b1_negNatHom
      ((Polynomial.toFinsuppIso R) (Polynomial.C a.1)) = C a.1
    simp [a3b1_negNatHom]]
  rw [show a3b1_reflectPolynomial R Polynomial.X = T (-1) by
    change AddMonoidAlgebra.mapDomain a3b1_negNatHom
      ((Polynomial.toFinsuppIso R) Polynomial.X) = T (-1)
    change AddMonoidAlgebra.mapDomain a3b1_negNatHom
      (AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single (-1) 1
    rw [AddMonoidAlgebra.mapDomain_single]
    rfl]

lemma a3b1_normalConeToSpecialFiber_monomial_zero
    (R : Type*) [CommRing R] (I : Ideal R) (r : R) :
    a3b1_normalConeToSpecialFiber R I
        (Ideal.Quotient.mk _
          (⟨Polynomial.C r, by
            rw [mem_reesAlgebra_iff]
            intro i
            by_cases hi : i = 0
            · subst i; simp
            · simp [Polynomial.coeff_C, hi]⟩ : reesAlgebra I)) =
      Ideal.Quotient.mk _ (algebraMap R (a3cc3_deformationAlgebra I) r) := by
  rw [a3b1_normalConeToSpecialFiber, Ideal.Quotient.lift_mk]
  apply congrArg (Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I}))
  apply Subtype.ext
  rw [a3b1_reesToDeformation_coe]
  change a3b1_reflectPolynomial R (Polynomial.C r) = C r
  change AddMonoidAlgebra.mapDomain a3b1_negNatHom
    ((Polynomial.toFinsuppIso R) (Polynomial.C r)) = C r
  simp [a3b1_negNatHom]

lemma a3b1_normalConeToSpecialFiber_injective
    (R : Type*) [CommRing R] (I : Ideal R) :
    Function.Injective (a3b1_normalConeToSpecialFiber R I) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · intro x hx
    refine Quotient.inductionOn x ?_ hx
    intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [mem_map_algebraMap_reesAlgebra_iff]
    intro n
    change Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I})
      (a3b1_reesToDeformation R I f) = 0 at hf
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hf
    obtain ⟨d, hd⟩ := hf
    have hd' := congrArg (fun z : LaurentPolynomial R => z.coeff (-(n : ℤ)))
      (congrArg Subtype.val hd)
    rw [a3b1_reesToDeformation_coe, a3b1_reflectPolynomial_coeff] at hd'
    rw [Subalgebra.coe_mul] at hd'
    rw [show (a3cc3_parameter I : LaurentPolynomial R) = T 1 by rfl] at hd'
    rw [mul_comm (T 1) d.1] at hd'
    change f.1.coeff n =
      (d.1 * AddMonoidAlgebra.single (1 : ℤ) 1).coeff (-(n : ℤ)) at hd'
    rw [AddMonoidAlgebra.coeff_mul_single_apply] at hd'
    simp only [mul_one] at hd'
    have hmem := (a3cc3_mem_deformationAlgebra_iff I d.1).mp d.2 (-((n + 1 : ℕ) : ℤ))
    rw [show d.1.coeff (-((n + 1 : ℕ) : ℤ)) = f.1.coeff n by
      rw [show -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) by omega]
      simpa [add_comm] using hd'.symm] at hmem
    simpa using hmem
  · exact bot_le

lemma a3b1_normalConeToSpecialFiber_surjective
    (R : Type*) [CommRing R] (I : Ideal R) :
    Function.Surjective (a3b1_normalConeToSpecialFiber R I) := by
  intro y
  refine Quotient.inductionOn y ?_
  intro d
  change ∃ x, a3b1_normalConeToSpecialFiber R I x = Ideal.Quotient.mk _ d
  apply Algebra.adjoin_induction (p := fun z hz =>
    ∃ x, a3b1_normalConeToSpecialFiber R I x =
      Ideal.Quotient.mk _ (⟨z, hz⟩ : a3cc3_deformationAlgebra I))
  · intro z hz
    rcases hz with hz | ⟨a, ha, rfl⟩
    · rw [Set.mem_singleton_iff] at hz
      subst z
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span (Set.mem_singleton _)
    · let a' : I := ⟨a, ha⟩
      refine ⟨a3b1_coneMonomial R I 1 ⟨a, by simpa using ha⟩, ?_⟩
      exact a3b1_normalConeToSpecialFiber_monomial_one R I a'
  · intro r
    refine ⟨Ideal.Quotient.mk _
      (⟨Polynomial.C r, by
        rw [mem_reesAlgebra_iff]
        intro i
        by_cases hi : i = 0
        · subst i; simp
        · simp [Polynomial.coeff_C, hi]⟩ : reesAlgebra I), ?_⟩
    exact a3b1_normalConeToSpecialFiber_monomial_zero R I r
  · intro x y hx hy ihx ihy
    obtain ⟨x', hx'⟩ := ihx
    obtain ⟨y', hy'⟩ := ihy
    refine ⟨x' + y', ?_⟩
    rw [map_add, hx', hy']
    rfl
  · intro x y hx hy ihx ihy
    obtain ⟨x', hx'⟩ := ihx
    obtain ⟨y', hy'⟩ := ihy
    refine ⟨x' * y', ?_⟩
    rw [map_mul, hx', hy']
    rfl

def a3b1_normalConeToSpecialFiberAlgHom
    (R : Type*) [CommRing R] (I : Ideal R) :
    a3cc3_normalConeRing I →ₐ[R] a3cc3_specialFiber I where
  __ := a3b1_normalConeToSpecialFiber R I
  commutes' r := by
    change a3b1_normalConeToSpecialFiber R I
      (Ideal.Quotient.mk _ (algebraMap R (reesAlgebra I) r)) =
        Ideal.Quotient.mk _ (algebraMap R (a3cc3_deformationAlgebra I) r)
    rw [a3b1_normalConeToSpecialFiber, Ideal.Quotient.lift_mk]
    apply congrArg (Ideal.Quotient.mk (Ideal.span {a3cc3_parameter I}))
    apply Subtype.ext
    rw [a3b1_reesToDeformation_coe]
    change a3b1_reflectPolynomial R (Polynomial.C r) = C r
    change AddMonoidAlgebra.mapDomain a3b1_negNatHom
      ((Polynomial.toFinsuppIso R) (Polynomial.C r)) = C r
    simp [a3b1_negNatHom]

def a3b1_specialFiberAlgEquiv
    (R : Type*) [CommRing R] (I : Ideal R) :
    a3cc3_specialFiber I ≃ₐ[R] a3cc3_normalConeRing I :=
  (AlgEquiv.ofBijective (a3b1_normalConeToSpecialFiberAlgHom R I)
    ⟨a3b1_normalConeToSpecialFiber_injective R I,
      a3b1_normalConeToSpecialFiber_surjective R I⟩).symm

end HodgeLean.Adapters
