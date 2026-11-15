import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

noncomputable section

open HodgeLean.Papers MulAction

namespace HodgeLean.Foundations.Program

theorem g32p_top_local_character {G : Type*} [Group G] {m : ℕ}
    (χ : (⊤ : Subgroup G) →* Multiplicative (ZMod m)) (g : G)
    (q : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ (⊤ : Subgroup G)))) :
    χ (papersLocalMonodromy ⊤ g q) = χ ⟨g, Subgroup.mem_top g⟩ := by
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have h1 : Function.minimalPeriod (g • ·) q.out = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (Subsingleton.elim _ _)
  let x : (⊤ : Subgroup G) := ⟨q.out.out, Subgroup.mem_top _⟩
  change χ ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out, _⟩ = _
  rw [h1, pow_one]
  change χ (x⁻¹ * ⟨g, Subgroup.mem_top g⟩ * x) = _
  simp only [map_mul, map_inv]
  rw [mul_comm (χ x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem g32p_top_exponents {G : Type*} [Group G] [Finite G] {m : ℕ}
    (χ : (⊤ : Subgroup G) →* Multiplicative (ZMod m)) (g : G) :
    papersExps ⊤ χ g =
      ({Multiplicative.toAdd (χ ⟨g, Subgroup.mem_top g⟩)} : Multiset (ZMod m)).filter
        (· ≠ 0) := by
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  let q₀ : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ (⊤ : Subgroup G))) :=
    Quotient.mk'' (1 : G)
  have hsub : ∀ q : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ (⊤ : Subgroup G))),
      q = q₀ := by
    intro q
    induction q using Quotient.inductionOn' with
    | h c => exact congrArg _ (Subsingleton.elim _ _)
  unfold papersExps
  simp only [g32p_top_local_character, Multiset.map_const', Finset.card_val, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, Nat.card_eq_one_iff_exists.mpr ⟨q₀, hsub⟩,
    Multiset.replicate_one]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem g32p_generator_determinant (i : Fin 4) :
    Matrix.det (b4b_toMatrix (b4b_generators i)) =
      ![g32h_omega, g32h_omega ^ 2, 1, 1] i := by
  fin_cases i <;>
    norm_num [b4b_toMatrix, b4b_generators, g32R1, g32R2, g32X, g32Y,
      Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_zero, Fin.sum_univ_succ,
      Matrix.submatrix, Fin.succAbove] <;>
    first
    | (right; trivial)
    | (right; papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)
    | (papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)

theorem g32p_omega_primitive : IsPrimitiveRoot g32h_omega 3 := by
  exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

def g32p_omegaUnit : ℂˣ := g32p_omega_primitive.toRootsOfUnity.val

theorem g32p_omegaUnit_val : (g32p_omegaUnit : ℂ) = g32h_omega := by
  simp [g32p_omegaUnit, IsPrimitiveRoot.toRootsOfUnity]

theorem g32p_omegaUnit_primitive : IsPrimitiveRoot g32p_omegaUnit 3 := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [g32p_omegaUnit_val]
  exact g32p_omega_primitive

def g32p_determinant : g32p_G →* ℂˣ :=
  (Matrix.detMonoidHom.comp b4b_toMatrix).toHomUnits

theorem g32p_determinant_val (g : g32p_G) :
    (g32p_determinant g : ℂ) = Matrix.det (b4b_toMatrix g) := rfl


theorem g32p_determinant_cube (g : g32p_G) : g32p_determinant g ^ 3 = 1 := by
  have hm : ∀ a ∈ g32h_G, Matrix.det a ^ 3 = 1 := by
    intro a ha
    induction ha using Submonoid.closure_induction with
    | mem a ha =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        have h0 := g32p_generator_determinant 0
        have h1 := g32p_generator_determinant 1
        have h2 := g32p_generator_determinant 2
        have h3 := g32p_generator_determinant 3
        change Matrix.det (g32R1 g32h_omega) = g32h_omega at h0
        change Matrix.det (g32R2 g32h_omega) = g32h_omega ^ 2 at h1
        change Matrix.det (g32X g32h_omega) = 1 at h2
        change Matrix.det (g32Y g32h_omega) = 1 at h3
        rcases ha with rfl | rfl | rfl | rfl
        · rw [h0]; exact g32p_omega_primitive.pow_eq_one
        · rw [h1, ← pow_mul, Nat.mul_comm 2 3, pow_mul,
            g32p_omega_primitive.pow_eq_one, one_pow]
        · rw [h2, one_pow]
        · rw [h3, one_pow]
    | one => simp
    | mul a b ha hb iha ihb => rw [Matrix.det_mul, mul_pow, iha, ihb, mul_one]
  apply Units.ext
  change Matrix.det (b4b_toMatrix g) ^ 3 = 1
  exact hm _ g.property

theorem g32p_determinant_mem_powers (g : g32p_G) :
    g32p_determinant g ∈ Subgroup.zpowers g32p_omegaUnit := by
  rw [g32p_omegaUnit_primitive.zpowers_eq]
  exact (mem_rootsOfUnity 3 _).mpr (g32p_determinant_cube g)

def g32p_determinantToPowers : g32p_G →* Subgroup.zpowers g32p_omegaUnit where
  toFun g := ⟨g32p_determinant g, g32p_determinant_mem_powers g⟩
  map_one' := Subtype.ext (map_one g32p_determinant)
  map_mul' g h := Subtype.ext (map_mul g32p_determinant g h)

def g32p_determinantExponent : g32p_G →* Multiplicative (ZMod 3) :=
  g32p_omegaUnit_primitive.zmodEquivZPowers.symm.toAddMonoidHom.toMultiplicativeRight.comp
    g32p_determinantToPowers

theorem g32p_determinantExponent_of_pow (g : g32p_G) (n : ℕ)
    (h : g32p_determinant g = g32p_omegaUnit ^ n) :
    g32p_determinantExponent g = Multiplicative.ofAdd (n : ZMod 3) := by
  apply Multiplicative.toAdd.injective
  change g32p_omegaUnit_primitive.zmodEquivZPowers.symm
    (Additive.ofMul (g32p_determinantToPowers g)) = (n : ZMod 3)
  have hs : g32p_determinantToPowers g =
      (⟨g32p_omegaUnit ^ n, ⟨(n : ℤ), by simp⟩⟩ : Subgroup.zpowers g32p_omegaUnit) :=
    Subtype.ext h
  rw [hs]
  exact g32p_omegaUnit_primitive.zmodEquivZPowers_symm_apply_pow n

theorem g32p_generator_determinantExponent (i : Fin 4) :
    g32p_determinantExponent (b4b_generators i) =
      Multiplicative.ofAdd (![1, 2, 0, 0] i : ZMod 3) := by
  have h (j : Fin 4) (n : ℕ)
      (hn : Matrix.det (b4b_toMatrix (b4b_generators j)) = g32h_omega ^ n) :
      g32p_determinantExponent (b4b_generators j) = Multiplicative.ofAdd (n : ZMod 3) := by
    apply g32p_determinantExponent_of_pow
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, g32p_determinant_val, g32p_omegaUnit_val] using hn
  fin_cases i
  · exact h 0 1 (by simpa using g32p_generator_determinant 0)
  · exact h 1 2 (by simpa using g32p_generator_determinant 1)
  · exact h 2 0 (by simpa using g32p_generator_determinant 2)
  · exact h 3 0 (by simpa using g32p_generator_determinant 3)


def g32p_determinantSupplier : g32p_Supplier where
  H := ⊤
  m := 3
  three_le := by decide
  χ := g32p_determinantExponent.comp (⊤ : Subgroup g32p_G).subtype
  surjective := by
    intro a
    refine ⟨⟨b4b_generators 0 ^ (Multiplicative.toAdd a).val, Subgroup.mem_top _⟩, ?_⟩
    change g32p_determinantExponent (b4b_generators 0 ^ (Multiplicative.toAdd a).val) = a
    apply Multiplicative.toAdd.injective
    rw [map_pow, g32p_generator_determinantExponent, toAdd_pow]
    simp

theorem g32p_determinantSupplier_order : Nat.card g32p_determinantSupplier.H = 155520 := by
  change Nat.card (⊤ : Subgroup g32p_G) = _
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup g32p_G) ≃* g32p_G).toEquiv]
  exact (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
    HurwitzPrymRex_g32_ncard

theorem g32p_class_determinantExponent (j : Fin 13) :
    g32p_determinantExponent (g32p_classDatum j) =
      Multiplicative.ofAdd (if j.val < 6 then (1 : ZMod 3) else if j.val < 12 then 2 else 0) := by
  have h0 := g32p_generator_determinantExponent 0
  have h1 := g32p_generator_determinantExponent 1
  have h2 := g32p_generator_determinantExponent 2
  fin_cases j <;> first
  | exact h0
  | exact h1
  | (change g32p_determinantExponent (b4b_generators 2 * b4b_generators 2) =
        Multiplicative.ofAdd (0 : ZMod 3)
     rw [map_mul, h2]
     rfl)

theorem g32p_determinantSupplier_exponents :
    (g32p_exponents g32p_determinantSupplier).Perm
      (List.replicate 6 1 ++ List.replicate 6 2) := by
  classical
  apply Multiset.coe_eq_coe.mp
  simp only [g32p_exponents, papersExpsList, Multiset.coe_toList]
  have ht : papersExpsTuple g32p_determinantSupplier.H g32p_determinantSupplier.χ
      g32p_classList =
      (List.replicate 6 (1 : ZMod 3) ++ List.replicate 6 (2 : ZMod 3) : Multiset (ZMod 3)) := by
    change papersExpsTuple ⊤
      (g32p_determinantExponent.comp (⊤ : Subgroup g32p_G).subtype) g32p_classList = _
    have htwo : (2 : ZMod 3) ≠ 0 := by decide
    simp [papersExpsTuple, g32p_classList, List.ofFn_succ, g32p_top_exponents,
      g32p_class_determinantExponent, List.replicate_succ, Multiset.filter_singleton, htwo] <;> decide +kernel
  rw [ht]
  decide


theorem g32p_determinantSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 1 ∧ r.m = g32p_determinantSupplier.m ∧
      r.orderH = Nat.card g32p_determinantSupplier.H ∧
      (g32p_exponents g32p_determinantSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨1, -1, 155520, 3, 0, 12, 10, some 1, [(1, 6), (2, 6)], .S⟩,
    ?_, rfl, rfl, g32p_determinantSupplier_order.symm, ?_⟩
  · exact List.mem_cons_self
  · exact g32p_determinantSupplier_exponents

end HodgeLean.Foundations.Program

end
end
