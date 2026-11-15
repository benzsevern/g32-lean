import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6Defs

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
open HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Adapters
local instance : IsCommMonObj E :=
  isCommMonObj_of_complexSelfProductIntegral E (complexSelfProductIntegral_of_isIntegral E)

/-- Positivity of the standard elliptic form.
Source: Birkenhake--Lange, second edition, section 1.3. -/
theorem bh6_elliptic_positive_aux (τ : ℂ) (hτ : 0 < τ.im) :
    (bh6_ellipticForm τ).IsPositiveDefinite := by
  intro z hz
  change 0 < (star z * z / (τ.im : ℂ)).re
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.div_re]
  convert div_pos (Complex.normSq_pos.mpr hz) hτ using 1 <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero] <;>
    field_simp [ne_of_gt hτ] <;>
    rw [Complex.normSq_ofReal] <;> ring

/-- The imaginary part on two integer combinations of the periods is the determinant.
Source: Birkenhake--Lange, second edition, section 1.3. -/
theorem bh6_elliptic_integral_aux (τ : ℂ) (hτ : 0 < τ.im) (a b c d : ℤ) :
    (bh6_ellipticForm τ).imaginary ((a : ℂ) + τ * b) ((c : ℂ) + τ * d) =
      ((a * d - b * c : ℤ) : ℝ) := by
  simp only [HermitianForm.imaginary, bh6_ellipticForm, Complex.div_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    Int.cast_sub, Int.cast_mul]
  field_simp [Complex.normSq_ofReal, ne_of_gt hτ]
  rw [Complex.normSq_ofReal]
  ring

/-- Choose oriented normalized periods for the fixed cubic's exponential lattice.
This is a lattice-coordinate statement; no Hermitian form or polarization is an input.
Source: Birkenhake--Lange, second edition, section 1.1; `abelianLatticeBasis`. -/
theorem bh6_elliptic_coordinates_aux :
    ∃ (τ : ℂ) (q : (Fin (dim E.left) → ℂ) ≃ₗ[ℂ] ℂ)
      (a b : abelianPeriodLattice E →+ ℤ),
      0 < τ.im ∧ Function.Surjective (fun l ↦ (a l, b l)) ∧
      ∀ l : abelianPeriodLattice E, q l = (a l : ℂ) + τ * b l := by
  let e : Fin (dim E.left) ≃ Fin 1 := Equiv.cast (congrArg Fin E_dim)
  have hd : 2 * dim E.left = 2 := by simp [E_dim]
  let f : Fin (2 * dim E.left) ≃ Fin 2 := Equiv.cast (congrArg Fin hd)
  let B := (abelianLatticeBasis E).reindex f
  let R := (abelianRealBasis E).reindex f
  have hRB (i : Fin 2) : R i = (B i : Fin (dim E.left) → ℂ) := by
    simp [R, B, abelianRealBasis_apply]
  let w₀ : ℂ := (B 0 : Fin (dim E.left) → ℂ) (e.symm 0)
  let w₁ : ℂ := (B 1 : Fin (dim E.left) → ℂ) (e.symm 0)
  have hw₀ : w₀ ≠ 0 := by
    intro h
    have hz : (B 0 : Fin (dim E.left) → ℂ) = 0 := by
      funext i
      have hi : i = e.symm 0 := e.injective (Subsingleton.elim _ _)
      subst i
      exact h
    exact (B.ne_zero 0) (Subtype.ext hz)
  have hratio : (w₁ / w₀).im ≠ 0 := by
    intro h
    have heq : w₁ = (w₁ / w₀).re • w₀ := by
      rw [Complex.real_smul]
      calc
        w₁ = (w₁ / w₀) * w₀ := by field_simp
        _ = ((w₁ / w₀).re : ℂ) * w₀ := by
          congr 1
          apply Complex.ext <;> simp [h]
    have heq' : (B 1 : Fin (dim E.left) → ℂ) =
        (w₁ / w₀).re • (B 0 : Fin (dim E.left) → ℂ) := by
      funext i
      have hi : i = e.symm 0 := e.injective (Subsingleton.elim _ _)
      subst i
      exact heq
    have heqR : R 1 = (w₁ / w₀).re • R 0 := by
      rw [hRB, hRB]
      exact heq'
    have h := congrArg (fun v => R.repr v (1 : Fin 2)) heqR
    simp at h
  let qe : (Fin (dim E.left) → ℂ) ≃ₗ[ℂ] ℂ :=
    (LinearEquiv.funCongrLeft ℂ ℂ e.symm).trans (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
  let qm : ℂ ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective (LinearMap.mulRight ℂ w₀⁻¹) (by
    constructor
    · intro x y h
      have h' := congrArg (fun z => z * w₀) h
      simpa only [LinearMap.mulRight_apply, inv_mul_cancel₀ hw₀, mul_assoc, one_mul, mul_one] using h'
    · intro x
      refine ⟨x * w₀, ?_⟩
      simp [hw₀])
  let q := qe.trans qm
  let c₀ : abelianPeriodLattice E →+ ℤ := (B.coord 0).toAddMonoidHom
  let c₁ : abelianPeriodLattice E →+ ℤ := (B.coord 1).toAddMonoidHom
  by_cases hp : 0 < (w₁ / w₀).im
  · refine ⟨w₁ / w₀, q, c₀, c₁, hp, ?_, ?_⟩
    · rintro ⟨x, y⟩
      refine ⟨B.equivFun.symm (fun i => if i = 0 then x else y), ?_⟩
      simp [c₀, c₁]
    · intro l
      have hl : ((B.repr l 0 : ℤ) : ℂ) * w₀ + ((B.repr l 1 : ℤ) : ℂ) * w₁ =
          (l : Fin (dim E.left) → ℂ) (e.symm 0) := by
        have hx := congrArg (fun v : abelianPeriodLattice E =>
          (v : Fin (dim E.left) → ℂ) (e.symm 0)) (B.sum_repr l)
        simp only [Fin.sum_univ_two] at hx
        change (B.repr l 0) • w₀ + (B.repr l 1) • w₁ = _ at hx
        rw [← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ] at hx
        simpa only [smul_eq_mul] using hx
      rw [← B.sum_repr l]
      simp [q, qe, qm, c₀, c₁]
      change _ * w₀⁻¹ = _
      field_simp [hw₀]
      rw [← hl]
      ring
  · have hn : 0 < -(w₁ / w₀).im := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hratio)
    refine ⟨-(w₁ / w₀), q, c₀, -c₁, by simpa using hn, ?_, ?_⟩
    · rintro ⟨x, y⟩
      refine ⟨B.equivFun.symm (fun i => if i = 0 then x else -y), ?_⟩
      simp [c₀, c₁]
    · intro l
      have hl : ((B.repr l 0 : ℤ) : ℂ) * w₀ + ((B.repr l 1 : ℤ) : ℂ) * w₁ =
          (l : Fin (dim E.left) → ℂ) (e.symm 0) := by
        have hx := congrArg (fun v : abelianPeriodLattice E =>
          (v : Fin (dim E.left) → ℂ) (e.symm 0)) (B.sum_repr l)
        simp only [Fin.sum_univ_two] at hx
        change (B.repr l 0) • w₀ + (B.repr l 1) • w₁ = _ at hx
        rw [← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ] at hx
        simpa only [smul_eq_mul] using hx
      rw [← B.sum_repr l]
      simp [q, qe, qm, c₀, c₁]
      change _ * w₀⁻¹ = _
      field_simp [hw₀]
      rw [← hl]
      ring

/-- The exponential covering space of the square is the product of the two factor covers.
Compatibility is asserted with the actual embedded period lattices, before any forms are chosen.
Source: Birkenhake--Lange, second edition, section 1.2, analytic representations of products. -/
theorem bh6_product_coordinates_aux :
    ∃ (q : (Fin (dim (g3_power E 2).left) → ℂ) ≃ₗ[ℂ]
        (Fin 2 → (Fin (dim E.left) → ℂ)))
      (t : abelianPeriodLattice (g3_power E 2) →+ (Fin 2 → abelianPeriodLattice E)),
      (∀ (l : abelianPeriodLattice (g3_power E 2)) (i : Fin 2),
        q l i = (t l i : Fin (dim E.left) → ℂ)) ∧
      ∀ v, AlgebraicGeometry.Point.map (g3_proj E 2 0) (abelianExp (g3_power E 2) v) =
        abelianExp E (q v 0) := by
  letI : IsCommMonObj (g3_power E 2) := spec_g3_isCommMonObj_power E 2
  letI : CommGroup (ComplexPoint E) := complexPointCommGroup E
    (complexSelfProductIntegral_of_isIntegral E)
  letI : CommGroup (ComplexPoint (g3_power E 2)) := complexPointCommGroup (g3_power E 2)
    (complexSelfProductIntegral_of_isIntegral (g3_power E 2))
  letI (i : Fin 2) : IsMonHom (g3_proj E 2 i) := spec_g3_isMonHom_proj E 2 i
  letI (i : Fin 2) : IsMonHom (g3_incl E 2 i) := spec_g3_isMonHom_incl E 2 i
  choose A hA using fun i : Fin 2 ↦ spec_abelianHom_analyticRepresentation (g3_proj E 2 i)
  choose B hB using fun i : Fin 2 ↦ spec_abelianHom_analyticRepresentation (g3_incl E 2 i)
  let Q : (Fin (dim (g3_power E 2).left) → ℂ) →ₗ[ℂ]
      (Fin 2 → (Fin (dim E.left) → ℂ)) := LinearMap.pi A
  let S : (Fin 2 → (Fin (dim E.left) → ℂ)) →ₗ[ℂ]
      (Fin (dim (g3_power E 2).left) → ℂ) :=
    (B 0).comp (LinearMap.proj 0) + (B 1).comp (LinearMap.proj 1)
  have hSQ : S.comp Q = LinearMap.id := by
    apply spec_analyticRepresentation_unique (g3_power E 2)
    intro v
    apply Additive.toMul.injective
    change Additive.toMul (complexExponential (g3_power E 2) _
      (B 0 (A 0 v) + B 1 (A 1 v))) = Additive.toMul (complexExponential (g3_power E 2) _ v)
    have hadd := (complexExponentialHom (g3_power E 2) (dim (g3_power E 2).left)).map_add
      (B 0 (A 0 v)) (B 1 (A 1 v))
    have hadd' := congrArg Additive.toMul hadd
    simp only [toMul_add] at hadd'
    change Additive.toMul (complexExponential (g3_power E 2) _
      (B 0 (A 0 v) + B 1 (A 1 v))) =
        Additive.toMul (complexExponential (g3_power E 2) _ (B 0 (A 0 v))) *
          Additive.toMul (complexExponential (g3_power E 2) _ (B 1 (A 1 v))) at hadd'
    rw [hadd', hB, hB, hA, hA]
    rw [← AlgebraicGeometry.Point.map_comp_apply, ← AlgebraicGeometry.Point.map_comp_apply]
    have hp := spec_g3_prod_proj_incl E 2
    let x := Additive.toMul (complexExponential (g3_power E 2) _ v)
    calc
      AlgebraicGeometry.Point.map (g3_proj E 2 0 ≫ g3_incl E 2 0) x *
          AlgebraicGeometry.Point.map (g3_proj E 2 1 ≫ g3_incl E 2 1) x =
        AlgebraicGeometry.Point.map
          ((g3_proj E 2 0 ≫ g3_incl E 2 0) *
            (g3_proj E 2 1 ≫ g3_incl E 2 1)) x := (MonObj.comp_mul _ _ _).symm
      _ = x := by
        have hpx := congrArg (fun f ↦ AlgebraicGeometry.Point.map f x) hp
        simpa only [Fin.prod_univ_two, AlgebraicGeometry.Point.map_id] using hpx
  have hQinj : Function.Injective Q := by
    intro v w hvw
    have := congrArg S hvw
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hSQ,
      LinearMap.id_apply, LinearMap.id_apply] at this
    exact this
  have hfin : Module.finrank ℂ (Fin (dim (g3_power E 2).left) → ℂ) =
      Module.finrank ℂ (Fin 2 → (Fin (dim E.left) → ℂ)) := by
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype, spec_g3link_dim_eq]
    simp only [Module.finrank_fin_fun, Fin.sum_univ_two]
    omega
  have hQsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hQinj
  let q := LinearEquiv.ofBijective Q ⟨hQinj, hQsurj⟩
  have hperiod (l : abelianPeriodLattice (g3_power E 2)) (i : Fin 2) :
      q l i ∈ abelianPeriodLattice E := by
    rw [show q (l : Fin (dim (g3_power E 2).left) → ℂ) i = A i l from rfl]
    change complexExponential E (dim E.left) (A i l) = 0
    rw [← complexExponential_zero E (dim E.left)]
    apply Additive.toMul.injective
    rw [hA i]
    have hl := l.property
    change complexExponential (g3_power E 2) (dim (g3_power E 2).left) l = 0 at hl
    rw [hl, complexExponential_zero]
    exact MonObj.one_comp (g3_proj E 2 i)
  let t : abelianPeriodLattice (g3_power E 2) →+
      (Fin 2 → abelianPeriodLattice E) :=
    { toFun := fun l i ↦ ⟨q l i, hperiod l i⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        exact congrFun q.map_zero i
      map_add' := fun l m ↦ by
        funext i
        apply Subtype.ext
        exact congrFun (q.map_add l m) i }
  refine ⟨q, t, ?_, ?_⟩
  · intro l i
    rfl
  · intro v
    exact (hA 0 v).symm

/-- Positivity survives transport along an injective complex linear map.
Source: Birkenhake--Lange, second edition, section 1.3. -/
theorem bh6_pull_positive (n : ℕ) (q : (Fin n → ℂ) ≃ₗ[ℂ] ℂ)
    (H : HermitianForm (V := ℂ)) (hH : H.IsPositiveDefinite) :
    (bh6_pullForm n q.toLinearMap H).IsPositiveDefinite := by
  intro v hv
  exact hH (q v) (fun h ↦ hv (q.injective (h.trans (q.map_zero.symm))))

/-- Two positive forms give a positive product after a linear equivalence.
Source: Birkenhake--Lange, second edition, section 4.3. -/
theorem bh6_product_positive_aux (n m : ℕ)
    (q : (Fin m → ℂ) ≃ₗ[ℂ] (Fin 2 → (Fin n → ℂ)))
    (H : HermitianForm (V := Fin n → ℂ)) (hH : H.IsPositiveDefinite) :
    (bh6_productForm n m q.toLinearMap H).IsPositiveDefinite := by
  intro v hv
  have hqv : q v ≠ 0 := fun h ↦ hv (q.injective (h.trans q.map_zero.symm))
  have hnonneg (w : Fin n → ℂ) : 0 ≤ (H.toFun w w).re := by
    by_cases hw : w = 0
    · subst w
      have hz : H.toFun 0 0 = 0 := by
        have ha := H.add_left 0 0 0
        have hb := congrArg (fun z ↦ z - H.toFun 0 0) ha
        simpa only [zero_add, add_sub_cancel_left, sub_self] using hb.symm
      rw [hz]
      exact le_rfl
    · exact (hH w hw).le
  change 0 < (H.toFun (q v 0) (q v 0) + H.toFun (q v 1) (q v 1)).re
  rw [Complex.add_re]
  by_cases h0 : q v 0 = 0
  · have h1 : q v 1 ≠ 0 := by
      intro h1
      apply hqv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    exact add_pos_of_nonneg_of_pos (hnonneg _) (hH _ h1)
  · exact add_pos_of_pos_of_nonneg (hH _ h0) (hnonneg _)

/-- Integer values of a Hermitian imaginary part assemble into a biadditive integer form.
Source: Birkenhake--Lange, second edition, section 2.1; integer-cast injectivity. -/
theorem bh6_integral_lift (n : ℕ) (L : Submodule ℤ (Fin n → ℂ))
    (H : HermitianForm (V := Fin n → ℂ))
    (h : ∀ l m : L, ∃ k : ℤ, H.imaginary l m = k) :
    ∃ F : L →+ L →+ ℤ, ∀ l m : L, (F l m : ℝ) = H.imaginary l m := by
  have hfl : ∀ l m : L, (⌊H.imaginary l m⌋ : ℝ) = H.imaginary l m := by
    intro l m
    obtain ⟨k, hk⟩ := h l m
    rw [hk, Int.floor_intCast]
  refine ⟨AddMonoidHom.mk' (fun l ↦ AddMonoidHom.mk' (fun m ↦ ⌊H.imaginary l m⌋)
    (fun m m' ↦ ?_)) (fun l l' ↦ ?_), hfl⟩
  · apply Int.cast_injective (α := ℝ)
    rw [Int.cast_add, hfl, hfl, hfl]
    simp only [Submodule.coe_add, HermitianForm.imaginary, H.add_right, Complex.add_im]
  · ext m
    apply Int.cast_injective (α := ℝ)
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
    rw [Int.cast_add, hfl, hfl, hfl]
    simp only [Submodule.coe_add, HermitianForm.imaginary, H.add_left, Complex.add_im]

/-- Assemble the dimension-one witness using normalized periods and the existing semicharacter.
Source: Birkenhake--Lange, second edition, sections 1.3 and 2.2. -/
theorem bh6_witness_positive_dim1 :
    ∃ A : bh4_AHData E, A.H.IsPositiveDefinite := by
  obtain ⟨τ, q, a, b, hτ, _, hq⟩ := bh6_elliptic_coordinates_aux
  let H := bh6_pullForm (dim E.left) q.toLinearMap (bh6_ellipticForm τ)
  have hi : ∀ l m : abelianPeriodLattice E, ∃ k : ℤ, H.imaginary l m = k := by
    intro l m
    refine ⟨a l * b m - b l * a m, ?_⟩
    change (bh6_ellipticForm τ).imaginary (q l) (q m) = _
    rw [hq, hq]
    exact bh6_elliptic_integral_aux τ hτ _ _ _ _
  obtain ⟨F, hF⟩ := bh6_integral_lift _ _ H hi
  obtain ⟨χ, hχ⟩ := spec_exists_semicharacterOfX E H F hF
  exact ⟨⟨H, F, hF, χ, hχ⟩,
    bh6_pull_positive _ q _ (bh6_elliptic_positive_aux τ hτ)⟩

/-- Assemble the product witness from dimension one and product-cover transport.
Source: Birkenhake--Lange, second edition, section 4.3. -/
theorem bh6_witness_positive_dim2 :
    ∃ A : bh4_AHData (g3_power E 2), A.H.IsPositiveDefinite := by
  obtain ⟨A, hA⟩ := bh6_witness_positive_dim1
  obtain ⟨q, t, ht, _⟩ := bh6_product_coordinates_aux
  let H := bh6_productForm _ _ q.toLinearMap A.H
  have hi : ∀ l m : abelianPeriodLattice (g3_power E 2), ∃ k : ℤ,
      H.imaginary l m = k := by
    intro l m
    refine ⟨A.E (t l 0) (t m 0) + A.E (t l 1) (t m 1), ?_⟩
    change (A.H.toFun (q l 0) (q m 0) + A.H.toFun (q l 1) (q m 1)).im = _
    simp only [Complex.add_im, ht, Int.cast_add]
    exact congrArg₂ (· + ·) (A.integral _ _).symm (A.integral _ _).symm
  obtain ⟨F, hF⟩ := bh6_integral_lift _ _ H hi
  obtain ⟨χ, hχ⟩ := spec_exists_semicharacterOfX (g3_power E 2) H F hF
  exact ⟨⟨H, F, hF, χ, hχ⟩, bh6_product_positive_aux _ _ q A.H hA⟩

end HodgeLean.Adapters
