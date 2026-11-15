import HodgeLean.Foundations.Program.TorusAlgebraizationB52GridInterpolation
import HodgeLean.Foundations.Program.TorusAlgebraizationB52SeparateDescent

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

include hherm himag hcocycle in
theorem b52_separate_descent_of_grid_delta
    (k a b : ℕ) (hn : a + b ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q ((k * (a + b)) * (a * (a + b))))]
    (s : b5_sections Λ F hF Q (k * (a + b)))
    (t : b5_sections Λ F hF Q ((k * (a + b)) * (a * b)))
    (ht : t.val 0 ≠ 0)
    (hgrid : ∀ l : Λ,
      (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := Λ) (a + b)).range) l ≠ 0 →
        t.val (((a + b : ℕ) : ℂ)⁻¹ • b5_lattice Λ F l) = 0) :
    ∃ N : ℕ, ∃ u : Fin N → b5_sections Λ F hF Q (k * a),
      ∃ v : Fin N → b5_sections Λ F hF Q (k * b),
        ∀ z, s.val z = ∑ i, (u i).val z * (v i).val z := by
  classical
  let n := a + b
  let G := Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite G
  let r : G → Λ := fun q ↦ q.out
  have hr : ∀ q, QuotientAddGroup.mk (r q) = q := fun q ↦ QuotientAddGroup.out_eq' q
  let C : ℂ := (Fintype.card G : ℂ)⁻¹
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hC : C ≠ 0 := inv_ne_zero hcard
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨N, u₀, v₀, huv⟩ := b52_theta_weighted_addition Λ F hF Q (k * n) a b s t
  let u' (i : Fin N) : b5_sections Λ F hF Q ((k * a) * n ^ 2) :=
    ⟨(u₀ i).val, by convert (u₀ i).property using 1 <;> congr 1 <;> dsimp [n] <;> ring⟩
  let v' (i : Fin N) : b5_sections Λ F hF Q ((k * b) * n ^ 2) :=
    ⟨(v₀ i).val, by convert (v₀ i).property using 1 <;> congr 1 <;> dsimp [n] <;> ring⟩
  let u (i : Fin N) := b52_descentTrace Λ F hF Q hherm himag hcocycle (k * a) n hn (u' i)
  let v (i : Fin N) := b52_descentTrace Λ F hF Q hherm himag hcocycle (k * b) n hn (v' i)
  have hsum (z : b5_V Λ F) :
      ∑ i, (u i).val z * (v i).val z = (C * t.val 0) * s.val z := by
    let e (q : G) := (n : ℂ)⁻¹ • (z + b5_lattice Λ F (r q))
    let A (q : G) := (b5_factor Λ F hF Q (r q) z ^ (k * a))⁻¹
    let B (q : G) := (b5_factor Λ F hF Q (r q) z ^ (k * b))⁻¹
    have hu (i : Fin N) : (u i).val z = C * ∑ q, A q * (u₀ i).val (e q) :=
      b52_descentTrace_apply_sum Λ F hF Q hherm himag hcocycle (k * a) n hn r hr (u' i) z
    have hv (i : Fin N) : (v i).val z = C * ∑ q, B q * (v₀ i).val (e q) :=
      b52_descentTrace_apply_sum Λ F hF Q hherm himag hcocycle (k * b) n hn r hr (v' i) z
    have he (q : G) : (a : ℂ) • e q + (b : ℂ) • e q =
        z + b5_lattice Λ F (r q) := by
      rw [← add_smul, ← Nat.cast_add]
      change (n : ℂ) • ((n : ℂ)⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hn', one_smul]
    have hoff (q p : G) (hqp : p ≠ q) : t.val (e q - e p) = 0 := by
      have hne : (QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := Λ) n).range) (r q - r p) ≠ 0 := by
        rw [map_sub]
        change QuotientAddGroup.mk (r q) - QuotientAddGroup.mk (r p) ≠ 0
        rw [hr, hr, sub_ne_zero]
        exact hqp.symm
      have heq : e q - e p = (n : ℂ)⁻¹ • b5_lattice Λ F (r q - r p) := by
        dsimp [e]
        rw [← smul_sub, map_sub]
        congr 1
        abel
      rw [heq]
      exact hgrid _ hne
    have hdiag (q : G) :
        (A q * B q) * (s.val ((a : ℂ) • e q + (b : ℂ) • e q) *
          t.val (e q - e q)) = s.val z * t.val 0 := by
      rw [he, sub_self, s.property.2]
      have hf : b5_factor Λ F hF Q (r q) z ≠ 0 :=
        mul_ne_zero (b5_chi Λ Q (r q)).coe_ne_zero (Complex.exp_ne_zero _)
      dsimp [A, B]
      rw [← mul_inv, ← pow_add, ← Nat.mul_add]
      change (b5_factor Λ F hF Q (r q) z ^ (k * n))⁻¹ *
        (b5_factor Λ F hF Q (r q) z ^ (k * n) * s.val z * t.val 0) = _
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hf), one_mul]
    calc
      _ = C ^ 2 * ∑ i, (∑ q, A q * (u₀ i).val (e q)) *
          (∑ q, B q * (v₀ i).val (e q)) := by
        simp_rw [hu, hv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = C ^ 2 * ∑ q, ∑ p, (A q * B p) *
          (s.val ((a : ℂ) • e q + (b : ℂ) • e p) * t.val (e q - e p)) := by
        rw [b52_sum_products_of_separate_sums]
        simp_rw [← huv]
      _ = C ^ 2 * ∑ q : G, s.val z * t.val 0 := by
        congr 1
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_eq_single q]
        · exact hdiag q
        · intro p _ hp
          rw [hoff q p hp, mul_zero, mul_zero]
        · simp
      _ = (C * t.val 0) * s.val z := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul]
        dsimp [C]
        field_simp
  refine ⟨N, fun i ↦ (C * t.val 0)⁻¹ • u i, v, ?_⟩
  intro z
  change s.val z = ∑ i, ((C * t.val 0)⁻¹ * (u i).val z) * (v i).val z
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hsum, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hC ht), one_mul]

include hherm himag hcocycle in
theorem b52_cubic_successive_multiplication_surjective
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (m : ℕ) (hm : 0 < m)
    [Module.Finite ℂ (b5_sections Λ F hF Q ((3 * (m + 1)) * (m * (m + 1))))] :
    Function.Surjective (b52_sectionMultiplication Λ F hF Q 1 m) := by
  classical
  obtain ⟨θ, hθ⟩ := b52_exists_nonzero_section Λ F hF Q hherm himag hpos hcocycle
  have hr : 2 ≤ (m + 1) * (2 * m - 1) := by
    have h : 1 ≤ 2 * m - 1 := by omega
    nlinarith
  obtain ⟨t₀, ht₀, hgrid₀⟩ := b52_torsion_grid_delta Λ F hF Q hherm hpos θ hθ
    (m + 1) ((m + 1) * (2 * m - 1)) (by omega) hr
  have hdegree : (m + 1) ^ 2 + (m + 1) * (2 * m - 1) =
      (3 * (m + 1)) * (m * 1) := by
    have h : 2 * m - 1 + 1 = 2 * m := by omega
    nlinarith
  let t : b5_sections Λ F hF Q ((3 * (m + 1)) * (m * 1)) :=
    ⟨t₀.val, by rw [← hdegree]; exact t₀.property⟩
  intro s
  let s' : b5_sections Λ F hF Q (3 * (m + 1)) :=
    ⟨s.val, by simpa only [Nat.add_comm] using s.property⟩
  obtain ⟨N, u, v, huv⟩ := b52_separate_descent_of_grid_delta
    Λ F hF Q hherm himag hcocycle 3 m 1 (by omega) s' t ht₀ hgrid₀
  refine ⟨∑ i : Fin N, v i ⊗ₜ[ℂ] u i, ?_⟩
  apply Subtype.ext
  funext z
  simpa [b52_sectionMultiplication, mul_comm] using (huv z).symm

end HodgeLean.Foundations.Program
