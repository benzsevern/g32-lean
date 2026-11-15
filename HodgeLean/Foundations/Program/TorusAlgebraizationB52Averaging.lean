import HodgeLean.Foundations.Program.TorusAlgebraizationB52DescentAction

noncomputable section
namespace HodgeLean.Foundations.Program

variable {G : Type*} [AddGroup G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]

def b52_averageEnd (ρ : G →+ Additive (Module.End ℂ V)) : Module.End ℂ V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, (ρ g).toMul

theorem b52_averageEnd_invariant (ρ : G →+ Additive (Module.End ℂ V)) (g : G) :
    (ρ g).toMul * b52_averageEnd ρ = b52_averageEnd ρ := by
  unfold b52_averageEnd
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  have hρ : ∀ h, (ρ g).toMul * (ρ h).toMul = (ρ (g + h)).toMul :=
    fun h ↦ (congrArg Additive.toMul (ρ.map_add g h)).symm
  simp_rw [hρ]
  exact Fintype.sum_equiv (Equiv.addLeft g) _ _ (fun h ↦ rfl)

theorem b52_averageEnd_apply_of_fixed (ρ : G →+ Additive (Module.End ℂ V))
    (v : V) (hv : ∀ g, (ρ g).toMul v = v) : b52_averageEnd ρ v = v := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [b52_averageEnd, LinearMap.smul_apply, LinearMap.sum_apply,
    hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem b52_mem_range_averageEnd_iff (ρ : G →+ Additive (Module.End ℂ V)) (v : V) :
    v ∈ LinearMap.range (b52_averageEnd ρ) ↔ ∀ g, (ρ g).toMul v = v := by
  constructor
  · rintro ⟨w, rfl⟩ g
    exact congrArg (fun T : Module.End ℂ V ↦ T w) (b52_averageEnd_invariant ρ g)
  · intro hv
    exact ⟨v, b52_averageEnd_apply_of_fixed ρ v hv⟩

open scoped TensorProduct
variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_mem_dilation_iff_descent_fixed (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    t ∈ Set.range (b52_dilatedSection Λ F hF Q k n) ↔
      ∀ l, b52_descentTranslate Λ F hF Q k n l t.val = t.val := by
  rw [b52_mem_dilatedSection_range_iff Λ F hF Q k n hn t]
  have hne : ∀ l z, b5_factor Λ F hF Q l z ≠ 0 := fun l z ↦
    mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)
  constructor
  · intro ht l
    funext z
    change (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k)⁻¹ *
      t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) = t.val z
    rw [ht, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (hne _ _)), one_mul]
  · intro ht l z
    have hz := congrFun (ht l) z
    change (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k)⁻¹ *
      t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) = t.val z at hz
    have hh := congrArg (fun a : ℂ ↦ b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * a) hz
    simpa only [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (hne _ _)), one_mul] using hh

def b52_descentAverage
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (k n : ℕ) (hn : n ≠ 0) :
    Module.End ℂ (b5_sections Λ F hF Q (k * n ^ 2)) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  exact b52_averageEnd (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle k n hn)

theorem b52_descentAverage_range
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (k n : ℕ) (hn : n ≠ 0) (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    t ∈ LinearMap.range (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn) ↔
      t ∈ Set.range (b52_dilatedSection Λ F hF Q k n) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  change t ∈ LinearMap.range (b52_averageEnd
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle k n hn)) ↔ _
  rw [b52_mem_range_averageEnd_iff, b52_mem_dilation_iff_descent_fixed Λ F hF Q k n hn t]
  constructor
  · intro ht l
    exact congrArg Subtype.val (ht (QuotientAddGroup.mk l))
  · intro ht q
    refine QuotientAddGroup.induction_on q ?_
    intro l
    apply Subtype.ext
    exact ht l

variable
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

theorem b52_descentAverage_dilation (k n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q k) :
    b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn
      (b52_dilatedSection Λ F hF Q k n s) = b52_dilatedSection Λ F hF Q k n s := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  change b52_averageEnd
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle k n hn) _ = _
  apply b52_averageEnd_apply_of_fixed
  apply (b52_mem_range_averageEnd_iff _ _).mp
  exact (b52_descentAverage_range Λ F hF Q hherm himag hcocycle k n hn _).mpr ⟨s, rfl⟩

def b52_descentTrace (k n : ℕ) (hn : n ≠ 0) :
    b5_sections Λ F hF Q (k * n ^ 2) →ₗ[ℂ] b5_sections Λ F hF Q k where
  toFun t := b52_descendedSection Λ F hF Q k n hn
    (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn t) (by
      apply (b52_mem_dilatedSection_range_iff Λ F hF Q k n hn _).mp
      exact (b52_descentAverage_range Λ F hF Q hherm himag hcocycle k n hn _).mp ⟨t, rfl⟩)
  map_add' t u := by
    apply Subtype.ext
    funext z
    change (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn (t + u)).val
      ((n : ℂ)⁻¹ • z) =
      (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn t).val ((n : ℂ)⁻¹ • z) +
      (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn u).val ((n : ℂ)⁻¹ • z)
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c t := by
    apply Subtype.ext
    funext z
    change (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn (c • t)).val
      ((n : ℂ)⁻¹ • z) =
      c * (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn t).val ((n : ℂ)⁻¹ • z)
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem b52_descentTrace_dilation (k n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q k) :
    b52_descentTrace Λ F hF Q hherm himag hcocycle k n hn
      (b52_dilatedSection Λ F hF Q k n s) = s := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  apply Subtype.ext
  funext z
  change (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn
    (b52_dilatedSection Λ F hF Q k n s)).val ((n : ℂ)⁻¹ • z) = s.val z
  rw [b52_descentAverage_dilation]
  change s.val ((n : ℂ) • ((n : ℂ)⁻¹ • z)) = s.val z
  simp only [smul_smul, mul_inv_cancel₀ hn', one_smul]

theorem b52_descentTrace_surjective (k n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (b52_descentTrace Λ F hF Q hherm himag hcocycle k n hn) := by
  intro s
  exact ⟨b52_dilatedSection Λ F hF Q k n s,
    b52_descentTrace_dilation Λ F hF Q hherm himag hcocycle k n hn s⟩

end HodgeLean.Foundations.Program
