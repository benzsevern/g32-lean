import HodgeLean.Port.Markman.Defs
import HodgeLean.Foundations.DualForm
import HodgeLean.RealDefs.F1569

/-!
# Comparison with the Markman Weil model

Markman's statements use the standard `i`-eigenspace convention.  The upstream library's
`productStructure` construction uses its negative, whereas the ported `JX` used by this comparison
already has the standard sign.  The transport through `kdHomologyEquiv` in
`MarkmanTransport.lean` handles the resulting negative action on cohomology explicitly.

Relation to the goal: HC no distance; AV milestone no distance.  This compares the formalization
registered at F-807 (addendum r1427) with the F-1569 statement (F-1721); it proves nothing new
about either statement.
-/

namespace HodgeLean.RealDefs.Compare.Markman

open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
open QuadraticAlgebra
open Module

namespace Port

open WeilClasses

theorem sqrtNeg_sq {d : ℚ} (hd : 0 ≤ d) : WeilClasses.sqrtNeg d ^ 2 = -(d : ℂ) := by
  have h : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  rw [WeilClasses.sqrtNeg, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, h,
    Complex.ofReal_ratCast]
  ring

private theorem sqrtNeg_mul_self (d : ℚ) :
    WeilClasses.sqrtNeg d * WeilClasses.sqrtNeg d = -((max d 0 : ℚ) : ℂ) := by
  rcases le_or_gt 0 d with hd | hd
  · rw [max_eq_left hd, ← sq, sqrtNeg_sq hd]
  · have h : Real.sqrt (d : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast hd.le)
    simp [WeilClasses.sqrtNeg, h, max_eq_right hd.le]

private def quadSubfield (d : ℚ) : Subfield ℂ where
  carrier := {z | ∃ a b : ℚ, z = a + b * WeilClasses.sqrtNeg d}
  mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        refine ⟨a * a' - max d 0 * b * b', a * b' + a' * b, ?_⟩
        have hs := sqrtNeg_mul_self d
        push_cast
        linear_combination ((b : ℂ) * b') * hs
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        exact ⟨a + a', b + b', by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        have h := sqrtNeg_mul_self d
        have hm : 0 ≤ max d 0 := le_max_right _ _
        by_cases hN : a ^ 2 + max d 0 * b ^ 2 = 0
        · have ha : a = 0 := by nlinarith [sq_nonneg a, mul_nonneg hm (sq_nonneg b)]
          have hb : max d 0 * b ^ 2 = 0 := by rw [ha] at hN; simpa using hN
          have hz : ((a : ℂ) + b * WeilClasses.sqrtNeg d) *
              ((a : ℂ) + b * WeilClasses.sqrtNeg d) = 0 := by
            have hb' : ((max d 0 : ℚ) : ℂ) * (b : ℂ) ^ 2 = 0 := by exact_mod_cast hb
            rw [ha]
            push_cast
            linear_combination ((b : ℂ) ^ 2) * h - hb'
          rw [mul_self_eq_zero.mp hz, inv_zero]
          exact ⟨0, 0, by simp⟩
        · refine ⟨a / (a ^ 2 + max d 0 * b ^ 2),
            -b / (a ^ 2 + max d 0 * b ^ 2), ?_⟩
          have hN' : ((a ^ 2 + max d 0 * b ^ 2 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hN
          apply inv_eq_of_mul_eq_one_right
          set D : ℂ := ((a ^ 2 + max d 0 * b ^ 2 : ℚ) : ℂ) with hD
          have e : ((a : ℂ) + b * WeilClasses.sqrtNeg d) *
              (((a / (a ^ 2 + max d 0 * b ^ 2) : ℚ) : ℂ) +
                ((-b / (a ^ 2 + max d 0 * b ^ 2) : ℚ) : ℂ) *
                  WeilClasses.sqrtNeg d) =
              ((a : ℂ) ^ 2 - (b : ℂ) ^ 2 *
                (WeilClasses.sqrtNeg d * WeilClasses.sqrtNeg d)) / D := by
            rw [hD]; push_cast; ring
          rw [e, h, ← div_self hN', hD]
          push_cast
          ring

theorem kd_mem_iff (d : ℚ) {z : ℂ} : z ∈ WeilClasses.Kd d ↔
    ∃ a b : ℚ, z = a + b * WeilClasses.sqrtNeg d := by
  constructor
  · intro hz
    have hle : WeilClasses.Kd d ≤ quadSubfield d := Subfield.closure_le.mpr (by
      rintro _ rfl
      exact ⟨0, 1, by simp⟩)
    exact hle hz
  · rintro ⟨a, b, rfl⟩
    have hs : WeilClasses.sqrtNeg d ∈ WeilClasses.Kd d :=
      Subfield.subset_closure (Set.mem_singleton _)
    exact add_mem (SubfieldClass.ratCast_mem _ a)
      (mul_mem (SubfieldClass.ratCast_mem _ b) hs)

/-- The exact field conversion `ℚ(√−d) ≃ QuadraticAlgebra ℚ (−d) 0`, sending Markman's
chosen `√−d ⊂ ℂ` to `ω`.

Source: the presentations by the generator satisfying `x² = −d`, as in external roadmap §1.2. -/
noncomputable def kdEquiv (d : ℚ) (hd : 0 < d) :
    WeilClasses.Kd d ≃ₐ[ℚ] QuadraticAlgebra ℚ (-d) 0 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r) := ⟨fun r hr => by nlinarith [sq_nonneg r]⟩
  let f : QuadraticAlgebra ℚ (-d) 0 →ₐ[ℚ] WeilClasses.Kd d :=
    QuadraticAlgebra.lift ⟨WeilClasses.Kd.sqrtNeg d, by
      apply Subtype.ext
      simpa [WeilClasses.Kd.sqrtNeg, pow_two, Rat.smul_def] using sqrtNeg_sq hd.le⟩
  exact (AlgEquiv.ofBijective f ⟨f.injective, by
    rintro ⟨z, hz⟩
    obtain ⟨a, b, rfl⟩ := (kd_mem_iff d).mp hz
    refine ⟨(⟨a, b⟩ : QuadraticAlgebra ℚ (-d) 0), ?_⟩
    apply Subtype.ext
    simp [f, QuadraticAlgebra.lift_apply_apply, Rat.smul_def, WeilClasses.Kd.sqrtNeg]⟩).symm

example : kdEquiv 3 (by norm_num) (WeilClasses.Kd.sqrtNeg 3) = QuadraticAlgebra.omega := by
  change (AlgEquiv.ofBijective _ _).symm (WeilClasses.Kd.sqrtNeg 3) = _
  rw [AlgEquiv.symm_apply_eq]
  simp [WeilClasses.Kd.sqrtNeg]

end Port

section Formula

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- Markman's dual-space formula becomes the same alternating form after transport by contraction.

Source: external roadmap §1.2, using `dualForm_contract_contract`. -/
theorem transportedAlternatingForm {w : ⋀[ℚ]^2 V} (hω : IsNondegenerate w)
    (φ ψ : Module.Dual ℚ V) :
    dualForm hω (contract w φ) (contract w ψ) = ψ (contract w φ) :=
  dualForm_contract_contract hω φ ψ

example {w : ⋀[ℚ]^2 V} (hω : IsNondegenerate w) (φ ψ : Module.Dual ℚ V) :
    dualForm hω (contract w φ) (contract w ψ) = ψ (contract w φ) :=
  transportedAlternatingForm hω φ ψ

end Formula

section DeterminantClass

variable {a : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
variable {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ a 0) W]
  [Module.Finite (QuadraticAlgebra ℚ a 0) W]

/-- A nonzero rational Gram determinant represents `[c]` precisely when it is `c` times a
quadratic-field norm.  This is the quotient-group step in the conversion from Markman's
existential `DiscIs` predicate to `HermitianForm.detClass`.

Source: external roadmap §1.2, steps 1–2; the definition of a quotient by the norm subgroup. -/
theorem detClass_eq_iff_exists_norm {h : W →ₗ⋆[QuadraticAlgebra ℚ a 0]
    W →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0}
    (hh : h.IsSymm) (hn : h.Nondegenerate)
    {c : ℚ} (hc : c ≠ 0) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (e : Basis ι (QuadraticAlgebra ℚ a 0) W) :
    detClass h hh hn =
        ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0)) ↔
      ∃ z : QuadraticAlgebra ℚ a 0, z ≠ 0 ∧
        gramDetℚ h e = c * QuadraticAlgebra.norm z := by
  rw [detClass_eq hh hn e, QuotientGroup.eq_iff_div_mem]
  constructor
  · intro hmem
    obtain ⟨z, hz⟩ := mem_normSubgroup_iff.mp hmem
    refine ⟨z, ?_, ?_⟩
    · rintro rfl
      have hunit : ((↑(Units.mk0 (gramDetℚ h e) (gramDetℚ_ne_zero hh hn e) /
          Units.mk0 c hc) : ℚ)) ≠ 0 := Units.ne_zero _
      exact hunit (by simpa using hz.symm)
    · change QuadraticAlgebra.norm z = gramDetℚ h e / c at hz
      field_simp at hz ⊢
      simpa [mul_comm] using hz.symm
  · rintro ⟨z, hz0, hz⟩
    apply mem_normSubgroup_iff.mpr
    refine ⟨z, ?_⟩
    change QuadraticAlgebra.norm z = gramDetℚ h e / c
    field_simp
    simpa [mul_comm] using hz.symm

/-- The sign introduced by carrying Markman's transposed action from `H₁` to `H¹` does not
change the determinant class in even `K`-dimension.

Source: external roadmap §1.2, step 4; `detClass_neg`. -/
theorem detClass_neg_of_even {h : W →ₗ⋆[QuadraticAlgebra ℚ a 0]
    W →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0}
    (hh : h.IsSymm) (hn : h.Nondegenerate)
    (heven : Even (finrank (QuadraticAlgebra ℚ a 0) W)) :
    detClass (-h) (isSymm_neg hh) (nondegenerate_neg hn) = detClass h hh hn := by
  rw [detClass_neg hh hn]
  obtain ⟨n, hn⟩ := heven
  rw [hn, ← two_mul, pow_mul]
  simp

example {h : W →ₗ⋆[QuadraticAlgebra ℚ a 0]
    W →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0}
    (hh : h.IsSymm) (hn : h.Nondegenerate) {c : ℚ} (hc : c ≠ 0)
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (e : Basis ι (QuadraticAlgebra ℚ a 0) W) :
    detClass h hh hn =
        ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0)) ↔
      ∃ z : QuadraticAlgebra ℚ a 0, z ≠ 0 ∧
        gramDetℚ h e = c * QuadraticAlgebra.norm z :=
  detClass_eq_iff_exists_norm hh hn hc ι e

example {h : W →ₗ⋆[QuadraticAlgebra ℚ a 0]
    W →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0}
    (hh : h.IsSymm) (hn : h.Nondegenerate)
    (heven : Even (finrank (QuadraticAlgebra ℚ a 0) W)) :
    detClass (-h) (isSymm_neg hh) (nondegenerate_neg hn) = detClass h hh hn :=
  detClass_neg_of_even hh hn heven

end DeterminantClass

section Families

open WeilClasses

/-- The shape of Markman's discriminant-`−1` family conclusion in the linear-algebra model:
the Hodge–Weil plane is contained in the chosen abstract algebraic classes.

Source: Markman, *Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds*,
Theorem 1.5.1, as encoded by the formalization registered at F-807 (addendum r1427).

Relation to the goal: HC no distance; AV milestone no distance. -/
def MarkmanMinusOneFamilyStatement (Z : CycleClasses) : Prop :=
  ∀ (A : AbVar (2 * 3)) (X : PolarizedWeilType A 3),
    X.DiscIs (-1) → X.toWeilType.HW ≤ Z.alg (2 * 3) A.J

example (Z : CycleClasses) : MarkmanMinusOneFamilyStatement Z ↔
    ∀ (A : AbVar (2 * 3)) (X : PolarizedWeilType A 3),
      X.DiscIs (-1) → X.toWeilType.HW ≤ Z.alg (2 * 3) A.J := Iff.rfl

/-- The two repositories state family predicates in different ambient categories: Markman's
coordinate model and F-1569's actual smooth projective group objects. This pair deliberately makes
no implication between them.

Source: external roadmap §3, items 2–3; F-1569 (F-1721).

Relation to the goal: HC no distance; AV milestone no distance. -/
def FamilyStatementsSideBySide
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X)
    (Z : CycleClasses) : Prop :=
  MarkmanMinusOneFamilyStatement Z ∧ F1569StatementFor cup

example
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X)
    (Z : CycleClasses) : FamilyStatementsSideBySide cup Z ↔
      MarkmanMinusOneFamilyStatement Z ∧ F1569StatementFor cup := Iff.rfl

end Families

section Falsification

/-- In `K`-dimension two, scaling the form by `2` gives the same determinant class.

Source: the explicit `d = 3` examples in `Foundations/WeilHermitian.lean`. -/
theorem sameClass_d3_dim2 :
    weilDetClass ((2 : ℚ) • exE₄) exJ₄' (skew_smul 2 exE₄_skew) (isAlt_smul 2 exE₄_isAlt)
        (nondegenerate_smul two_ne_zero exE₄_nondegenerate) =
      weilDetClass exE₄ exJ₄' exE₄_skew exE₄_isAlt exE₄_nondegenerate :=
  weilDetClass_two_exE₄

example :
    weilDetClass ((2 : ℚ) • exE₄) exJ₄' (skew_smul 2 exE₄_skew) (isAlt_smul 2 exE₄_isAlt)
        (nondegenerate_smul two_ne_zero exE₄_nondegenerate) =
      weilDetClass exE₄ exJ₄' exE₄_skew exE₄_isAlt exE₄_nondegenerate := sameClass_d3_dim2

/-- In `K`-dimension one, scaling the form by `2` changes the determinant class.

Source: the explicit `d = 3` counterexample in `Foundations/WeilHermitian.lean`. -/
theorem differentClass_d3_dim1 :
    weilDetClass ((2 : ℚ) • exE) exJ' (skew_smul 2 exE_skew) (isAlt_smul 2 exE_isAlt)
        (nondegenerate_smul two_ne_zero exE_nondegenerate) ≠
      weilDetClass exE exJ' exE_skew exE_isAlt exE_nondegenerate :=
  weilDetClass_two_exE_ne

example :
    weilDetClass ((2 : ℚ) • exE) exJ' (skew_smul 2 exE_skew) (isAlt_smul 2 exE_isAlt)
        (nondegenerate_smul two_ne_zero exE_nondegenerate) ≠
      weilDetClass exE exJ' exE_skew exE_isAlt exE_nondegenerate := differentClass_d3_dim1

end Falsification

end HodgeLean.RealDefs.Compare.Markman
