import HodgeLean.Foundations.Program.RigidStartingSystemDefs

/-! # Pullback domains and action conventions

The domains retain the ordinary point at infinity and the three apparent poles.
The word evaluator supplies finite data for a later component computation.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The thirteen geometric branch points before normalization.
Source: G32 v0.16, §5.2, Lemma surj and the displayed P₅ and P₋₇. -/
def b65s_branch : Set (OnePoint ℂ) :=
  {p | ∃ z : ℂ, p = (z : OnePoint ℂ) ∧
    (z = 0 ∨ b65r_P 5 z = 0 ∨ b65r_P (-7) z = 0)}

example : ((0 : ℂ) : OnePoint ℂ) ∈ b65s_branch := ⟨0, rfl, Or.inl rfl⟩
example : OnePoint.infty ∉ b65s_branch := by
  rintro ⟨z, h, _⟩
  exact OnePoint.coe_ne_infty z h.symm

/-- The sphere with only the genuine branch points removed.
Source: G32 v0.16, §5.2, Lemma surj. -/
def b65s_sphere : Set (OnePoint ℂ) := b65s_branchᶜ

example : OnePoint.infty ∈ b65s_sphere := by
  rintro ⟨z, h, _⟩
  exact OnePoint.coe_ne_infty z h.symm

/-- Plane domain on which the printed coefficient is analytic.
Source: G32 v0.16, §5.4, including the apparent poles 3, 1 and −2. -/
def b65s_regular : Set ℂ :=
  {z | z ≠ 0 ∧ z ≠ 3 ∧ z ≠ 1 ∧ z ≠ -2 ∧
    b65r_P 5 z ≠ 0 ∧ b65r_P (-7) z ≠ 0}

example : (2 : ℂ) ∈ b65s_regular := by
  norm_num [b65s_regular, b65r_P]

/-- Inclusion used to compare sphere monodromy with printed plane transport.
Source: OnePoint.continuous_coe and G32 v0.16, §5.2. -/
def b65s_inclusion : C(b65s_regular, b65s_sphere) where
  toFun z := ⟨(z.val : OnePoint ℂ), by
    rintro ⟨w, hw, h⟩
    have he : z.val = w := OnePoint.coe_injective hw
    subst w
    rcases h with h | h | h
    · exact z.property.1 h
    · exact z.property.2.2.2.2.1 h
    · exact z.property.2.2.2.2.2 h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact OnePoint.continuous_coe.comp continuous_subtype_val

example (z : b65s_regular) : (b65s_inclusion z : OnePoint ℂ) = (z.val : OnePoint ℂ) := rfl

/-- Finite chart of the normalization sending a to zero, b to one, and zero to infinity.
Source: G32 v0.16, §3.1, normalization modulo PGL₂; cross-ratio formula. -/
def b65s_normalize (a b z : ℂ) : ℂ := (z - a) * b / (z * (b - a))

example (a b : ℂ) : b65s_normalize a b a = 0 := by simp [b65s_normalize]
example : b65s_normalize 1 2 2 = 1 := by norm_num [b65s_normalize]

/-- Inverse-unop converts opposite multiplication to ordinary multiplication.
Source: Mathlib MulOpposite.unop_mul and mul_inv_rev; mr_root_op_reverse_prod. -/
def b65s_unopInv (G : Type*) [Group G] : Gᵐᵒᵖ →* G where
  toFun g := (MulOpposite.unop g)⁻¹
  map_one' := inv_one
  map_mul' g h := by simp only [MulOpposite.unop_mul, mul_inv_rev]

example (G : Type*) [Group G] (g : G) : b65s_unopInv G (MulOpposite.op g) = g⁻¹ := rfl

/-- Column action of the fixed faithful matrix realization.
Source: G32 v0.16, Appendix A, and Matrix.mulVecLin_mul. -/
def b65s_action : b4b_Group →* ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) where
  toFun g := b65r_operator (b4b_toMatrix g)
  map_one' := by
    rw [map_one]
    ext v i
    simp [b65r_operator]
  map_mul' g h := by
    rw [map_mul]
    ext v i
    exact congrFun (Matrix.mulVec_mulVec v (b4b_toMatrix g) (b4b_toMatrix h)).symm i

example (g : b4b_Group) : (b65s_action.toHomUnits g).val =
    b65r_operator (b4b_toMatrix g) := rfl

/-- Column representation associated to an opposite-valued covering representation.
Source: mr_curve multiplication convention; inverse-unop followed by the column action. -/
def b65s_column {Γ : Type*} [Group Γ] (κ : Γ →* b4b_Groupᵐᵒᵖ) :
    Γ →* ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ :=
  b65s_action.toHomUnits.comp ((b65s_unopInv b4b_Group).comp κ)

example {Γ : Type*} [Group Γ] (κ : Γ →* b4b_Groupᵐᵒᵖ) (c : Γ) :
    (b65s_column κ c).val = b65r_operator (b4b_toMatrix ((MulOpposite.unop (κ c))⁻¹)) := rfl

/-- The ordinary product-one tuple obtained by reversing and inverting covering values.
Source: mr_root_op_reverse_prod; chronological versus categorical loop multiplication. -/
def b65s_columnRoot : Fin 13 → b4b_Group := fun i ↦ (b4b_root i.rev)⁻¹

example : b65s_columnRoot 0 = (b4b_root 12)⁻¹ := rfl

/-- Data for one signed adjacent braid or a simultaneous conjugation.
Source: Völklein, Groups as Galois Groups, Chapters 9–10; b4_braid. -/
inductive b65s_Move where
  | positive (i : Fin 12)
  | negative (i : Fin 12)
  | conjugate (g : b4b_Group)

example : b65s_Move := .positive 0

/-- Evaluation of a signed elementary move, with negative generator the inverse Hurwitz move.
Source: Völklein, Chapters 9–10, (a,b) ↦ (aba⁻¹,a) and (b,b⁻¹ab). -/
def b65s_step (m : b65s_Move) (t : Fin 13 → b4b_Group) : Fin 13 → b4b_Group :=
  match m with
  | .positive i => b4_braid i.castSucc i.succ t
  | .negative i => Function.update (t ∘ Equiv.swap i.castSucc i.succ) i.succ
      ((t i.succ)⁻¹ * t i.castSucc * t i.succ)
  | .conjugate g => b4_conjTuple g t

example (t : Fin 13 → b4b_Group) : b65s_step (.positive 0) t 0 =
    t 0 * t 1 * (t 0)⁻¹ := by simp [b65s_step, b4_braid]

/-- A finite word acts in list order; the empty word acts identically.
Source: Völklein, Chapters 9–10, composition of Hurwitz moves. -/
def b65s_word (w : List b65s_Move) (t : Fin 13 → b4b_Group) : Fin 13 → b4b_Group :=
  w.foldl (fun s m ↦ b65s_step m s) t

example (t : Fin 13 → b4b_Group) : b65s_word [] t = t := rfl

example : 0 < Module.finrank ℂ (Fin 4 → ℂ) := by simp
example : b4b_root 0 ≠ 1 := by
  intro h
  have ho := b63_root_order (0 : Fin 13)
  rw [h, orderOf_one] at ho
  norm_num at ho

end HodgeLean.Foundations.Program
