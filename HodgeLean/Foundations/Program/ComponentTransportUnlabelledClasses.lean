import HodgeLean.Foundations.Program.BraidBridgesDefs
import HodgeLean.Papers.PapersG32Certificates

/-! # Unlabelled chain: determinant classes of the three monodromy tuples
Finite data for the class comparison of review hlean-rev-ctpu (2026-11-05). `P`, `M` and `S`
stand for the conjugacy classes of `r₁`, `r₁⁻¹` and `x²` in `b4b_Group`; their determinants
`ω`, `ω²` and `1` are distinct, so the determinant of an element of one of these classes
names its class. The kernel checks the determinant of every entry of `b4b_root`,
`b65s_columnRoot` and the inverted certified tuple `(b65b_initial i)⁻¹`, and the permutation
facts on the finite class sequences.

Not claimed here: membership of each entry in the named conjugacy class (the review derives it
from the explicit words), and any relation between the class-matching permutation `q` and the
permutation the certificate realizes. Class compatibility is necessary for the endpoint
equation of the certified chain, not sufficient.
HC no distance; AV milestone no distance.
-/
noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- Conjugacy-class labels of the review table: `P = [r₁]`, `M = [r₁⁻¹]`, `S = [x²]`.
Source: review hlean-rev-ctpu (2026-11-05), exact finite comparison; G32 v0.16, Appendix A. -/
inductive b65y_Class where
  | P | M | S
  deriving DecidableEq, Repr

example : b65y_Class.P ≠ b65y_Class.M := by decide

/-- The determinant of each labelled class: `ω`, `ω²` and `1`.
Source: G32 v0.16, Appendix A, determinants of `r₁` and `x`; `papers_g32_r1_det`. -/
def b65y_Class.det : b65y_Class → ℂ
  | .P => g32h_omega
  | .M => g32h_omega ^ 2
  | .S => 1

example : b65y_Class.S.det = 1 := rfl

open b65y_Class in
/-- Class sequence of `b4b_root`, in its declared index order.
Source: review hlean-rev-ctpu (2026-11-05), table; `PrymFamilyB4Defs.lean`, `b4b_root`. -/
def b65y_rootClasses : Fin 13 → b65y_Class := ![P, M, P, M, P, M, P, M, P, M, P, M, S]

example : b65y_rootClasses 12 = .S := rfl

open b65y_Class in
/-- Class sequence of `b65s_columnRoot`, in its declared index order.
Source: review hlean-rev-ctpu (2026-11-05), table; `PullbackMonodromyDefs.lean`,
`b65s_columnRoot`. -/
def b65y_columnRootClasses : Fin 13 → b65y_Class := ![S, P, M, P, M, P, M, P, M, P, M, P, M]

example : b65y_columnRootClasses 0 = .S := rfl

open b65y_Class in
/-- Class sequence of `(b65b_initial i)⁻¹`, in its declared index order.
Source: review hlean-rev-ctpu (2026-11-05), table; `BraidCertificateDefs.lean`,
`b65b_initialWords`. -/
def b65y_initialInvClasses : Fin 13 → b65y_Class := ![S, P, M, P, M, P, M, M, P, M, P, M, P]

example : b65y_initialInvClasses 7 = .M := rfl

/-- The class-matching source-index permutation: `[(b65b_initial i)⁻¹] = [b65s_columnRoot (q i)]`.
Source: review hlean-rev-ctpu (2026-11-05), exact finite comparison. -/
def b65y_classSourcePerm : Fin 13 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6, 8, 7, 10, 9, 12, 11]

example : Function.Bijective b65y_classSourcePerm := by decide

/-- A class-matching reference-source permutation in branch-label coordinates
`j = 12 - b65x_slot i`: the certified class at label `j` is the class of `b4b_root (σ j)`.
Source: review hlean-rev-ctpu (2026-11-05); slot convention `BraidBridgesDefs.lean`,
`b65x_slot`. -/
def b65y_classLabelPerm : Fin 13 → Fin 13 := ![0, 1, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 12]

example : b65y_classLabelPerm 10 = 11 := rfl

/-- The column permutation of the 86-move word `b65b_word`, as recorded on `spec/htw`.
Source: `docs/specs/spec-htw.md` on `spec/htw`; review hlean-rev-ctpu (2026-11-05). -/
def b65y_wordPerm : Fin 13 → Fin 13 := ![0, 4, 1, 7, 2, 6, 9, 5, 10, 3, 12, 11, 8]

example : Function.Bijective b65y_wordPerm := by decide

/-- The inverse of `b65y_wordPerm`.
Source: review hlean-rev-ctpu (2026-11-05). -/
def b65y_wordPermInv : Fin 13 → Fin 13 := ![0, 2, 4, 9, 1, 7, 5, 3, 12, 6, 8, 11, 10]

example : ∀ i, b65y_wordPermInv (b65y_wordPerm i) = i := by decide

private def b65y_detU : b4b_Group →* ℂˣ := (Matrix.detMonoidHom.comp b4b_toMatrix).toHomUnits

private theorem b65y_detU_val (g : b4b_Group) : (b65y_detU g : ℂ) = (b4b_toMatrix g).det := rfl

private theorem b65y_det_gen0 : (b65y_detU (b4b_generators 0) : ℂ) = g32h_omega :=
  papers_g32_r1_det g32h_omega g32h_omega_sq_add

private theorem b65y_det_gen1 : (b65y_detU (b4b_generators 1) : ℂ) = g32h_omega ^ 2 := by
  change (g32R2 g32h_omega).det = _
  have hω := g32h_omega_sq_add
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32R2, Fin.succAbove]
  papers3b_omega_ring papers3b_omega_pow g32h_omega hω

private theorem b65y_det_gen2 : (b65y_detU (b4b_generators 2) : ℂ) = 1 := by
  change (g32X g32h_omega).det = _
  have hω := g32h_omega_sq_add
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, g32X, Fin.succAbove]
  papers3b_omega_ring papers3b_omega_pow g32h_omega hω

private theorem b65y_omega_ne : g32h_omega ≠ 0 := by
  intro h
  have hω := g32h_omega_sq_add
  rw [h] at hω
  norm_num at hω

/-- The three class determinants are pairwise distinct.
Source: `g32h_omega_sq_add`; `ω` is a primitive cube root of unity. -/
theorem b65y_class_det_injective : Function.Injective b65y_Class.det := by
  have hω := g32h_omega_sq_add
  have h0 := b65y_omega_ne
  have h1 : g32h_omega ≠ 1 := by
    intro h
    rw [h] at hω
    norm_num at hω
  have h2 : g32h_omega ^ 2 ≠ 1 := by
    intro h
    have h' : g32h_omega = -2 := by linear_combination hω - h
    rw [h'] at h
    norm_num at h
  have h3 : g32h_omega ≠ g32h_omega ^ 2 := by
    intro h
    have h' : g32h_omega = -1 / 2 := by linear_combination (hω + h) / 2
    rw [h'] at hω
    norm_num at hω
  intro a b h
  cases a <;> cases b <;> simp_all [b65y_Class.det, eq_comm]

example : b65y_Class.P.det ≠ b65y_Class.M.det :=
  fun h ↦ absurd (b65y_class_det_injective h) (by decide)

set_option maxHeartbeats 400000 in
/-- Every entry of `b4b_root` has the determinant of its class in `b65y_rootClasses`.
Source: `b4b_root`, `b4b_reflection`; G32 v0.16, Appendix A, determinants of `r₁`, `r₂`, `x`. -/
theorem b65y_root_classes (i : Fin 13) :
    (b4b_toMatrix (b4b_root i)).det = (b65y_rootClasses i).det := by
  have hω := g32h_omega_sq_add
  have h0 := b65y_omega_ne
  rw [← b65y_detU_val]
  fin_cases i <;>
    simp [b4b_root, b4b_reflection, b65y_rootClasses, b65y_Class.det, map_mul, map_inv,
      Units.val_mul, b65y_det_gen0, b65y_det_gen1, b65y_det_gen2] <;>
    field_simp <;> papers3b_omega_ring papers3b_omega_pow g32h_omega hω

example : (b4b_toMatrix (b4b_root 10)).det = g32h_omega := b65y_root_classes 10

set_option maxHeartbeats 400000 in
/-- Every entry of `b65s_columnRoot` has the determinant of its class in
`b65y_columnRootClasses`.
Source: `b65s_columnRoot`, `b4b_root`; G32 v0.16, Appendix A. -/
theorem b65y_columnRoot_classes (i : Fin 13) :
    (b4b_toMatrix (b65s_columnRoot i)).det = (b65y_columnRootClasses i).det := by
  have hω := g32h_omega_sq_add
  have h0 := b65y_omega_ne
  rw [← b65y_detU_val]
  fin_cases i <;>
    simp [b65s_columnRoot, b4b_root, b4b_reflection, b65y_columnRootClasses, b65y_Class.det,
      map_mul, map_inv, Units.val_mul, b65y_det_gen0, b65y_det_gen1, b65y_det_gen2] <;>
    field_simp <;> papers3b_omega_ring papers3b_omega_pow g32h_omega hω

example : (b4b_toMatrix (b65s_columnRoot 0)).det = 1 := b65y_columnRoot_classes 0

set_option maxHeartbeats 400000 in
/-- Every inverted certified entry `(b65b_initial i)⁻¹` has the determinant of its class in
`b65y_initialInvClasses`.
Source: `b65b_initialWords`, `b65b_eval`, `b65b_cut`; G32 v0.16, Appendix A. -/
theorem b65y_initial_classes (i : Fin 13) :
    (b4b_toMatrix (b65b_initial i)⁻¹).det = (b65y_initialInvClasses i).det := by
  have hω := g32h_omega_sq_add
  have h0 := b65y_omega_ne
  rw [← b65y_detU_val]
  fin_cases i <;>
    simp [b65b_initial, b65b_initialWords, b65b_eval, b65b_cut, b65y_initialInvClasses,
      b65y_Class.det, map_mul, map_inv, Units.val_mul, b65y_det_gen0, b65y_det_gen1,
      b65y_det_gen2] <;>
    field_simp <;> papers3b_omega_ring papers3b_omega_pow g32h_omega hω

example : (b4b_toMatrix (b65b_initial 4)⁻¹).det = g32h_omega ^ 2 := b65y_initial_classes 4

/-- Each of the three class sequences has six entries `P`, six entries `M` and one entry `S`.
Source: review hlean-rev-ctpu (2026-11-05), multiset `6P + 6M + S`. -/
theorem b65y_class_counts :
    ∀ f ∈ [b65y_rootClasses, b65y_columnRootClasses, b65y_initialInvClasses],
      (List.ofFn f).count .P = 6 ∧ (List.ofFn f).count .M = 6 ∧ (List.ofFn f).count .S = 1 := by
  decide

example : (List.ofFn b65y_rootClasses).count .S = 1 := (b65y_class_counts _ (by simp)).2.2

/-- The source-index permutation `q` matches classes, and hence determinants:
`[(b65b_initial i)⁻¹] = [b65s_columnRoot (q i)]` at the level of class labels.
Source: `b65y_initial_classes`, `b65y_columnRoot_classes`; finite check. -/
theorem b65y_classSourcePerm_matches (i : Fin 13) :
    b65y_initialInvClasses i = b65y_columnRootClasses (b65y_classSourcePerm i) ∧
      (b4b_toMatrix (b65b_initial i)⁻¹).det =
        (b4b_toMatrix (b65s_columnRoot (b65y_classSourcePerm i))).det := by
  have h : b65y_initialInvClasses i = b65y_columnRootClasses (b65y_classSourcePerm i) := by
    revert i
    decide
  exact ⟨h, by rw [b65y_initial_classes, b65y_columnRoot_classes, h]⟩

example : b65y_initialInvClasses 7 = b65y_columnRootClasses 8 :=
  (b65y_classSourcePerm_matches 7).1

/-- In branch-label coordinates `j = 12 - b65x_slot i`, the label permutation `σ` matches
classes: the certified class at label `j` is the class of `b4b_root (σ j)`.
Source: review hlean-rev-ctpu (2026-11-05); `b65x_slot`; finite check. -/
theorem b65y_classLabelPerm_matches (i : Fin 13) :
    b65y_initialInvClasses i = b65y_rootClasses (b65y_classLabelPerm (b65x_slot i).rev) ∧
      (b4b_toMatrix (b65b_initial i)⁻¹).det =
        (b4b_toMatrix (b4b_root (b65y_classLabelPerm (b65x_slot i).rev))).det := by
  have h : b65y_initialInvClasses i =
      b65y_rootClasses (b65y_classLabelPerm (b65x_slot i).rev) := by
    revert i
    decide
  exact ⟨h, by rw [b65y_initial_classes, b65y_root_classes, h]⟩

example : (b65x_slot 4).rev = 10 := rfl

/-- Neither the word permutation `p` nor its inverse matches classes in the
`b65s_columnRoot` and `(b65b_initial i)⁻¹` convention; both fail at index one.
Source: review hlean-rev-ctpu (2026-11-05); `b65y_class_det_injective`. -/
theorem b65y_wordPerm_not_class_matching :
    (b4b_toMatrix (b65b_initial 1)⁻¹).det ≠
        (b4b_toMatrix (b65s_columnRoot (b65y_wordPerm 1))).det ∧
      (b4b_toMatrix (b65b_initial 1)⁻¹).det ≠
        (b4b_toMatrix (b65s_columnRoot (b65y_wordPermInv 1))).det := by
  rw [b65y_initial_classes, b65y_columnRoot_classes, b65y_columnRoot_classes]
  exact ⟨fun h ↦ absurd (b65y_class_det_injective h) (by decide),
    fun h ↦ absurd (b65y_class_det_injective h) (by decide)⟩

example : b65y_wordPerm 1 = 4 ∧ b65y_wordPermInv 1 = 2 := ⟨rfl, rfl⟩

end HodgeLean.Foundations.Program
