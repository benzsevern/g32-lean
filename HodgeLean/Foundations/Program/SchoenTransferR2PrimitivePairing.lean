import HodgeLean.Foundations.CyclicAction
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Primitive tests for an invariant perfect pairing

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Invariance makes eigenvectors orthogonal unless their eigenvalues multiply to one.
Source: Schoen (1988), Lemma 1.1, p. 5, character decomposition and invariant pairings.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_eigen_pairing_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) (T : Module.End ℂ V)
    (hB : ∀ x y, B (T x) (T y) = B x y)
    (lam mu : ℂ) (hlammu : lam * mu ≠ 1) (x y : V)
    (hx : T x = lam • x) (hy : T y = mu • y) : B x y = 0 := by
  have he : (lam * mu) * B x y = B x y := by
    simpa only [hx, hy, map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm mu lam] using hB x y
  have hz : (lam * mu - 1) * B x y = 0 := by
    rw [sub_mul, one_mul, he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hlammu)

#print axioms s4_assembly_eigen_pairing_eq_zero
/-- Extending scalars preserves invariance of a bilinear form.
Source: Bourbaki, Algebra, Chapter II, scalar extension of bilinear forms.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_pairing_baseChange_invariant
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V) (T : Module.End ℚ V)
    (hB : ∀ x y, B (T x) (T y) = B x y) :
    ∀ x y, B.baseChange ℂ ((T.baseChange ℂ) x) ((T.baseChange ℂ) y) =
      B.baseChange ℂ x y := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => intro y; simp
  | add x z hx hz => intro y; simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a x =>
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b y => simp only [LinearMap.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, hB]

#print axioms s4_assembly_pairing_baseChange_invariant
/-- The primitive part of an invariant perfect rational pairing is nondegenerate.
Source: Schoen (1988), Lemma 1.1, p. 5, character decomposition and invariant pairings.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_primitive_pairing_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hperfect : Function.Bijective B)
    (T : Module.End ℚ V) (m : ℕ) (hm : 0 < m) (hT : T ^ m = 1)
    (hB : ∀ x y, B (T x) (T y) = B x y)
    (v : V) (hv : v ∈ isotypic T m)
    (hzero : ∀ w ∈ isotypic T m, B v w = 0) : v = 0 := by
  classical
  letI : FiniteDimensional ℚ V :=
    (Basis.linearEquiv_dual_iff_finiteDimensional).mp
      ⟨LinearEquiv.ofBijective B hperfect⟩
  let BC := B.baseChange ℂ
  let TC := T.baseChange ℂ
  let vc : ℂ ⊗[ℚ] V := 1 ⊗ₜ[ℚ] v
  have hvc : vc ∈ (isotypic T m).baseChange ℂ :=
    Submodule.tmul_mem_baseChange_of_mem 1 hv
  have hkill : (isotypic T m).baseChange ℂ ≤ LinearMap.ker (BC vc) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro z ⟨w, hw, rfl⟩
    change B.baseChange ℂ (1 ⊗ₜ[ℚ] v) (1 ⊗ₜ[ℚ] w) = 0
    simp [hzero w hw]
  have hinv := s4_assembly_pairing_baseChange_invariant B T hB
  have horth (mu : ℂ) (hmu : ¬ IsPrimitiveRoot mu m)
      (z : ℂ ⊗[ℚ] V) (hz : z ∈ Module.End.eigenspace TC mu) :
      (isotypic T m).baseChange ℂ ≤ LinearMap.ker ((BC.flip) z) := by
    rw [baseChange_isotypic T hm]
    refine iSup_le fun lam => iSup_le fun hlam => ?_
    intro x hx
    change BC x z = 0
    apply s4_assembly_eigen_pairing_eq_zero BC TC hinv lam mu ?_ x z
      (Module.End.mem_eigenspace_iff.mp hx) (Module.End.mem_eigenspace_iff.mp hz)
    intro he
    have hlam' := (mem_primitiveRoots hm).mp hlam
    have hne : lam ≠ 0 := hlam'.ne_zero hm.ne'
    have hmu' : mu = lam⁻¹ := by
      apply (mul_left_cancel₀ hne)
      rw [he, mul_inv_cancel₀ hne]
    exact hmu (hmu' ▸ hlam'.inv)
  have hall : (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) ≤ LinearMap.ker (BC vc) := by
    have hdecomp := ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (isInternal_eigenspace_baseChange T hm hT)).2
    rw [← hdecomp]
    refine iSup_le fun mu => ?_
    intro z hz
    by_cases hmu : IsPrimitiveRoot ((mu : ℂˣ) : ℂ) m
    · apply hkill
      rw [baseChange_isotypic T hm]
      exact Submodule.mem_iSup_of_mem ((mu : ℂˣ) : ℂ)
        (Submodule.mem_iSup_of_mem ((mem_primitiveRoots hm).mpr hmu) hz)
    · exact horth _ hmu z hz hvc
  have he : B v = 0 := by
    ext w
    have hw := hall (show 1 ⊗ₜ[ℚ] w ∈ (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) from trivial)
    change B.baseChange ℂ (1 ⊗ₜ[ℚ] v) (1 ⊗ₜ[ℚ] w) = 0 at hw
    simpa using hw
  apply hperfect.injective
  simpa using he

#print axioms s4_assembly_primitive_pairing_eq_zero
end HodgeLean.Foundations.Program
