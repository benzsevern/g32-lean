import HodgeLean.Foundations.Program.MilneTensorOrbit
import HodgeLean.Foundations.Program.MilneTensorAlternating

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem m1b_alternating_abstract_basis (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (ha : ∀ x, B x x = 0) :
    ∃ (k : ℕ) (b : Module.Basis (Fin k ⊕ Fin k) ℂ V),
      Module.finrank ℂ V = 2 * k ∧ ∀ i j, B (b i) (b j) = m1b_J k i j := by
  classical
  let b₀ := Module.finBasis ℂ V
  let M := B.toMatrix b₀
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b₀).mp hB))
  have hs : M.transpose = -M := by
    ext i j
    simp only [M, Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply]
    exact (LinearMap.IsAlt.neg ha _ _).symm
  obtain ⟨k, b, hk, hb⟩ := m1b_alternating_basis (Module.finrank ℂ V) M hM hs
  refine ⟨k, b.map b₀.equivFun.symm, hk, ?_⟩
  intro i j
  change B (b₀.equivFun.symm (b i)) (b₀.equivFun.symm (b j)) = m1b_J k i j
  rw [← LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
  simpa only [Matrix.toBilin'_apply', M] using hb i j

theorem m1b_alternating_forms_same_orbit (B C : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (haB : ∀ x, B x x = 0) (haC : ∀ x, C x x = 0) :
    C ∈ Set.range (m1b_formTransport B) := by
  obtain ⟨k, b, hk, hb⟩ := m1b_alternating_abstract_basis B hB haB
  obtain ⟨l, c, hl, hc⟩ := m1b_alternating_abstract_basis C hC haC
  have hkl : l = k := by omega
  subst l
  let e := b.equiv c (Equiv.refl _)
  have heB : C.compl₁₂ e.toLinearMap e.toLinearMap = B := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, e,
      Module.Basis.equiv_apply, Equiv.refl_apply, hb, hc]
  refine ⟨e, ?_⟩
  ext x y
  have h := LinearMap.congr_fun (LinearMap.congr_fun heB (e.symm x)) (e.symm y)
  simpa only [m1b_formTransport, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h.symm

end HodgeLean.Foundations.Program
