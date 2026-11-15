import HodgeLean.Foundations.Program.PeriodMultiplication
import HodgeLean.Foundations.Program.PrymTheoremAPolarized

/-! Ordered frame changes for residue multiplication.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold TopologicalSpace HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Change a three-frame using columns of its coordinate matrix.
Source: Mathlib Module.Basis.sum_repr; G32 v0.16, Subsection 5.5(6). -/
def b66e_reframe (D : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : Fin 3 → b66g_primitiveForms D t) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (i : Fin 3) : b66g_primitiveForms D t := ∑ a, P a i • q a

example (D : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : Fin 3 → b66g_primitiveForms D t) (i : Fin 3) :
    b66e_reframe D t q 1 i = q i := by
  simp [b66e_reframe, Matrix.one_apply]

/-- Output change on ordered products. The two old indices are column indices.
Source: G32 v0.16, Subsection 5.5(7); Mathlib finProdFinEquiv. -/
def b66e_productChange (P R : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 9) (Fin 9) ℂ := fun u w =>
  let ij := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm u
  let ab := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm w
  P ab.1 ij.1 * R ab.2 ij.2

example (P R : Matrix (Fin 3) (Fin 3) ℂ) (i j a b : Fin 3) :
    b66e_productChange P R (finProdFinEquiv (i,j)) (finProdFinEquiv (a,b)) =
      P a i * R b j := by simp [b66e_productChange]

/-- Transpose of the column matrix of multiplication, in the retained row convention.
Source: g32r_PeriodMap.codiff; G32 v0.16, Lemma 5.1 and Subsection 5.5(7). -/
def b66e_rows (μ : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 10 → ℂ)) :
    Matrix (Fin 9) (Fin 10) ℂ := (LinearMap.toMatrix' μ).transpose

example (μ : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 10 → ℂ)) (i : Fin 9) (j : Fin 10) :
    b66e_rows μ i j = μ (Pi.single i 1) j := rfl

/-- Checked shared-cover inputs for the based marking, with positive lattice rank.
This example uses only existing statements with bodies. -/
example : ∃ (R : rf8_SharedFamily) (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint}),
    (∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) ∧
    Module.finrank ℤ (b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀) = 12 ∧ b4b_root 0 ≠ 1 := by
  obtain ⟨R, y₀, γ, u₀, hγ, hroot⟩ := rf8_shared_root
  have hy : y₀ = b63gP_basePoint := by
    apply Subtype.ext
    obtain ⟨p, hp, -⟩ := hγ 12
    calc
      (y₀ : OnePoint ℂ) = mr_curve 12 0 := by simpa using hp 0
      _ = (b63gP_basePoint : OnePoint ℂ) := by
        change mr_curve 12 0 = ((mr_basePoint : ℂ) : OnePoint ℂ)
        simp [mr_curve, mr_outer, mr_basePoint]
  subst y₀
  have hγeq : γ = b63gP_loops := by
    funext i
    exact (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique
      (hγ i) (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  subst γ
  refine ⟨R, u₀, hroot, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin]
  · intro h
    have ho := b63_root_order (0 : Fin 13)
    rw [h, orderOf_one] at ho
    norm_num at ho

/-- Every retained fibre has dimension six and Hodge numbers three and three. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) :
    dim ((b63gR_family R).fiber t).X.left = 6 ∧
      g32h_h10 ((b63gR_family R).fiber t) = 3 ∧
      g32h_h01 ((b63gR_family R).fiber t) = 3 :=
  ⟨(g32h_fiber_polarized _ t).dim_eq, g32h_h10_eq_three _ t⟩

/-- A nonidentity tuple entry excludes the trivial monodromy case. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) (i : Fin 13) :
    (b63gR_family R).tuple t i ≠ 1 := by
  intro hi
  change b63g5_tuple i = 1 at hi
  have h1 : b4b_root i = 1 :=
    Subtype.val_injective (hi.trans (map_one b4b_toMatrix).symm)
  have h3 := b63_root_order i
  rw [h1, orderOf_one] at h3
  split_ifs at h3 <;> omega

/-- The universal-family equality used by S7 has a checked instance. -/
example : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ :=
  ⟨{ univ := b60b_univ, member := b60b_member, cover := b60c_cover }, rfl⟩

end HodgeLean.Foundations.Program
