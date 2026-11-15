import HodgeLean.Foundations.Program.CoverDictionaryReconstruct
import HodgeLean.Foundations.Program.CoverDictionarySolutionGerms

/-! Rational representations from invariant coefficient vectors. -/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
  (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
  (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
  (φ : (Fin 4 → ℂ) →ₗ[ℂ]
    (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
  (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
  (hYm : ∀ x i j, MeromorphicAt
    (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
      (extChartAt 𝓘(ℂ, ℂ) x x))

include hθ ht hφ hYm

/-- Invariance of `Y (φ(eᵢ)/ds)` yields a rational r-representation. -/
theorem b65g_rational_rRepresents
    (hinv : ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
      ∀ h : b4b_Group, b65g_Y S θ t (h • x) *ᵥ
        (fun i ↦ φ (Pi.single i 1) ⟨h • x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩) =
        b65g_Y S θ t x *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩)) :
    ∃ r : Fin 4 → RatFunc ℂ,
      (∀ i s, (r i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) ∧
      b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11)
        (b65p_poles p θ) (b65g_Y S θ t) r φ := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨r, hr, he⟩ := b65g_descend_generic O D θ hθO t ht (b65g_Y S θ t)
    (fun i ↦ φ (Pi.single i 1)) (fun i ↦ hφ _)
    (fun x hx i j ↦ (b65g_Y_entries_analytic S θ hθ t ht x hx i j).2) hYm hinv
  refine ⟨r, hr, b65g_rRepresents_of_descended D t _ _ _ _ φ hφ ?_ ?_ r he⟩
  · exact fun x hx ↦ b65g_mat_det_ne (S.unit θ hθ t ht x hx)
  · exact fun x hx ↦ b65g_ds_ne_good O D θ hθO t ht x hx

/-- Invariance of `Y⁻ᵀ (φ(eᵢ)/ds)` yields a rational q-representation. -/
theorem b65g_rational_qRepresents
    (hinv : ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
      ∀ h : b4b_Group, (b65g_Y S θ t (h • x))⁻¹ᵀ *ᵥ
        (fun i ↦ φ (Pi.single i 1) ⟨h • x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩) =
        (b65g_Y S θ t x)⁻¹ᵀ *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩)) :
    ∃ q : Fin 4 → RatFunc ℂ,
      (∀ i s, (q i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) ∧
      b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11)
        (b65p_poles p θ) (b65g_Y S θ t) q φ := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨q, hq, he⟩ := b65g_descend_generic O D θ hθO t ht (fun x ↦ (b65g_Y S θ t x)⁻¹ᵀ)
    (fun i ↦ φ (Pi.single i 1)) (fun i ↦ hφ _)
    (fun x hx i j ↦ (b65g_Y_entries_analytic S θ hθ t ht x hx j i).1)
    (fun x i j ↦ caf_meromorphic_matrix_inv _ _ (hYm x) j i) hinv
  refine ⟨q, hq, b65g_qRepresents_of_descended D t _ _ _ _ φ hφ ?_ ?_ q he⟩
  · exact fun x hx ↦ b65g_mat_det_ne (S.unit θ hθ t ht x hx)
  · exact fun x hx ↦ b65g_ds_ne_good O D θ hθO t ht x hx

end HodgeLean.Foundations.Program
