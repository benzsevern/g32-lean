import HodgeLean.Foundations.Program.CodifferentialDictionaryRealizationProofs
import HodgeLean.Foundations.Program.PrymFamilyCentreNaturality

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

theorem b66d_transport_operator {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (s t : b6t_polydisc c)
    (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) :
    b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t (D.A s x) =
      b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x +
      (2 : ℤ) • b4_latticeAct ℂ b63d_scalarElement
        (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x) := by
  change D.P t (b6m_H1Equiv _ (D.A s x).val) = _
  rw [D.hA]
  simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, two_smul, map_add]
  rw [b63d_centre_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _) t s,
    b63g2_period_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) t
      (D.hG t) (D.P t) (D.hP t), b63d_period_centre_scalar]
  rfl

theorem b66d_root_star_mul : g32h_omega * star g32h_omega = 1 := by
  have hs : g32h_omega + star g32h_omega = -1 := by
    linear_combination (b64b_root_eigenvalue + b64b_conjugate_root_eigenvalue) / 2
  linear_combination g32h_omega * hs - g32h_omega_sq_add

theorem b66d_inverse_scalar {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ b4b_Group V) (h : b4b_Group) (v : V)
    (z w : ℂ) (hz : ρ h v = z • v) (hw : w * z = 1) :
    ρ h⁻¹ v = w • v := by
  have hk : v = z • ρ h⁻¹ v := by
    calc
      v = ρ h⁻¹ (ρ h v) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      _ = z • ρ h⁻¹ v := by rw [hz, map_smul]
  calc
    ρ h⁻¹ v = (w * z) • ρ h⁻¹ v := by rw [hw, one_smul]
    _ = w • v := by rw [mul_smul, ← hk]

theorem b66d_transport_form_eigen {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (s t : b6t_polydisc c) (cj : Bool)
    (φ : b65g_homG D t cj)
    (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) :
    (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t
      (D.A s x)).val ⟨φ.val (Pi.single 0 1), φ.property.1 _⟩ =
    (if cj then Complex.I * (Real.sqrt 3 : ℂ) else -Complex.I * (Real.sqrt 3 : ℂ)) *
      (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val
        ⟨φ.val (Pi.single 0 1), φ.property.1 _⟩ := by
  let θ : b3_HolForm ℂ (b65z_fibre c D.C t) := ⟨φ.val (Pi.single 0 1), φ.property.1 _⟩
  let w : ℂ := if cj then g32h_omega else star g32h_omega
  have hw : w * (if cj then star g32h_omega else g32h_omega) = 1 := by
    cases cj <;> simpa only [w, Bool.false_eq_true, ite_false, ite_true, mul_comm] using b66d_root_star_mul
  have hz : b4_formRepresentation (D.hG t) b63d_scalarElement θ =
      (if cj then star g32h_omega else g32h_omega) • θ :=
    Subtype.ext (b66d_form_scalar D t cj φ)
  have hinv := b66d_inverse_scalar (b4_formRepresentation (D.hG t))
    b63d_scalarElement θ _ w hz hw
  let l := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  rw [b66d_transport_operator]
  change L θ + (2 : ℤ) • (b4_latticeAct ℂ b63d_scalarElement l).val θ = _
  rw [b4cov_latticeAct_apply (D.hG t) b63d_scalarElement
    (b4_latticeAct_isPushforward (D.hG t) b63d_scalarElement) l θ]
  change L θ + (2 : ℤ) • L ((b4_formRepresentation (D.hG t)) b63d_scalarElement⁻¹ θ) = _
  rw [hinv, map_smul, ← Int.cast_smul_eq_zsmul ℂ]
  have hvalue : 1 + 2 * w =
      (if cj then Complex.I * (Real.sqrt 3 : ℂ) else -Complex.I * (Real.sqrt 3 : ℂ)) := by
    cases cj
    · exact b64b_conjugate_root_eigenvalue
    · exact b64b_root_eigenvalue
  change L θ + (2 : ℂ) * (w * L θ) =
    (if cj then Complex.I * (Real.sqrt 3 : ℂ) else -Complex.I * (Real.sqrt 3 : ℂ)) * L θ
  rw [← hvalue]
  ring

theorem b66d_pairing_omega_skew (x y : ℂ ⊗[ℤ] b60_Lattice) :
    b60_E.baseChange ℂ (b60_omegaC x) y = -b60_E.baseChange ℂ x (b60_omegaC y) := by
  change b60_E.baseChange ℂ (b60_omega.baseChange ℂ x) y =
    -b60_E.baseChange ℂ x (b60_omega.baseChange ℂ y)
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, neg_add]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz, neg_add]
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        b60_E_omega_skew, neg_smul]

end HodgeLean.Foundations.Program
