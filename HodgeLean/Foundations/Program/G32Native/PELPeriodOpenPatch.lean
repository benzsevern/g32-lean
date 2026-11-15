import HodgeLean.Foundations.Program.G32Native.PELDomainTopology
import HodgeLean.Foundations.Program.G32Native.PELReferenceBasisInclusion
import HodgeLean.Foundations.Program.G32Native.PELRealCayleyComponent
import HodgeLean.Foundations.Program.G32Native.PELRealSkewCentralizer
import HodgeLean.Foundations.Program.G32Native.PELCayleyInverse
import HodgeLean.Foundations.Program.G32Native.PELPeriodMatrices

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MatrixCayley MvPolynomial
open scoped Quaternion

/-- An open patch of retained period points supplies equations on the real
Cayley conjugates near zero, with the original matrix marking. -/
theorem pel_period_open_patch_equations (R : PELSplitReference)
    (U : Set (PELSplitComponent R)) (hU : IsOpen U) (z : PELSplitComponent R) (hz : z ∈ U)
    (s : Set (MvPolynomial (Fin 12 × Fin 12) ℂ))
    (hs : ∀ w ∈ U, pelPeriodMatrix R w.val ∈ g1_zeroSet s) :
    let E := R.form.map (algebraMap ℚ ℝ)
    let S := Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ)
    ∀ᶠ X : pel_real_skew_centralizer E S in nhds 0,
      ∀ p ∈ s, eval (fun ij : Fin 12 × Fin 12 =>
        (cayley (-(X.val.map Complex.ofReal)) * (pelPeriodMatrix R z.val).val *
          cayley (X.val.map Complex.ofReal)) ij.1 ij.2) p = 0 := by
  let E := R.form.map (algebraMap ℚ ℝ)
  let S := Set.range fun i : Fin 4 =>
    (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ)
  let L := pel_real_skew_centralizer E S
  change ∀ᶠ X : L in nhds 0, _
  have hi : Topology.IsInducing (fun w : PELSplitComponent R => w.val.J) :=
    (pel_domain_isEmbedding R).isInducing.comp Topology.IsInducing.subtypeVal
  obtain ⟨V, hV, hVU⟩ := hi.isOpen_iff.mp hU
  have hzV : z.val.J ∈ V := by
    change z ∈ (fun w : PELSplitComponent R => w.val.J) ⁻¹' V
    rwa [hVU]
  have hX : ContinuousAt (fun X : L => X.val) 0 := continuous_subtype_val.continuousAt
  have hinv1 : ContinuousAt
      (fun M : Matrix (Fin 12) (Fin 12) ℝ => M⁻¹) 1 := by
    apply continuousAt_matrix_inv
    rw [Matrix.det_one]
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have hcp : ContinuousAt (fun X : L => cayley X.val) 0 := by
    unfold cayley
    apply (continuousAt_const.sub hX).mul
    exact hinv1.comp_of_eq (continuousAt_const.add hX) (by simp)
  have hcpi : ContinuousAt (fun X : L => (cayley X.val)⁻¹) 0 := by
    exact hinv1.comp_of_eq hcp (by simp [cayley])
  have hW : ∀ᶠ X : L in nhds 0, (cayley X.val)⁻¹ * z.val.J * cayley X.val ∈ V := by
    have hf : ContinuousAt (fun X : L =>
        (cayley X.val)⁻¹ * z.val.J * cayley X.val) 0 :=
      (hcpi.mul continuousAt_const).mul hcp
    apply hf.eventually (hV.mem_nhds ?_)
    simpa only [ZeroMemClass.coe_zero, cayley, add_zero, sub_zero,
      inv_one, mul_one, one_mul] using hzV
  have hN := pel_real_cayley_identity_neighborhood E S L
    (fun X => X.property.1) (fun X => X.property.2)
  have hD : ∀ᶠ X : L in nhds 0, (1 + X.val).det ≠ 0 := by
    apply ((continuous_const.add continuous_subtype_val).matrix_det.isOpen_preimage _
      isOpen_compl_singleton).mem_nhds
    simp
  filter_upwards [hW, hN, hD] with X hXV hXN hXD
  obtain ⟨g, hg, hgval⟩ := hXN
  let q := pel_reference_basis_inclusion R g
  have hq : q ∈ connectedComponent (1 : pelRealIsometries R) := by
    have hh := (pel_reference_basis_inclusion_continuous R).mapsTo_connectedComponent 1 hg
    simpa only [map_one] using hh
  let w : PELSplitComponent R :=
    ⟨pelRealConjugate R q z.val, pelRealConjugate_mem_component R q hq z⟩
  have hwJ : w.val.J = (cayley X.val)⁻¹ * z.val.J * cayley X.val := by
    change (g.val⁻¹).val * z.val.J * g.val.val = _
    rw [Matrix.GeneralLinearGroup.coe_inv, hgval]
  have hwU : w ∈ U := by
    rw [← hVU]
    change w.val.J ∈ V
    rwa [hwJ]
  intro p hp
  have hh := hs w hwU p hp
  change eval (fun ij : Fin 12 × Fin 12 =>
    (w.val.J.map (algebraMap ℝ ℂ)) ij.1 ij.2) p = 0 at hh
  rw [hwJ, pel_cayley_inverse X.val hXD, Matrix.map_mul, Matrix.map_mul,
    MatrixCayley.map, MatrixCayley.map] at hh
  rw [Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a)] at hh
  exact hh

#print axioms pel_period_open_patch_equations
end HodgeLean.Foundations.Program.GeneralTypeIII
