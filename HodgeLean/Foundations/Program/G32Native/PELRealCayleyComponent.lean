import HodgeLean.Foundations.Program.G32Native.PELIsometryGroup
import HodgeLean.Foundations.Program.G32Native.PELBilinearCayley
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.LocallyConvex.WithSeminorms

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MatrixCayley

/-- Cayley matrices from a real skew-centralizer subspace near zero belong
to the ordinary real identity component of the isometry centralizer. -/
theorem pel_real_cayley_identity_neighborhood {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (S : Set (Matrix (Fin n) (Fin n) ℝ))
    (L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hskew : ∀ X : L, X.val.transpose * E + E * X.val = 0)
    (hcomm : ∀ X : L, ∀ T ∈ S, X.val * T = T * X.val) :
    ∀ᶠ X : L in nhds 0, ∃ g : pelIsometrySubgroup E S,
      g ∈ connectedComponent (1 : pelIsometrySubgroup E S) ∧
      (g.val.val : Matrix (Fin n) (Fin n) ℝ) = cayley X.val := by
  let U : Set L := {X | (1 + X.val).det ≠ 0 ∧ (1 - X.val).det ≠ 0}
  have h0 : (0 : L) ∈ U := by simp [U]
  have hU : IsOpen U := by
    exact ((continuous_const.add continuous_subtype_val).matrix_det.isOpen_preimage _
      isOpen_compl_singleton).inter
      ((continuous_const.sub continuous_subtype_val).matrix_det.isOpen_preimage _
        isOpen_compl_singleton)
  have hdet : ∀ X : U, (cayley X.val.val).det ≠ 0 := by
    intro X
    rw [cayley, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero X.property.2 (inv_ne_zero X.property.1)
  let f : U → Matrix.GeneralLinearGroup (Fin n) ℝ := fun X =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (cayley X.val.val) (hdet X)
  have hC : Continuous (fun X : U => cayley X.val.val) := by
    have hX : Continuous (fun X : U => X.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    have he : (fun X : U => cayley X.val.val) = fun X =>
        (1 - X.val.val) * ((1 + X.val.val).det⁻¹ • (1 + X.val.val).adjugate) := by
      funext X
      simp only [cayley, Matrix.inv_def, Ring.inverse_eq_inv']
    rw [he]
    exact (continuous_const.sub hX).mul
      (((continuous_const.add hX).matrix_det.inv₀ (fun X => X.property.1)).smul
        (continuous_const.add hX).matrix_adjugate)
  have hf : Continuous f := by
    apply Units.continuous_iff.mpr
    refine ⟨hC, ?_⟩
    simp only [Matrix.GeneralLinearGroup.coe_inv]
    change Continuous (fun X : U => (cayley X.val.val)⁻¹)
    apply continuous_iff_continuousAt.mpr
    intro X
    apply (continuousAt_matrix_inv _ ?_).comp hC.continuousAt
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hdet X)
  let g : U → pelIsometrySubgroup E S := fun X =>
    ⟨f X, pel_cayley_preserves_bilinear (hskew X.val) X.property.1,
      fun T hT => MatrixCayley.commutes (hcomm X.val T hT)⟩
  have hg : Continuous g := continuous_induced_rng.mpr hf
  have hg0 : g ⟨0, h0⟩ = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp [g, f, cayley]
  haveI : LocallyConvexSpace ℝ ℝ := NormedSpace.toLocallyConvexSpace
  haveI : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℝ))
  haveI : LocallyConvexSpace ℝ L := .induced L.subtype
  haveI : ContinuousSMul ℝ L := inferInstance
  haveI : LocallyPathConnectedSpace L := inferInstance
  have hN : connectedComponentIn U (0 : L) ∈ nhds (0 : L) :=
    connectedComponentIn_mem_nhds (hU.mem_nhds h0)
  filter_upwards [hN] with X hX
  rw [connectedComponentIn_eq_image h0] at hX
  obtain ⟨Y, hY, rfl⟩ := hX
  refine ⟨g Y, ?_, rfl⟩
  have hh := hg.mapsTo_connectedComponent ⟨0, h0⟩ hY
  rwa [hg0] at hh

end HodgeLean.Foundations.Program.GeneralTypeIII
