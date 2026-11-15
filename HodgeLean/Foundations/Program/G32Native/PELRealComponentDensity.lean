import HodgeLean.Foundations.Program.G32Native.PELComplexCayleyMembership
import HodgeLean.Foundations.Program.G32Native.PELZariskiOpenPatch

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MatrixCayley MvPolynomial

/-- A complex algebraic subgroup containing the ordinary real identity
component of a real bilinear isometry centralizer contains its complex
Zariski identity component. -/
theorem pel_complex_component_subset_of_real_component {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (S : Set (Matrix (Fin n) (Fin n) ℝ))
    (K : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hK : @IsClosed _ (g1_zariski ℂ n) (K : Set _))
    (hreal : ∀ g : pelIsometrySubgroup E S, g ∈ connectedComponent 1 →
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈ K) :
    g1_identityComponent (pelIsometryGroup (E.map Complex.ofReal)
      ((fun T => T.map Complex.ofReal) '' S)) ⊆ (K : Set _) := by
  classical
  letI : TopologicalSpace (Matrix.GeneralLinearGroup (Fin n) ℂ) := g1_zariski ℂ n
  let G := pelIsometryGroup (E.map Complex.ofReal) ((fun T => T.map Complex.ofReal) '' S)
  let U : Set G.carrier := {g | (1 + g.val.val).det ≠ 0}
  have hZ : IsClosed {g : Matrix.GeneralLinearGroup (Fin n) ℂ | (1 + g.val).det = 0} := by
    have hd := g1_isClosed_zeroSet ({(1 + g1_varMatrix ℂ n).det} :
      Set (MvPolynomial (Fin n × Fin n) ℂ))
    convert hd using 1
    ext g
    simp only [g1_zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rw [RingHom.map_det, map_add, map_one, g1_mapMatrix_eval_varMatrix]
  have hU : IsOpen U := hZ.isOpen_compl.preimage continuous_subtype_val
  have hone : (1 : G.carrier) ∈ U := by
    change (1 + (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0
    rw [show (1 + (1 : Matrix (Fin n) (Fin n) ℂ)) = (2 : ℂ) • 1 by
      rw [two_smul], Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ two_ne_zero
  apply pel_identityComponent_subset_of_open_patch G K hK U hU hone
  intro g hg
  let Y := cayley g.val.val
  have hG : g.val.val.transpose * E.map Complex.ofReal * g.val.val = E.map Complex.ofReal ∧
      ∀ T ∈ S, g.val.val * T.map Complex.ofReal = T.map Complex.ofReal * g.val.val :=
    ⟨g.property.1, fun T hT => (g.property.2 _ ⟨T, hT, rfl⟩).eq⟩
  have hY := pel_cayley_bilinear_skew hG.1 hg
  have hYC : ∀ T ∈ S, Y * T.map Complex.ofReal = T.map Complex.ofReal * Y :=
    fun T hT => MatrixCayley.commutes (hG.2 T hT)
  let L := pel_real_skew_centralizer E S
  have hR : Y.map Complex.re ∈ L :=
    ⟨(pel_real_imag_bilinear_skew E Y hY).1,
      fun T hT => (pel_real_imag_commute T Y (hYC T hT)).1⟩
  have hI : Y.map Complex.im ∈ L :=
    ⟨(pel_real_imag_bilinear_skew E Y hY).2,
      fun T hT => (pel_real_imag_commute T Y (hYC T hT)).2⟩
  have hinv := MatrixCayley.involution (two_ne_zero : (2 : ℂ) ≠ 0) hg
  exact pel_complex_cayley_mem_of_real_component E S L
    (fun X => X.property.1) (fun X => X.property.2) K hK hreal Y hR hI hinv.1
    g.val hinv.2.symm

end HodgeLean.Foundations.Program.GeneralTypeIII
