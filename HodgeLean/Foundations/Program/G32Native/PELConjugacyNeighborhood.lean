import HodgeLean.Foundations.Program.G32Native.PELRealConjugationContinuation
import HodgeLean.Foundations.Program.G32Native.PELConnectedClosedPatch
import HodgeLean.Foundations.Program.G32Native.PELRealSkewCentralizer
import HodgeLean.Foundations.Program.G32Native.PELZariskiNormalizer

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MatrixCayley MvPolynomial

/-- Polynomial equations on conjugates in a real Cayley neighborhood hold on
all conjugates by the complex identity component of the isometry centralizer. -/
theorem pel_conjugacy_equations_of_real_neighborhood {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (S : Set (Matrix (Fin n) (Fin n) ℝ))
    (x : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (s : Set (MvPolynomial (Fin n × Fin n) ℂ))
    (hlocal : ∀ᶠ X : pel_real_skew_centralizer E S in nhds 0,
      ∀ p ∈ s, eval (fun ij : Fin n × Fin n =>
        (cayley (-(X.val.map Complex.ofReal)) * x.val *
          cayley (X.val.map Complex.ofReal)) ij.1 ij.2) p = 0) :
    ∀ g ∈ g1_identityComponent (pelIsometryGroup (E.map Complex.ofReal)
      ((fun T => T.map Complex.ofReal) '' S)),
      g⁻¹ * x * g ∈ g1_zeroSet s := by
  classical
  letI := g1_zariski ℂ n
  let G := pelIsometryGroup (E.map Complex.ofReal)
    ((fun T => T.map Complex.ofReal) '' S)
  obtain ⟨I, hI⟩ := g1_exists_identityComponent G
  have hIc : g1_IsConnected I := by
    change @IsConnected _ (g1_zariski ℂ n) (I.carrier : Set _)
    rw [hI]
    exact isConnected_connectedComponentIn_iff.mpr G.carrier.one_mem
  let Z := {g : Matrix.GeneralLinearGroup (Fin n) ℂ | g⁻¹ * x * g ∈ g1_zeroSet s}
  let U := {g : Matrix.GeneralLinearGroup (Fin n) ℂ | (1 + g.val).det ≠ 0}
  have hZ : @IsClosed _ (g1_zariski ℂ n) Z :=
    (g1_isClosed_zeroSet s).preimage (pel_continuous_conjugating x)
  have hU : @IsOpen _ (g1_zariski ℂ n) U := by
    have hd := g1_isClosed_zeroSet ({(1 + g1_varMatrix ℂ n).det} :
      Set (MvPolynomial (Fin n × Fin n) ℂ))
    have he : g1_zeroSet ({(1 + g1_varMatrix ℂ n).det} :
        Set (MvPolynomial (Fin n × Fin n) ℂ)) = Uᶜ := by
      ext g
      simp only [g1_zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq,
        U, Set.mem_compl_iff, not_not]
      rw [RingHom.map_det, map_add, map_one, g1_mapMatrix_eval_varMatrix]
    rw [he] at hd
    simpa only [compl_compl] using hd.isOpen_compl
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) ∈
      (I.carrier : Set _) ∩ U := by
    refine ⟨I.carrier.one_mem, ?_⟩
    change (1 + (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0
    rw [show (1 + (1 : Matrix (Fin n) (Fin n) ℂ)) = (2 : ℂ) • 1 by
      rw [two_smul], Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ two_ne_zero
  have hpatch : (I.carrier : Set _) ∩ U ⊆ Z := by
    rintro g ⟨hg, hgu⟩
    have hgG : g ∈ G.carrier := by
      rw [hI] at hg
      exact connectedComponentIn_subset _ _ hg
    let Y := cayley g.val
    have hgE : g.val.transpose * E.map Complex.ofReal * g.val = E.map Complex.ofReal :=
      hgG.1
    have hgS : ∀ T ∈ S, g.val * T.map Complex.ofReal = T.map Complex.ofReal * g.val :=
      fun T hT => (hgG.2 _ ⟨T, hT, rfl⟩).eq
    have hY := pel_cayley_bilinear_skew hgE hgu
    have hYC : ∀ T ∈ S, Y * T.map Complex.ofReal = T.map Complex.ofReal * Y :=
      fun T hT => MatrixCayley.commutes (hgS T hT)
    have hR : Y.map Complex.re ∈ pel_real_skew_centralizer E S :=
      ⟨(pel_real_imag_bilinear_skew E Y hY).1,
        fun T hT => (pel_real_imag_commute T Y (hYC T hT)).1⟩
    have hIm : Y.map Complex.im ∈ pel_real_skew_centralizer E S :=
      ⟨(pel_real_imag_bilinear_skew E Y hY).2,
        fun T hT => (pel_real_imag_commute T Y (hYC T hT)).2⟩
    have hinv := MatrixCayley.involution (two_ne_zero : (2 : ℂ) ≠ 0) hgu
    have hminus : (1 - Y).det ≠ 0 := by
      have hgd : (cayley Y).det ≠ 0 := by rw [hinv.2]; exact g.det_ne_zero
      rw [cayley, Matrix.det_mul] at hgd
      exact (mul_ne_zero_iff.mp hgd).1
    have hci : (cayley Y)⁻¹ = cayley (-Y) := by
      rw [cayley, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hinv.1)]
      simp only [cayley, sub_neg_eq_add, sub_eq_add_neg, neg_neg]
      rfl
    have hi : (g⁻¹).val = cayley (-Y) := by
      calc
        (g⁻¹).val = g.val⁻¹ := Matrix.GeneralLinearGroup.coe_inv g
        _ = (cayley Y)⁻¹ := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M⁻¹) hinv.2.symm
        _ = cayley (-Y) := hci
    intro p hp
    change eval (fun ij : Fin n × Fin n =>
      ((g⁻¹).val * x.val * g.val) ij.1 ij.2) p = 0
    rw [hi, ← hinv.2]
    exact pel_real_subspace_conjugation_continuation
      (pel_real_skew_centralizer E S) x.val p
      (hlocal.mono fun _ h => h p hp) Y hR hIm hminus hinv.1
  have h := pel_connected_group_subset_closed_of_patch I hIc Z U hZ hU ⟨1, h1⟩ hpatch
  intro g hg
  exact h (by rwa [hI])

#print axioms pel_conjugacy_equations_of_real_neighborhood
end HodgeLean.Foundations.Program.GeneralTypeIII
