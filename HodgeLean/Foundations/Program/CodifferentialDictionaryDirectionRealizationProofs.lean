import HodgeLean.Foundations.Program.CodifferentialDictionaryPeriodProofs

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

theorem b66d_direction_of_chart_homG {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily c g) (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        s (D.P s) (D.Q s)).baseChange ℚ x y)
    (cj : Bool) (φ : b65g_homG D t cj) (q : b66f_primitiveForms D t)
    (hchart : b66f_chartForm D t q.val = φ.val (Pi.single 0 1)) :
    q.val ∈ b66f_direction D s t m (if cj then 0 else 1) := by
  obtain ⟨f, w, hc, hf, hs, hp⟩ :=
    b66f_gen_b66m_normalized_basis hg D s t m hJ hpol
  obtain ⟨M, hM⟩ := b66f_gen_b66m_chart_comparison hg D t
  let H : b66f_primitiveForms D t →ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c D.C t) :=
    M.toLinearMap.comp (Submodule.inclusion inf_le_left)
  have hH (u : b66f_primitiveForms D t) : (H u).val = b66f_chartForm D t u.val :=
    hM ⟨u.val, u.property.1⟩
  have hw (ij) : w ij = H (f ij) := Subtype.ext ((hc ij).trans (hH _).symm)
  let b := Module.Basis.mk hf hs.ge
  let a : Fin 2 × Fin 3 → ℂ := fun ij => b.repr q ij
  have hsum : ∑ ij, a ij • f ij = q := by
    simpa only [a, b, Module.Basis.mk_apply] using b.sum_repr q
  let θ : b3_HolForm ℂ (b65z_fibre c D.C t) := ⟨φ.val (Pi.single 0 1), φ.property.1 _⟩
  have hθ : H q = θ := Subtype.ext ((hH q).trans hchart)
  have hsumw : ∑ ij, a ij • w ij = θ := by
    simp_rw [hw]
    simp_rw [← map_smul H]
    rw [← map_sum H, hsum, hθ]
  let e : (Fin 2 × Fin 3) → b63l_parameterLattice c D.C D.hC
      (b6t_polydisc c) (Subset.refl _) s → ℂ := fun ij x =>
    b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
      (b60_frame (b65z_period D s m t.val) ij)
  have hexp (x) :
      (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val θ =
        ∑ ij, a ij * e ij x := by
    let l := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x
    let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
    change L θ = _
    have hL (ij) : L (w ij) = e ij x := hp ij x
    rw [← hsumw, map_sum]
    simp only [map_smul, hL, smul_eq_mul]
  have he : ∀ ij x, e ij (D.A s x) =
      (if ij.1 = 0 then Complex.I * (Real.sqrt 3 : ℂ)
        else -Complex.I * (Real.sqrt 3 : ℂ)) * e ij x :=
    fun ij x => b66d_frame_period_eigen (D.A s) m hJ _ ij x
  have hcoeff := b66d_eigen_coefficients e
    (b66d_frame_functionals_independent m (b65z_period D s m t.val)) (D.A s)
    (fun ij => if ij.1 = 0 then Complex.I * (Real.sqrt 3 : ℂ)
      else -Complex.I * (Real.sqrt 3 : ℂ)) he a
    (if cj then Complex.I * (Real.sqrt 3 : ℂ) else -Complex.I * (Real.sqrt 3 : ℂ))
    (fun x => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hexp, b66d_transport_form_eigen D s t cj φ, hexp])
  have hne : Complex.I * (Real.sqrt 3 : ℂ) ≠ -Complex.I * (Real.sqrt 3 : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, zero_mul, one_mul,
      neg_zero, neg_mul, zero_add] at hi
    have hpos : 0 < Real.sqrt 3 := by positivity
    linarith
  have hzero (ij : Fin 2 × Fin 3) (hij : ij.1 ≠ (if cj then 0 else 1)) : a ij = 0 := by
    apply (mul_eq_zero.mp (hcoeff ij)).resolve_left
    apply sub_ne_zero.mpr
    rcases ij with ⟨k, i⟩
    cases cj
    · fin_cases k
      · simpa using hne
      · exact False.elim (hij rfl)
    · fin_cases k
      · exact False.elim (hij rfl)
      · simpa using hne.symm
  refine ⟨θ, hchart.symm, fun i => a ((if cj then 0 else 1), i), ?_⟩
  intro x
  rw [hexp, Fintype.sum_prod_type, Fin.sum_univ_two]
  cases cj
  · have hz : ∑ j : Fin 3, a (0, j) * e (0, j) x = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hzero (0, j) (by simp), zero_mul])
    rw [hz, zero_add]
    rfl
  · have hz : ∑ j : Fin 3, a (1, j) * e (1, j) x = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hzero (1, j) (by simp), zero_mul])
    rw [hz, add_zero]
    rfl

end HodgeLean.Foundations.Program
