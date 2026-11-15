import HodgeLean.Foundations.Program.CodifferentialComparisonFunctionalProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonBasisProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonTransportProofs
import HodgeLean.Foundations.Program.NumeratorJet
import HodgeLean.Foundations.Program.PeriodBasisAlignment

/-! Proofs for the codifferential comparison at the G32 centre (stage 6e). -/
noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b3Forms_isManifold_real
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b66f_polarized_matrix_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        s (D.P s) (D.Q s)).baseChange ℚ x y) :
    ∃ (q r : Fin 3 → b66f_primitiveForms D t)
      (ω η : Fin 3 → b3_HolForm ℂ (b65z_fibre c D.C t)) (κ : ℂ),
      (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
        κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
      (∀ i, (ω i).val = b66f_chartForm D t (q i).val ∧
        (η i).val = b66f_chartForm D t (r i).val) ∧
      LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∧
      Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 3 =>
        if ij.1 = 0 then q ij.2 else r ij.2)) = ⊤ ∧
      (∀ (i : Fin 3) (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s),
        (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val (ω i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b65z_period D s m t.val) (0, i)) ∧
        (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val (η i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b65z_period D s m t.val) (1, i))) ∧
      IsUnit (b66m_leftMatrix (b65z_period D s m t.val) κ) ∧
      ∀ (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
      (_hmero : ∀ j a z, z ∈ b66f_domain D t a → MeromorphicAt (v j a) z)
      (_hreg : ∀ j a z, z ∈ b66f_domain D t a →
        ((D.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
      (_hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (D.atlas.A a).source →
        (t, x) ∈ (D.atlas.A b).source →
        b66f_cocycle D t (Pi.single j 1) a b x = b66f_boundary D t (v j) a b x),
        b66f_multiplicationMatrix D t q r S v =
          b66m_leftMatrix (b65z_period D s m t.val) κ *
            LinearMap.toMatrix' (fderiv ℂ (b65z_period D s m) t.val).toLinearMap *
              (1 : Matrix (Fin 10) (Fin 10) ℂ) := by
  letI := b3_periodLattice_finite (E := ℂ) (C := b65z_fibre c D.C t) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := b65z_fibre c D.C t)
  let b := Module.Free.chooseBasis ℤ (b3_periodLattice ℂ (b65z_fibre c D.C t))
  let w := fun ij : Fin 2 × Fin 3 => b66f_gen_b66m_polarizedHarmonicForm D t b
    (b66f_gen_b66m_primitiveFullVector D s t m (b60_frame (b65z_period D s m t.val) ij))
  have hf (ij : Fin 2 × Fin 3) :
      ∃ q : b66f_primitiveForms D t, (w ij).val = b66f_chartForm D t q.val := by
    apply b66f_gen_b66m_primitive_coefficient_of_holProjector hg D t (w ij)
    exact b66f_gen_b66m_primitiveFullVector_holProjector hg D s t m hJ hpol b _
      (Submodule.subset_span ⟨ij, rfl⟩)
  choose f hc using hf
  have hp (ij : Fin 2 × Fin 3)
      (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) :
      (b63e_transportMap c D.C D.hC (b6t_polydisc c)
        (Subset.refl _) D.P s t x).val (w ij) =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b65z_period D s m t.val) ij) :=
    b66f_gen_b66m_primitiveFullVector_period hg D s t m hJ hpol b _
      (Submodule.subset_span ⟨ij, rfl⟩) x
  have hi := b66f_gen_b66m_chart_frames_independent hg D t f w hc
    (b66f_gen_b66m_normalized_frames_independent D s t m w hp)
  have hs := b66f_gen_b66m_primitive_frame_span hg D t f hi
  let q := fun i => f (0, i)
  let r := fun i => f (1, i)
  let κ : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)⁻¹
  have heq : (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) = f := by
    funext ij
    obtain ⟨a, i⟩ := ij
    fin_cases a <;> simp [q, r]
  refine ⟨q, r, (fun i => w (0, i)), (fun i => w (1, i)), κ,
    Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hc (0, i), hc (1, i)⟩
  · rwa [heq]
  · rwa [heq]
  · intro i x
    exact ⟨hp (0, i) x, hp (1, i) x⟩
  · apply b66m_leftMatrix_isUnit
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero))
  · intro S v hm hr hv
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
      (M := b65z_fibre c D.C t) isClosed_univ
      (fun a => {y : b65z_fibre c D.C t | y.val ∈ (D.atlas.A a).source})
      (fun a => b66f_gen_b66m_sc_open_source D t a)
      (fun y _ => mem_iUnion.mpr ⟨y.val, (D.atlas.hA y.val).1⟩)
    rw [Matrix.mul_one]
    ext a j
    let ij := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a
    let c := b66f_gen_b66m_sc_cechProjection D t
      ⟨b66f_gen_b66g_contract D (q ij.1).val (b66f_cocycle D t (Pi.single j 1)),
        b66f_gen_b66m_rs_contract_mem D t (q ij.1).property.1
          (b66f_gen_b66k_cocycle_mem D t (Pi.single j 1))⟩
    rw [b66f_gen_b66m_multiplicationMatrix_trace hg D t ρ hρ q r (fun i => w (1, i))
      (fun i => hc (1, i)) S v hm hr hv a j c rfl]
    change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * b66f_gen_b66m_cechTrace D t ρ hρ c (w (1, ij.2)) = _
    rw [b66f_gen_b66m_normalized_contraction_trace hg D s t m hJ hpol b ρ hρ
      (q ij.1) (w (0, ij.1)) ij.1 ij.2 (Pi.single j 1) (hc (0, ij.1)) (hp (0, ij.1)),
      b66m_leftMatrix_mul_apply, LinearMap.toMatrix'_apply]
    dsimp only [κ, ij]
    simp only [ContinuousLinearMap.coe_coe]
    ring

theorem b66f_numerator_codiff_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (hker : ∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0)
    (hdict : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ ht : b65p_curve p θ ∈ b6t_polydisc (b65z_centre p),
      ∃ (q r : Fin 3 → b66f_primitiveForms D ⟨b65p_curve p θ, ht⟩)
        (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
        (A : Matrix (Fin 9) (Fin 9) ℂ) (B : Matrix (Fin 10) (Fin 10) ℂ),
        (∀ i, (q i).val ∈
          b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩ m 0) ∧
        (∀ i, (r i).val ∈
          b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩ m 1) ∧
        LinearIndependent ℂ q ∧ LinearIndependent ℂ r ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a → MeromorphicAt (v j a) z) ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a →
          ((D.atlas.A a).symm (b65p_curve p θ, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z) ∧
        (∀ j a b x, x ∉ S j → (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A a).source →
          (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A b).source →
          b66f_cocycle D ⟨b65p_curve p θ, ht⟩ (Pi.single j 1) a b x =
            b66f_boundary D ⟨b65p_curve p θ, ht⟩ (v j) a b x) ∧
        IsUnit A ∧ IsUnit B ∧
        b65q_numMatrix p O.residue θ =
          A * b66f_multiplicationMatrix D ⟨b65p_curve p θ, ht⟩ q r S v * B) :
    ∀ᶠ θ in 𝓝 (0 : ℂ),
      ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
        IsUnit L ∧ IsUnit T ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ
            (b65z_period D (b65z_s₀ (b65z_centre p)) m)
            (b65p_curve p θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T := by
  filter_upwards [(b65e_certified_numMatrix p O hker).1, hdict] with θ hnum hd
  obtain ⟨ht, q, r, S, v, A, B, hq, hr, hqi, hri, hm, hreg, hv, hA, hB, hdictEq⟩ := hd
  let t : b6t_polydisc (b65z_centre p) := ⟨b65p_curve p θ, ht⟩
  obtain ⟨q₀, r₀, ω, η, κ, _, hc, hi, _, hp, hΛ, hM⟩ :=
    b66f_polarized_matrix_aux hg D (b65z_s₀ (b65z_centre p)) t m hJ hpair
  have hq₀ (i) : (q₀ i).val ∈ b66f_direction D (b65z_s₀ (b65z_centre p)) t m 0 := by
    refine ⟨ω i, (hc i).1, Pi.single i 1, ?_⟩
    intro x
    simpa [Pi.single_apply] using (hp i x).1
  have hr₀ (i) : (r₀ i).val ∈ b66f_direction D (b65z_s₀ (b65z_centre p)) t m 1 := by
    refine ⟨η i, (hc i).2, Pi.single i 1, ?_⟩
    intro x
    simpa [Pi.single_apply] using (hp i x).2
  have hqi₀ : LinearIndependent ℂ q₀ := by
    have hh := hi.comp (fun i : Fin 3 => ((0 : Fin 2), i))
      (fun _ _ h => congrArg Prod.snd h)
    simpa [Function.comp_def] using hh
  have hri₀ : LinearIndependent ℂ r₀ := by
    have hh := hi.comp (fun i : Fin 3 => ((1 : Fin 2), i))
      (fun _ _ h => congrArg Prod.snd h)
    simpa [Function.comp_def] using hh
  obtain ⟨P, hP, hqP⟩ := b66f_direction_change_aux hg D
    (b65z_s₀ (b65z_centre p)) t m hJ hpair 0 q₀ q hq₀ hq hqi₀ hqi
  obtain ⟨R, hR, hrR⟩ := b66f_direction_change_aux hg D
    (b65z_s₀ (b65z_centre p)) t m hJ hpair 1 r₀ r hr₀ hr hri₀ hri
  refine ⟨A * b66e_productChange P R * b66m_leftMatrix (b65z_period D
    (b65z_s₀ (b65z_centre p)) m t.val) κ, B,
    (hA.mul (b66e_productChange_unit P R hP hR)).mul hΛ, hB, ?_⟩
  rw [← hnum, hdictEq, hqP, hrR,
    b66f_multiplication_transport_aux D t q₀ r₀ P R S v hm, hM S v hm hreg hv,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]
  rfl

end HodgeLean.Foundations.Program
