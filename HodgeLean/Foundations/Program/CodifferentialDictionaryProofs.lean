import HodgeLean.Foundations.Program.CodifferentialDictionaryDefs
import HodgeLean.Foundations.Program.CodifferentialDictionaryDirectionRealizationProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryResidueSumProofs

/-! Proofs for the four dictionary statements. -/
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

theorem b66d_matrix_undo (κ : ℂ) (hκ : κ ≠ 0) (π : Equiv.Perm (Fin 9))
    (C : Matrix (Fin 9) (Fin 9) ℂ) (hC : IsUnit C)
    (V : Matrix (Fin 10) (Fin 10) ℂ) (hV : IsUnit V)
    (G M : Matrix (Fin 9) (Fin 10) ℂ)
    (hM : M = κ • ((Matrix.of (fun i j : Fin 9 ↦
      if π i = j then (1 : ℂ) else 0)) * G * V)) :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℂ) (B : Matrix (Fin 10) (Fin 10) ℂ),
      IsUnit A ∧ IsUnit B ∧ C * G = A * M * B := by
  let P : Matrix (Fin 9) (Fin 9) ℂ := π.permMatrix ℂ
  have hP : IsUnit P := by
    have h := (Group.isUnit π⁻¹).map (Matrix.permMatrixHom (R := ℂ) (n := Fin 9))
    simpa only [Matrix.permMatrixHom_apply, inv_inv] using h
  have hKP : IsUnit (κ • P) := by
    have he : κ • P = (algebraMap ℂ (Matrix (Fin 9) (Fin 9) ℂ) κ) * P := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    rw [he]
    exact ((isUnit_iff_ne_zero.mpr hκ).map (algebraMap ℂ _)).mul hP
  refine ⟨C * (κ • P)⁻¹, V⁻¹, hC.mul (Matrix.isUnit_nonsing_inv_iff.mpr hKP),
    Matrix.isUnit_nonsing_inv_iff.mpr hV, ?_⟩
  have he : M = (κ • P) * G * V := by
    rw [Matrix.smul_mul, Matrix.smul_mul]
    convert hM using 2 <;> ext i j <;> simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix, eq_comm]
  rw [he, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.mul_one,
    ← Matrix.mul_assoc (κ • P)⁻¹, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det (κ • P)).mp hKP),
    Matrix.one_mul]

theorem b66d_forms_of_homG_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D) (hconj : S.conj = true)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (t : b6t_polydisc (b65z_centre p)) (conj : Bool) :
    ∃ Φ : b65g_homG D t conj →ₗ[ℂ] b66f_primitiveForms D t,
      Function.Injective Φ ∧
      (∀ φ : b65g_homG D t conj,
        b66f_chartForm D t (Φ φ).val = φ.val (Pi.single 0 1)) ∧
      ∀ φ : b65g_homG D t conj,
        (Φ φ).val ∈ b66f_direction D (b65z_s₀ (b65z_centre p)) t m (b66d_dir S conj) := by
  obtain ⟨Φ, hΦ, hchart⟩ := b66d_chart_realization hg D t conj
  refine ⟨Φ, hΦ, hchart, ?_⟩
  intro φ
  have hlabel : b66d_dir S conj = (if conj then 0 else 1) := by
    cases conj <;> simp [b66d_dir, hconj]
  rw [hlabel]
  exact b66d_direction_of_chart_homG hg D (b65z_s₀ (b65z_centre p)) t m hJ hpair
    conj φ (Φ φ) (hchart φ)

theorem b66d_direction_of_conj_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    b66d_dir S S.conj = 0 ∧ b66d_dir S (!S.conj) = 1 := by
  cases h : S.conj <;> simp [b66d_dir, h]

theorem b66d_residue_normalization_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    : ∃ (κ : ℂ) (π : Equiv.Perm (Fin 9)) (ε : ℝ),
      κ ≠ 0 ∧ 0 < ε ∧ ε ≤ S.radius ∧
      ∀ θ ∈ Metric.ball (0 : ℂ) ε,
      ∀ (t : b6t_polydisc (b65z_centre p)), t.val = b65p_curve p θ →
      ∀ (φ : Fin 3 → b65g_homG D t S.conj)
        (ψ : Fin 3 → b65g_homG D t (!S.conj))
        (q r : Fin 3 → b66f_primitiveForms D t)
        (G : Matrix (Fin 9) (Fin 10) ℂ),
        LinearIndependent ℂ φ → LinearIndependent ℂ ψ →
        (∀ i, b66f_chartForm D t (q i).val = (φ i).val (Pi.single 0 1)) →
        (∀ i, b66f_chartForm D t (r i).val = (ψ i).val (Pi.single 0 1)) →
        (∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
          u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
          b65g_contract (φ a).val (ψ b).val u =
            b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11)
              (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) →
        ∃ (Z : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ),
          (∀ j a z, z ∈ b66f_domain D t a → MeromorphicAt (v j a) z) ∧
          (∀ j a z, z ∈ b66f_domain D t a →
            ((D.atlas.A a).symm (t.val, z)).2 ∉ Z j → AnalyticAt ℂ (v j a) z) ∧
          (∀ j a b x, x ∉ Z j → (t, x) ∈ (D.atlas.A a).source →
            (t, x) ∈ (D.atlas.A b).source →
            b66f_cocycle D t (Pi.single j 1) a b x = b66f_boundary D t (v j) a b x) ∧
          b66f_multiplicationMatrix D t q r Z v =
            κ • ((Matrix.of (fun i j : Fin 9 ↦ if π i = j then (1 : ℂ) else 0)) * G * b65g_branchMatrix p θ) := by
  refine ⟨38880, Equiv.refl _, S.radius, by norm_num, S.radius_pos, le_rfl, ?_⟩
  intro θ hθ t ht φ ψ q r G hφ hψ hq hr hnum
  obtain ⟨hmero, hreg, hcoc⟩ := b66d_standard_velocity_splittings D t
  refine ⟨fun _ => b66d_branchPoles D, b66d_branchLift D, hmero, hreg, hcoc, ?_⟩
  have hθO : θ ∈ ball (0 : ℂ) O.radius := (ball_subset_ball S.radius_le) hθ
  have hperm : Matrix.of (fun i j : Fin 9 =>
      if (Equiv.refl (Fin 9)) i = j then (1 : ℂ) else 0) = (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [hperm, Matrix.one_mul]
  ext i k
  let ab := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i
  change b66f_residueSum D t (b66d_branchPoles D) (b66d_branchLift D k)
    (b66f_multiply D t (q ab.1) (r ab.2)) =
      (38880 : ℂ) * ((G i) ᵥ* b65g_branchMatrix p θ) k
  apply b66d_product_residue_sum p O D hθO t ht k (G i) S.conj
    (φ ab.1) (ψ ab.2) (q ab.1) (r ab.2) (hq ab.1) (hr ab.2)
  intro u hu
  have hi : finProdFinEquiv (ab.1, ab.2) = i :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).apply_symm_apply i
  simpa only [hi] using hnum ab.1 ab.2 u hu

theorem b66d_dictionary_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D) (hconj : S.conj = true)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (hframes : ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∃ φ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ a, φ a ∈ b65g_homG D t S.conj ∧ b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) (φ a)) ∧
        LinearIndependent ℂ φ ∧ Submodule.span ℂ (Set.range φ) = b65g_homG D t S.conj) ∧
      ∃ ψ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ b, ψ b ∈ b65g_homG D t (!S.conj) ∧ b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) (ψ b)) ∧
        LinearIndependent ℂ ψ ∧ Submodule.span ℂ (Set.range ψ) = b65g_homG D t (!S.conj))
    (hunits : ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (βr βq : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ)
        (d : Matrix (Fin 48) (Fin 3) ℂ),
        (∀ a, βr a ∈ b65g_homG D t S.conj) → (∀ b, βq b ∈ b65g_homG D t (!S.conj)) →
        LinearIndependent ℂ βr → LinearIndependent ℂ βq →
        (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (βr a)) →
        (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (βq b)) →
        (∃! G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G) ∧
        IsUnit (b65g_A c d) ∧
        ∀ G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G →
          b65q_numMatrix p O.residue θ = b65g_A c d * G)
    (hbranch : ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ j k : Fin 10, AnalyticOnNhd ℂ (fun θ ↦ b65g_B p θ j k) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (b65g_branchMatrix p θ) ∧
        ∀ (N : Fin 10 → ℂ) (k : Fin 10),
          Tendsto (fun s : ℂ ↦ (s - b65p_moving p θ (Fin.castLE (by norm_num) k)) *
              (∑ j : Fin 10, N j * s ^ j.val) /
              ((b65q_denominator (b65p_poles p θ)).eval s *
                deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11)) s))
            (𝓝[≠] (b65p_moving p θ (Fin.castLE (by norm_num) k)))
            (𝓝 ((N ᵥ* b65g_branchMatrix p θ) k)))
    : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ ht : b65p_curve p θ ∈ b6t_polydisc (b65z_centre p),
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
          A * b66f_multiplicationMatrix D ⟨b65p_curve p θ, ht⟩ q r S v * B := by
  obtain ⟨εf, hf, hfS, hframes⟩ := hframes
  obtain ⟨εu, hu, huS, hunits⟩ := hunits
  obtain ⟨εb, hb, hbO, hbana, hbranch⟩ := hbranch
  obtain ⟨κ, π, εn, hκ, hn, hnS, hnorm⟩ :=
    b66d_residue_normalization_aux p O hg D S m hJ hpair
  have hf' : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) εf := Metric.ball_mem_nhds _ hf
  have hu' : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) εu := Metric.ball_mem_nhds _ hu
  have hb' : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) εb := Metric.ball_mem_nhds _ hb
  have hn' : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) εn := Metric.ball_mem_nhds _ hn
  filter_upwards [hf', hu', hb', hn'] with θ hθf hθu hθb hθn
  have hθO : θ ∈ ball (0 : ℂ) O.radius := (ball_subset_ball hbO) hθb
  let ht := (O.curve_mem θ hθO).1
  let t : b6t_polydisc (b65z_centre p) := ⟨b65p_curve p θ, ht⟩
  obtain ⟨⟨φ, hφ, hiφ, hsφ⟩, ψ, hψ, hiψ, hsψ⟩ := hframes θ hθf t rfl
  let φ' : Fin 3 → b65g_homG D t S.conj := fun i => ⟨φ i, (hφ i).1⟩
  let ψ' : Fin 3 → b65g_homG D t (!S.conj) := fun i => ⟨ψ i, (hψ i).1⟩
  have hiφ' : LinearIndependent ℂ φ' :=
    LinearIndependent.of_comp (b65g_homG D t S.conj).subtype hiφ
  have hiψ' : LinearIndependent ℂ ψ' :=
    LinearIndependent.of_comp (b65g_homG D t (!S.conj)).subtype hiψ
  obtain ⟨Φ, hΦ, hcΦ, hdΦ⟩ := b66d_forms_of_homG_aux p O hg D S hconj m hJ hpair t S.conj
  obtain ⟨Ψ, hΨ, hcΨ, hdΨ⟩ := b66d_forms_of_homG_aux p O hg D S hconj m hJ hpair t (!S.conj)
  let q := Φ ∘ φ'
  let r := Ψ ∘ ψ'
  have hq : LinearIndependent ℂ q := hiφ'.map' Φ (LinearMap.ker_eq_bot_of_injective hΦ)
  have hr : LinearIndependent ℂ r := hiψ'.map' Ψ (LinearMap.ker_eq_bot_of_injective hΨ)
  obtain ⟨⟨G, hG, hGuniq⟩, hA, hnum⟩ := hunits θ hθu t rfl φ ψ
    (b65q_rFrame p O.residue θ) (b65q_qFrame p O.residue θ)
    (fun i => (hφ i).1) (fun i => (hψ i).1) hiφ hiψ
    (fun i => (hφ i).2) (fun i => (hψ i).2)
  obtain ⟨Z, v, hmero, hana, hcoc, hM⟩ := hnorm θ hθn t rfl φ' ψ' q r G
    hiφ' hiψ' (fun i => hcΦ (φ' i)) (fun i => hcΨ (ψ' i)) hG
  obtain ⟨A, B, hA', hB, heq⟩ := b66d_matrix_undo κ hκ π _ hA _
    (hbranch θ hθb).1 G _ hM
  refine ⟨ht, q, r, Z, v, A, B, ?_, ?_, hq, hr, hmero, hana, hcoc, hA', hB, ?_⟩
  · intro i
    have h := hdΦ (φ' i)
    rwa [(b66d_direction_of_conj_aux p O D S).1] at h
  · intro i
    have h := hdΨ (ψ' i)
    rwa [(b66d_direction_of_conj_aux p O D S).2] at h
  · exact (hnum G hG).trans heq


end HodgeLean.Foundations.Program
