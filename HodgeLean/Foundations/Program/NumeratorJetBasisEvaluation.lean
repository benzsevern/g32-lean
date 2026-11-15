import HodgeLean.Foundations.Program.NumeratorJetBasisCertificates
import HodgeLean.Foundations.Program.NumeratorJetTaylorMatrix
import HodgeLean.Foundations.Program.NumeratorJetResidueJet

/-! # Taylor coefficients of the normalized eigenbases -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- Right multiplication by a constant matrix commutes with Taylor coefficients. -/
theorem b65e_TC_mul_const {m n l : Type*} [Fintype n] {F : ℂ → Matrix m n ℂ} (M : Matrix n l ℂ)
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ F θ * M) k = b65e_TC F k * M := by
  rw [b65e_TC_mul (G := fun _ ↦ M) hF (fun _ _ ↦ analyticAt_const), Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add]
  · simp only [b65e_TC_const, Nat.sub_self, ↓reduceIte]
  · intro a ha
    have := Finset.mem_range.mp ha
    simp only [b65e_TC_const, show k - a ≠ 0 by omega, ↓reduceIte, Matrix.mul_zero]

/-- Left multiplication by a constant matrix commutes with Taylor coefficients. -/
theorem b65e_TC_const_mul {m n l : Type*} [Fintype n] (M : Matrix m n ℂ) {F : ℂ → Matrix n l ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ M * F θ) k = M * b65e_TC F k := by
  rw [b65e_TC_mul (F := fun _ ↦ M) (fun _ _ ↦ analyticAt_const) hF, Finset.sum_range_succ',
    Finset.sum_eq_zero, zero_add]
  · simp only [b65e_TC_const, Nat.sub_zero, ↓reduceIte]
  · intro a _
    simp only [b65e_TC_const, show a + 1 ≠ 0 by omega, ↓reduceIte, Matrix.zero_mul]

/-- Eigenvector recursions with a block normalization have unique solutions. -/
theorem b65e_eigen_unique (A : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (P0 P0i : Matrix (Fin 4) (Fin 4) ℂ)
    (h1 : P0i * P0 = 1) (lam : Fin 4 → ℂ) (hA0 : A 0 * P0 = P0 * diagonal lam)
    (X Y : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (N : ℕ)
    (hX : ∀ k < N, ∑ a ∈ Finset.range (k + 1), A a * X (k - a) = X k * diagonal lam)
    (hY : ∀ k < N, ∑ a ∈ Finset.range (k + 1), A a * Y (k - a) = Y k * diagonal lam)
    (hn : ∀ k < N, ∀ i j, lam i = lam j → (P0i * X k) i j = (P0i * Y k) i j) :
    ∀ k < N, X k = Y k := by
  have h2 : P0 * P0i = 1 := mul_eq_one_comm.mp h1
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hx := hX k hk
    have hy := hY k hk
    rw [Finset.sum_range_succ'] at hx hy
    have hs : ∑ a ∈ Finset.range k, A (a + 1) * X (k - (a + 1)) =
        ∑ a ∈ Finset.range k, A (a + 1) * Y (k - (a + 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have := Finset.mem_range.mp ha
      rw [ih (k - (a + 1)) (by omega) (by omega)]
    simp only [Nat.sub_zero] at hx hy
    have hD : A 0 * (X k - Y k) = (X k - Y k) * diagonal lam := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hx, ← hy, hs]
      abel
    set Z := P0i * (X k - Y k) with hZ
    have hA : A 0 = P0 * diagonal lam * P0i := by
      rw [← hA0, Matrix.mul_assoc, h2, Matrix.mul_one]
    have hc : diagonal lam * Z = Z * diagonal lam := by
      calc
        diagonal lam * Z = P0i * (A 0 * (X k - Y k)) := by
          rw [hA, hZ]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc P0i P0, h1, Matrix.one_mul]
        _ = P0i * ((X k - Y k) * diagonal lam) := by rw [hD]
        _ = Z * diagonal lam := by rw [hZ, Matrix.mul_assoc]
    have hz : Z = 0 := by
      ext i j
      have hij := congrFun (congrFun hc i) j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
      by_cases hl : lam i = lam j
      · rw [hZ, Matrix.mul_sub, Matrix.sub_apply, hn k hk i j hl, sub_self, Matrix.zero_apply]
      · have : (lam i - lam j) * Z i j = 0 := by rw [sub_mul, hij, mul_comm, sub_self]
        rw [Matrix.zero_apply]
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl)
    have : X k - Y k = 0 := by
      rw [← Matrix.one_mul (X k - Y k), ← h2, Matrix.mul_assoc, ← hZ, hz, Matrix.mul_zero]
    exact sub_eq_zero.mp this

/-- Taylor coefficients of the residues are the stored coefficients through order seven. -/
theorem b65e_res_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) (n : ℕ)
    (hn : n < 8) :
    b65e_TC (fun θ ↦ b65q_res O.residue θ q) n = b65e_storedResidue p n q := by
  ext i j
  obtain ⟨P, hP, hc⟩ := b65e_residue_jet_series p O q i j
  simp only [b65e_TC, Matrix.of_apply]
  rw [b65e_T_coeff_of_series hP, hc ⟨n, hn⟩]
  have : (Fin.ofNat 8 n : Fin 8) = ⟨n, hn⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hn])
  simp only [b65e_storedResidue, this]

/-- Fixed-pole residue coefficients are the cast stored rational coefficients. -/
theorem b65e_res_TC_inl (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) (n : ℕ)
    (hn : n < 8) :
    b65e_TC (fun θ ↦ b65q_res O.residue θ (.inl k)) n =
      (b65e_fixedJet (Fin.ofNat 8 n) k).map ι := by
  rw [b65e_res_TC p O _ n hn]
  rfl

/-- Casting a rational convolution of matrices. -/
theorem b65e_map_conv {m n l : Type*} [Fintype n] (A : ℕ → Matrix m n ℚ) (B : ℕ → Matrix n l ℚ)
    (k : ℕ) :
    (∑ a ∈ Finset.range (k + 1), A a * B (k - a)).map ι =
      ∑ a ∈ Finset.range (k + 1), (A a).map ι * (B (k - a)).map ι := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.mul_apply, map_sum, map_mul]

/-- The normalized eigenbases have the stored Taylor coefficients through order seven. -/
theorem b65e_basis_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_basis O.residue θ k) n =
      (b65e_basisJetQ k (Fin.ofNat 8 n)).map ι := by
  obtain ⟨ε, hε, hεr, hgood⟩ := b65q_good_disc O
  obtain ⟨hPa, -, hpt⟩ := b65q_normalizations_on O hεr hgood
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hev : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) ε := isOpen_ball.mem_nhds h0
  have hanP : ∀ i j, AnalyticAt ℂ (fun θ ↦ b65q_basis O.residue θ k i j) 0 :=
    fun i j ↦ hPa k i j 0 h0
  have hanA : ∀ i j, AnalyticAt ℂ (fun θ ↦ b65q_res O.residue θ (.inl k) i j) 0 :=
    fun i j ↦ b65q_MatAn.res O _ i j 0 (mem_ball_self O.radius_pos)
  set lam : Fin 4 → ℂ := fun i ↦ ((b65q_lamQ k i : ℚ) : ℂ) with hlamdef
  have hlam : b65p_exponents k = lam := b65q_exponents_cast k
  have hdiag : diagonal lam = (diagonal (b65q_lamQ k)).map ι := by
    ext i j
    simp only [diagonal_apply, Matrix.map_apply, hlamdef]
    split_ifs <;> simp
  have hX : ∀ n, ∑ a ∈ Finset.range (n + 1),
      b65e_TC (fun θ ↦ b65q_res O.residue θ (.inl k)) a *
        b65e_TC (fun θ ↦ b65q_basis O.residue θ k) (n - a) =
      b65e_TC (fun θ ↦ b65q_basis O.residue θ k) n * diagonal lam := by
    intro n
    rw [← b65e_TC_mul hanA hanP, ← b65e_TC_mul_const _ hanP]
    apply b65e_TC_congr
    filter_upwards [hev] with θ hθ
    rw [((hpt θ hθ).1 k).2.1, hlam]
  have hN : ∀ n i j, lam i = lam j →
      ((b65q_P0invQ k).map ι * b65e_TC (fun θ ↦ b65q_basis O.residue θ k) n) i j =
        if n = 0 ∧ i = j then 1 else 0 := by
    intro n i j hij
    rw [← b65e_TC_const_mul _ hanP]
    have hc : (fun θ ↦ ((b65q_P0invQ k).map ι * b65q_basis O.residue θ k) i j) =ᶠ[𝓝 0]
        fun _ ↦ if i = j then (1 : ℂ) else 0 := by
      filter_upwards [hev] with θ hθ
      rw [← b65q_eigen0_inv]
      exact ((hpt θ hθ).1 k).2.2 i j (by rw [hlam]; exact hij)
    simp only [b65e_TC, Matrix.of_apply]
    rw [b65q_T_congr hc, b65q_T_const, PowerSeries.coeff_C]
    by_cases hn : n = 0 <;> by_cases hij' : i = j <;> simp [hn, hij']
  have h1 : (b65q_P0invQ k).map ι * (b65q_P0Q k).map ι = 1 := by
    rw [← Matrix.map_mul, mul_eq_one_comm.mp (b65q_P0Q_mul_inv k),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hA0 : b65e_TC (fun θ ↦ b65q_res O.residue θ (.inl k)) 0 * (b65q_P0Q k).map ι =
      (b65q_P0Q k).map ι * diagonal lam := by
    rw [b65e_TC_zero, b65q_res_zero_inl, ← Matrix.map_mul, b65q_fixed_eig_Q, Matrix.map_mul,
      hdiag]
  intro n hn
  refine b65e_eigen_unique _ _ _ h1 lam hA0 _
    (fun a ↦ (b65e_basisJetQ k (Fin.ofNat 8 a)).map ι) 8 (fun n _ ↦ hX n) ?_ ?_ n hn
  · intro m hm
    have hf : (Fin.ofNat 8 m : Fin 8) = ⟨m, hm⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hm])
    rw [Finset.sum_congr rfl fun a ha ↦ by
      rw [b65e_res_TC_inl p O k a (by have := Finset.mem_range.mp ha; omega)]]
    rw [← b65e_map_conv (fun a ↦ b65e_fixedJet (Fin.ofNat 8 a) k)
      (fun a ↦ b65e_basisJetQ k (Fin.ofNat 8 a)) m]
    have he := b65e_basisJet_eig k ⟨m, hm⟩
    rw [he, Matrix.map_mul, hdiag, hf]
  · intro m hm i j hij
    rw [hN m i j hij, ← Matrix.map_mul, Matrix.map_apply]
    have hq : b65q_lamQ k i = b65q_lamQ k j := by
      have h := hij
      simp only [hlamdef, Rat.cast_inj] at h
      exact h
    have hf : (Fin.ofNat 8 m : Fin 8) = ⟨m, hm⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hm])
    rw [hf, b65e_basisJet_norm k ⟨m, hm⟩ i j hq]
    split_ifs <;> simp

/-- Taylor coefficients of the identity relation for a product equal to one near the centre. -/
theorem b65e_TC_one {n : Type*} [DecidableEq n] (k : ℕ) :
    b65e_TC (fun _ : ℂ ↦ (1 : Matrix n n ℂ)) k = if k = 0 then 1 else 0 :=
  b65e_TC_const 1 k

/-- The inverse eigenbases have the stored Taylor coefficients through order seven. -/
theorem b65e_basisInv_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) (k : Fin 4) :
    ∀ n < 8, b65e_TC (fun θ ↦ (b65q_basis O.residue θ k)⁻¹) n =
      (b65e_basisInvJetQ k (Fin.ofNat 8 n)).map ι := by
  obtain ⟨ε, hε, hεr, hgood⟩ := b65q_good_disc O
  obtain ⟨hPa, -, hpt⟩ := b65q_normalizations_on O hεr hgood
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have hev : ∀ᶠ θ in 𝓝 (0 : ℂ), θ ∈ ball (0 : ℂ) ε := isOpen_ball.mem_nhds h0
  have hP : b65q_MatAn (ball 0 ε) fun θ ↦ b65q_basis O.residue θ k := fun i j ↦ hPa k i j
  have hPi : b65q_MatAn (ball 0 ε) fun θ ↦ (b65q_basis O.residue θ k)⁻¹ :=
    hP.inv fun θ hθ ↦ ((isUnit_iff_isUnit_det _).mp ((hpt θ hθ).1 k).1).ne_zero
  have hanP : ∀ i j, AnalyticAt ℂ (fun θ ↦ b65q_basis O.residue θ k i j) 0 :=
    fun i j ↦ hP i j 0 h0
  have hanPi : ∀ i j, AnalyticAt ℂ (fun θ ↦ (b65q_basis O.residue θ k)⁻¹ i j) 0 :=
    fun i j ↦ hPi i j 0 h0
  have hL0 : (b65q_P0invQ k).map ι * b65e_TC (fun θ ↦ b65q_basis O.residue θ k) 0 = 1 := by
    rw [b65e_TC_zero, b65q_basis_zero, b65q_eigen0_cast, ← Matrix.map_mul,
      mul_eq_one_comm.mp (b65q_P0Q_mul_inv k), Matrix.map_one _ (map_zero _) (map_one _)]
  intro n hn
  refine b65e_conv_unique (fun a ↦ b65e_TC (fun θ ↦ b65q_basis O.residue θ k) a) _ hL0 _
    (fun a ↦ (b65e_basisInvJetQ k (Fin.ofNat 8 a)).map ι) 8 ?_ n hn
  intro m hm
  have hf : (Fin.ofNat 8 m : Fin 8) = ⟨m, hm⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hm])
  rw [← b65e_TC_mul hanP hanPi]
  rw [b65e_TC_congr (G := fun _ ↦ (1 : Matrix (Fin 4) (Fin 4) ℂ)) (by
    filter_upwards [hev] with θ hθ
    exact Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp ((hpt θ hθ).1 k).1))]
  rw [Finset.sum_congr rfl fun a ha ↦ by
    rw [b65e_basis_TC p O k a (by have := Finset.mem_range.mp ha; omega)]]
  rw [← b65e_map_conv (fun a ↦ b65e_basisJetQ k (Fin.ofNat 8 a))
    (fun a ↦ b65e_basisInvJetQ k (Fin.ofNat 8 a)) m]
  have he := b65e_basisInvJet_mul k ⟨m, hm⟩
  rw [he, b65e_TC_one]
  split_ifs <;> simp

end HodgeLean.Foundations.Program
