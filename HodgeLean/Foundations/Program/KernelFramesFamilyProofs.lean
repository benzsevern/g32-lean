import HodgeLean.Foundations.Program.KernelFramesFamilyDefs
import HodgeLean.Foundations.Program.KernelFramesFamilyNumerators
import HodgeLean.Foundations.Program.KernelFramesFamilyDictionary

/-! # B6-5 stage 5d, family part: auxiliary bodies

One auxiliary per public statement of `KernelFramesFamily.lean`. The bodies assemble the
modules imported above (base values, normalizations, analytic systems, frames, numerators and
the dictionary).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65q_base_systems_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    b65q_basis O.residue 0 = b65q_eigen0 ∧
    (∀ j : Fin 12, b65q_left O.residue 0 j =
      fun i ↦ ((b65k_left (b65q_fibreIndex j) i : ℚ) : ℂ)) ∧
    b65q_rFamily p O.residue 0 = b65k_rSystem.map (Rat.castHom ℂ) ∧
    b65q_qFamily p O.residue 0 = b65k_qSystem.map (Rat.castHom ℂ) :=
  ⟨b65q_basis_zero O, b65q_left_zero O, b65q_rFamily_zero O, b65q_qFamily_zero O⟩

theorem b65q_normalizations_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ k : Fin 4, ∀ i j : Fin 4,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_basis O.residue θ k i j) (ball 0 ε)) ∧
      (∀ x : Fin 12, ∀ i : Fin 4,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_left O.residue θ x i) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε,
        (∀ k : Fin 4, IsUnit (b65q_basis O.residue θ k) ∧
          b65q_res O.residue θ (Sum.inl k) * b65q_basis O.residue θ k =
            b65q_basis O.residue θ k * diagonal (b65p_exponents k) ∧
          ∀ i j : Fin 4, b65p_exponents k i = b65p_exponents k j →
            ((b65q_eigen0 k)⁻¹ * b65q_basis O.residue θ k) i j = if i = j then 1 else 0) ∧
        ∀ x : Fin 12, b65q_left O.residue θ x ≠ 0 ∧
          b65q_left O.residue θ x ᵥ* b65q_res O.residue θ (Sum.inr x) =
            Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) • b65q_left O.residue θ x ∧
          b65q_left O.residue θ x ⬝ᵥ b65q_u (b65q_fibreIndex x) =
            Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) := by
  obtain ⟨ε, hε, hεr, hgood⟩ := b65q_good_disc O
  exact ⟨ε, hε, hεr, b65q_normalizations_on O hεr hgood⟩

theorem b65q_systems_analytic_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ r : Fin 45, ∀ c : Fin 36,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_rFamily p O.residue θ r c) (ball 0 ε)) ∧
      (∀ r : Fin 57, ∀ c : Fin 48,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_qFamily p O.residue θ r c) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε,
        ((b65q_rFamily p O.residue θ).submatrix b65k_rRows b65k_rPivot).det ≠ 0 ∧
        ((b65q_qFamily p O.residue θ).submatrix b65k_qRows b65k_qPivot).det ≠ 0 := by
  obtain ⟨ε, hε, hεr, hgood, hdet⟩ := b65q_block_disc O
  obtain ⟨hr, hq⟩ := b65q_family_an O hεr hgood
  exact ⟨ε, hε, hεr, fun r c ↦ hr r c, fun r c ↦ hq r c, hdet⟩

theorem b65q_frames_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ i : Fin 36, ∀ f : Fin 3,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_rFrame p O.residue θ i f) (ball 0 ε)) ∧
      (∀ i : Fin 48, ∀ f : Fin 3,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_qFrame p O.residue θ i f) (ball 0 ε)) ∧
      (∀ θ ∈ ball (0 : ℂ) ε,
        LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ b65q_rFrame p O.residue θ i f) ∧
        LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ b65q_qFrame p O.residue θ i f)) ∧
      b65q_rFrame p O.residue 0 = b65k_rKernel.map (Rat.castHom ℂ) ∧
      b65q_qFrame p O.residue 0 = b65k_qKernel.map (Rat.castHom ℂ) ∧
      (∀ a : Fin 3, ∀ j : Fin 4,
        b65q_principal (b65p_poles p 0) (fun i ↦ b65q_rFrame p O.residue 0 i a) j =
          b65q_castRat (b65k_rBase a j)) ∧
      ∀ b : Fin 3, ∀ j : Fin 4,
        b65q_qVector (b65p_poles p 0) p (b65q_left O.residue 0)
            (fun i ↦ b65q_qFrame p O.residue 0 i b) j =
          b65q_castRat (b65k_qBase b j) := by
  obtain ⟨ε, hε, hεr, hgood, hdet⟩ := b65q_block_disc O
  obtain ⟨hr, hq⟩ := b65q_family_an O hεr hgood
  refine ⟨ε, hε, hεr, fun i f ↦ ?_, fun i f ↦ ?_, fun θ _ ↦ ?_, b65q_rFrame_zero O,
    b65q_qFrame_zero O, b65q_principal_frame_zero O, b65q_qVector_frame_zero O⟩
  · simp only [b65q_rFrame_eq]
    exact b65q_ibFrame_an _ _ _ hr (fun θ hθ ↦ (hdet θ hθ).1) i f
  · simp only [b65q_qFrame_eq]
    exact b65q_ibFrame_an _ _ _ hq (fun θ hθ ↦ (hdet θ hθ).2) i f
  · simp only [b65q_rFrame_eq, b65q_qFrame_eq]
    exact ⟨b65q_ibFrame_linInd _ _ _ _ b65k_r_bijective,
      b65q_ibFrame_linInd _ _ _ _ b65k_q_bijective⟩

theorem b65q_frames_kernel_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      (b65q_rFamily p O.residue θ).submatrix b65k_rRows id * b65q_rFrame p O.residue θ = 0 ∧
      (b65q_qFamily p O.residue θ).submatrix b65k_qRows id * b65q_qFrame p O.residue θ = 0 ∧
      LinearMap.ker (b65q_rFamily p O.residue θ).mulVecLin ≤
        Submodule.span ℂ (Set.range fun f : Fin 3 ↦ fun i ↦ b65q_rFrame p O.residue θ i f) ∧
      LinearMap.ker (b65q_qFamily p O.residue θ).mulVecLin ≤
        Submodule.span ℂ (Set.range fun f : Fin 3 ↦ fun i ↦ b65q_qFrame p O.residue θ i f) ∧
      (b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ↔
        Module.finrank ℂ (LinearMap.ker (b65q_rFamily p O.residue θ).mulVecLin) = 3) ∧
      (b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 ↔
        Module.finrank ℂ (LinearMap.ker (b65q_qFamily p O.residue θ).mulVecLin) = 3) := by
  obtain ⟨ε, hε, hεr, -, hdet⟩ := b65q_block_disc O
  refine ⟨ε, hε, hεr, fun θ hθ ↦ ?_⟩
  obtain ⟨hr, hq⟩ := hdet θ hθ
  simp only [b65q_rFrame_eq, b65q_qFrame_eq]
  exact ⟨b65q_ibFrame_rows _ _ _ _ b65k_r_bijective hr, b65q_ibFrame_rows _ _ _ _ b65k_q_bijective hq,
    b65q_ibFrame_ker_le _ _ _ _ b65k_r_bijective hr, b65q_ibFrame_ker_le _ _ _ _ b65k_q_bijective hq,
    b65q_ibFrame_iff _ _ _ _ b65k_r_bijective hr, b65q_ibFrame_iff _ _ _ _ b65k_q_bijective hq⟩

theorem b65q_frame_change_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      (∀ c : Matrix (Fin 36) (Fin 3) ℂ, b65q_rFamily p O.residue θ * c = 0 →
        LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ c i f) →
        IsUnit (c.submatrix b65k_rFree id) ∧
        c = b65q_rFrame p O.residue θ * c.submatrix b65k_rFree id ∧
        ∀ M : Matrix (Fin 3) (Fin 3) ℂ, c = b65q_rFrame p O.residue θ * M →
          M = c.submatrix b65k_rFree id) ∧
      ∀ d : Matrix (Fin 48) (Fin 3) ℂ, b65q_qFamily p O.residue θ * d = 0 →
        LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ d i f) →
        IsUnit (d.submatrix b65k_qFree id) ∧
        d = b65q_qFrame p O.residue θ * d.submatrix b65k_qFree id ∧
        ∀ M : Matrix (Fin 3) (Fin 3) ℂ, d = b65q_qFrame p O.residue θ * M →
          M = d.submatrix b65k_qFree id := by
  obtain ⟨ε, hε, hεr, -, hdet⟩ := b65q_block_disc O
  refine ⟨ε, hε, hεr, fun θ hθ ↦ ?_⟩
  obtain ⟨hr, hq⟩ := hdet θ hθ
  simp only [b65q_rFrame_eq, b65q_qFrame_eq]
  exact ⟨fun c hc hli ↦ b65q_ibFrame_change _ _ _ _ b65k_r_bijective hr c hc hli,
    fun d hd hli ↦ b65q_ibFrame_change _ _ _ _ b65k_q_bijective hq d hd hli⟩

theorem b65q_dictionary_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ k : Fin 4, ∃ δ : ℝ, 0 < δ ∧
        (∀ i j : Fin 4,
          AnalyticOnNhd ℂ (fun s ↦ H k s i j) (ball (b65p_fixedPole k) δ)) ∧
        H k (b65p_fixedPole k) = 1 ∧
        ∀ s ∈ ball (b65p_fixedPole k) δ, ∀ i j : Fin 4,
          (s - b65p_fixedPole k) * deriv (fun s ↦ H k s i j) s =
            (diagonal (b65p_exponents k) * H k s - H k s * diagonal (b65p_exponents k) +
              (s - b65p_fixedPole k) • ((b65q_basis O.residue θ k)⁻¹ *
                b65q_regular (b65p_poles p θ) (b65q_res O.residue θ) k s *
                  b65q_basis O.residue θ k * H k s)) i j) →
      b65q_rSpace (b65p_poles p θ) (b65q_basis O.residue θ) H =
          b65q_principal (b65p_poles p θ) '' {c | b65q_rFamily p O.residue θ *ᵥ c = 0} ∧
      b65q_qSpace (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) H =
          b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) ''
            {d | b65q_qFamily p O.residue θ *ᵥ d = 0} ∧
      Function.Injective (b65q_principal (b65p_poles p θ)) ∧
      Function.Injective (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ)) := by
  obtain ⟨ε, hε, hεr, hgood⟩ := b65q_good_disc O
  exact ⟨ε, hε, hεr, b65q_dictionary_on O hεr hgood⟩

theorem b65q_family_numerators_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ θ ∈ ball (0 : ℂ) ε, ∀ (c : Fin 36 → ℂ) (d : Fin 48 → ℂ),
        b65q_rFamily p O.residue θ *ᵥ c = 0 → b65q_qFamily p O.residue θ *ᵥ d = 0 →
        (b65q_product (b65p_poles p θ) p (b65q_left O.residue θ) c d).denom = 1 ∧
        (b65q_product (b65p_poles p θ) p (b65q_left O.residue θ) c d).num.natDegree ≤ 9) ∧
      (∀ θ ∈ ball (0 : ℂ) ε,
        b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 →
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 →
        ∀ a b : Fin 3,
          (∑ j : Fin 10, RatFunc.C (b65q_numMatrix p O.residue θ (finProdFinEquiv (a, b)) j) *
            RatFunc.X ^ j.val) = b65q_frameProduct p O.residue θ a b) ∧
      b65q_numMatrix p O.residue 0 = b65k_baseMatrix.map (Rat.castHom ℂ) := by
  obtain ⟨ε, hε, hεr, hgood, -⟩ := b65q_block_disc O
  obtain ⟨h1, h2⟩ := b65q_family_numerators_on O hεr hgood
  exact ⟨ε, hε, hεr, h1, h2, b65q_numMatrix_zero O⟩

end HodgeLean.Foundations.Program
