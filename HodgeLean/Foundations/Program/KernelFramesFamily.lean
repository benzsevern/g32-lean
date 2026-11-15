import HodgeLean.Foundations.Program.KernelFramesFamilyProofs
import HodgeLean.Foundations.Program.KernelFrames
import HodgeLean.Papers.G32DominanceDefs

/-! # B6-5 stage 5d, family part: dictionary, kernel systems, frames and numerators

Implication from a stage 5c record `b65p_Outputs p` (the Schlesinger residues along the
normalized path, with their initial values and fixed-pole normal forms) to: the parameter-dependent
45-by-36 and 57-by-48 Laurent systems, analytic near `θ = 0` and equal at `θ = 0` to the printed
`b65k_rSystem` and `b65k_qSystem`; the normalized fixed-pole eigenbases and moving-pole left
eigenvectors of G32 §5.5(2)–(3); a neighbourhood on which both selected blocks stay invertible;
the analytic, independent inverse-block r- and q-frames with the base values of `b65k_`, the
kernel of the selected rows, and the containment of the full kernel in their span; the unique
`3 × 3` change from any independent kernel triple to these frames, its initial value being the
free-coordinate block of the triple; the differential dictionary on the `s`-line (order
conditions at the ramified pole `0`, the apparent poles `3, 1, −2`, the twelve moving poles and
`∞`) as the image of the two kernels; polynomial numerators of degree at most nine for all kernel
pairs; and the ordered `9 × 10` numerator array, equal at `θ = 0` to `b65k_baseMatrix`.

Not claimed: that the kernels stay three-dimensional for `θ ≠ 0` (equivalently that the frames
lie in the full kernels), which needs the identification of the dictionary spaces with
`Hom_G(ρ, H⁰(K_{C_θ}))` on the covers `C_θ`; any statement about covers, the retained cover
family or the B6-3 frames themselves; certification of the numerator array against
`papers8_Mseries` (5e); the codifferential (B6-6). HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- **Base values.** At `θ = 0` the normalized eigenbases are the printed ones, the normalized
left eigenvectors are `v₁`, `v₂`, and the two family systems are the printed rational systems.
Source: G32 v0.16, §5.5(2)–(5), Lemma 5.7 (normal form at the base cover); the record field
`b65p_Outputs.base_coefficient`, which forces the labelled poles to be the roots of `P₅`, `P₋₇`;
`docs/specs/KernelFrames.md`, construction of the literal entries. -/
theorem b65q_base_systems (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    b65q_basis O.residue 0 = b65q_eigen0 ∧
    (∀ j : Fin 12, b65q_left O.residue 0 j =
      fun i ↦ ((b65k_left (b65q_fibreIndex j) i : ℚ) : ℂ)) ∧
    b65q_rFamily p O.residue 0 = b65k_rSystem.map (Rat.castHom ℂ) ∧
    b65q_qFamily p O.residue 0 = b65k_qSystem.map (Rat.castHom ℂ) :=
  b65q_base_systems_aux p O

example := @b65q_base_systems

/-- **Normalized eigenbases and left eigenvectors.** Near `θ = 0` the eigenbases are analytic,
invertible, eigenbases of the residues with the constant ordered exponents, and of the form
`P₀(1 + Y)` with `Y` zero between equal exponents; the left eigenvectors are analytic, nonzero,
left eigenvectors for the constant nonzero eigenvalue, normalized by `wᵀu = tr`.
Source: G32 v0.16, §5.5(2)–(3) and the proof of Lemma 5.8 (Riesz projectors); Lemma 5.6(1)
(the residues stay conjugate). -/
theorem b65q_normalizations (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
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
            Matrix.trace (b65q_res O.residue 0 (Sum.inr x)) :=
  b65q_normalizations_aux p O

example := @b65q_normalizations

/-- **Analytic systems and invertible blocks.** Near `θ = 0` every entry of both family systems
is analytic, and the selected `33 × 33` and `45 × 45` blocks (rows and pivot columns of `b65k_`)
are invertible.
Source: G32 v0.16, Lemma 5.8 (Jets) and its proof: "the block Φ_{R,F'}(0) is invertible, so its
inverse is analytic near 0"; `b65k_r_block`, `b65k_q_block`. -/
theorem b65q_systems_analytic (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ r : Fin 45, ∀ c : Fin 36,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_rFamily p O.residue θ r c) (ball 0 ε)) ∧
      (∀ r : Fin 57, ∀ c : Fin 48,
        AnalyticOnNhd ℂ (fun θ ↦ b65q_qFamily p O.residue θ r c) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε,
        ((b65q_rFamily p O.residue θ).submatrix b65k_rRows b65k_rPivot).det ≠ 0 ∧
        ((b65q_qFamily p O.residue θ).submatrix b65k_qRows b65k_qPivot).det ≠ 0 :=
  b65q_systems_analytic_aux p O

example := @b65q_systems_analytic

/-- **Normalized frames.** Near `θ = 0` the inverse-block frames are analytic and independent;
at `θ = 0` they are the printed kernel columns, and the rational vectors they define are
`b65k_rBase` and `b65k_qBase`.
Source: G32 v0.16, Lemma 5.4 (kernel)(3), §5.5(6), Lemma 5.8; `docs/specs/KernelFrames.md`. -/
theorem b65q_frames (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
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
          b65q_castRat (b65k_qBase b j) :=
  b65q_frames_aux p O

example := @b65q_frames

/-- **Frames and kernels.** Near `θ = 0` the frames solve the selected rows, every kernel vector
of the full system lies in their span, and the frames solve the full system exactly when its
kernel has dimension three.
Source: G32 v0.16, Lemma 5.4 (kernel)(2)–(3) and its proof ("this kernel contains ker Φ"). -/
theorem b65q_frames_kernel (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
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
        Module.finrank ℂ (LinearMap.ker (b65q_qFamily p O.residue θ).mulVecLin) = 3) :=
  b65q_frames_kernel_aux p O

example := @b65q_frames_kernel

/-- **Change of frames.** Near `θ = 0`, any independent triple of kernel vectors of either system
is the frame times a unique invertible `3 × 3` matrix, namely its own free-coordinate block. For
a holomorphic triple, analyticity of this change follows by coordinate projection to its
free-coordinate block; its initial value is that block at `θ = 0`. These provide the algebraic
comparison once the geometric coefficient triples are constructed.
Source: G32 v0.16, Lemma 5.4 (kernel)(3); Remark (The Smith form), analytic changes of the bases;
`docs/specs/PeriodBasisAlignment.md`, review (the bridge `J θ = A θ · b66m_jet · B θ`). -/
theorem b65q_frame_change (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
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
          M = d.submatrix b65k_qFree id :=
  b65q_frame_change_aux p O

example := @b65q_frame_change

/-- **The differential dictionary on the `s`-line.** Near `θ = 0`, for every normal-form gauge
`H` at the four fixed poles (holomorphic, `H(t_k) = 1`, solving the local recursion with the
normalized eigenbasis), the space of rational vectors satisfying the order conditions of the
dictionary at the ramified pole `0`, the apparent poles `3, 1, −2`, the moving poles and `∞` is
the image of the kernel of the family system under the principal-part map, for r and for q; both
maps are injective.
Source: G32 v0.16, Lemma 5.3 (dictionary), Lemma 5.4 (kernel)(1)–(2), §5.5(3)–(5), and the
remark before Lemma 5.3 (changing free resonant entries keeps normal form). -/
theorem b65q_dictionary (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
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
      Function.Injective (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ)) :=
  b65q_dictionary_aux p O

example := @b65q_dictionary

/-- **Family numerators.** Near `θ = 0`, for all kernel vectors of the two systems the product
`D_θ qᵀr` is a polynomial of degree at most nine; wherever the frames solve the full systems,
the ten ordered coefficient columns of `𝐌(θ)` reconstruct the nine frame products; and at
`θ = 0` the array is the printed base array.
Source: G32 v0.16, Lemma 5.3 (dictionary), Lemma 5.5 (numerators), §5.5(7);
`b65k_base_numerator`, `b65k_base_coefficients`. -/
theorem b65q_family_numerators (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
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
      b65q_numMatrix p O.residue 0 = b65k_baseMatrix.map (Rat.castHom ℂ) :=
  b65q_family_numerators_aux p O

example := @b65q_family_numerators

/-- **Non-degeneracy of the dictionary spaces.** For every gauge the zero vector satisfies all
order conditions, while the constant vector `1` violates the condition at `∞`
(`KernelFramesFamilyDefs.lean`), so neither space is empty or everything. -/
example (t : Fin 4 ⊕ Fin 12 → ℂ) (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) : (0 : Fin 4 → RatFunc ℂ) ∈ b65q_rSpace t P H := by
  have h0 : ∀ z, meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) z = ⊤ := fun z ↦ by
    simp [meromorphicOrderAt_const]
  refine ⟨?_, ?_, ?_, fun i ↦ Or.inl rfl⟩
  · intro i s hs; simp at hs
  · intro x i; simp
  · intro k j
    rw [show (fun s ↦ ((P k * H k s)⁻¹ *ᵥ fun i ↦ b65q_eval ((0 : Fin 4 → RatFunc ℂ) i) s) j)
      = fun _ ↦ (0 : ℂ) from by funext s; simp [b65q_eval, ← Pi.zero_def]]
    simp [h0]

example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    (0 : Fin 4 → RatFunc ℂ) ∈ b65q_qSpace t A P H := by
  have h0 : ∀ z, meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) z = ⊤ := fun z ↦ by
    simp [meromorphicOrderAt_const]
  refine ⟨?_, ?_, ?_, ?_, fun i ↦ Or.inl rfl⟩
  · intro i s hs; simp at hs
  · intro x i; simp [b65q_eval, h0]
  · intro x v _; simp [b65q_eval, h0]
  · intro k j
    rw [show (fun s ↦ ((P k * H k s)ᵀ *ᵥ fun i ↦ b65q_eval ((0 : Fin 4 → RatFunc ℂ) i) s) j)
      = fun _ ↦ (0 : ℂ) from by funext s; simp [b65q_eval, ← Pi.zero_def]]
    simp [h0]

/-- **Non-degeneracy of the frames, rank three.** At every parameter the three frame columns
of each system have the identity as free-coordinate block, so neither frame is zero or of rank
less than three. -/
example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) :
    (b65q_rFrame p R θ).submatrix b65k_rFree id = 1 ∧
      (b65q_qFrame p R θ).submatrix b65k_qFree id = 1 := by
  constructor <;> ext a f <;> fin_cases a <;> fin_cases f <;>
    norm_num [b65q_rFrame, b65q_qFrame, b65k_rFree, b65k_qFree, b65k_rPivot, b65k_qPivot,
      Fin.sum_univ_succ, Matrix.one_apply] <;> decide

/-- **Chain check toward `g32r_PeriodMap.jet`.** The family numerator array along the 5c path
has the type of the `jet` field, and with the curve of the same record it fills `curve`,
`curve_cont`, `curve_zero` and `jet`; certification (5e) and the codifferential (B6-6) remain
binders stated for this same array and curve. This derives none of them. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p) (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (hsub : b6t_polydisc (b65p_curve p 0) ⊆ V)
    (period : (Fin 10 → ℂ) → Fin 9 → ℂ) (han : AnalyticOnNhd ℂ period V)
    (hmaps : MapsTo period V (g32m_Domain : Set (Fin 9 → ℂ)))
    (hisog : ∀ t (ht : t ∈ V), ∃ s, g32t_KIsog (P.fiber s) (F.univ ⟨period t, hmaps ht⟩))
    (hjet : g32r_CertifiedJet (b65q_numMatrix p O.residue))
    (hcodiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        b65q_numMatrix p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ period (b65p_curve p θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    Nonempty (g32r_PeriodMap F P) :=
  ⟨{ V := V, isOpen_V := hV, period := period, analytic := han, mapsTo := hmaps,
     isog := hisog, curve := b65p_curve p, curve_cont := O.curve_cont,
     curve_zero := hsub O.curve_zero, jet := b65q_numMatrix p O.residue,
     jet_certified := hjet, codiff := hcodiff }⟩

end HodgeLean.Foundations.Program
