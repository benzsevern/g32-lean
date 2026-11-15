import HodgeLean.Foundations.Program.NumeratorJetProofs
import HodgeLean.Foundations.Program.KernelFramesFamily
import HodgeLean.Papers.G32DominanceDefs

/-! # B6-5 stage 5e: analytic preparation for certification of the numerator jet along the 5c path

Implication from a stage 5c record `O : b65p_Outputs p` (the Schlesinger residues along the
normalized path) to: the Taylor coefficients through order seven of the residues, rational at the
fixed poles and polynomial in the labelled root at the moving poles (G32 v0.16, §5.5(1)); those
of the 5d inverse-block frames `b65q_rFrame`, `b65q_qFrame`; analyticity near `θ = 0` of the
numerator array `b65e_numerator` (the polynomial parts of the 5d frame products
`b65q_frameProduct`), its agreement with the 5d array `b65q_numMatrix` wherever the frames solve
the full systems, and its base value `b65k_baseMatrix`; its Taylor coefficients through order
seven, the explicit rational matrices `b65e_N0`, …, `b65e_N7` of `NumeratorJetData.lean`; the
equality of these with the exported jets `papers8_Mseries` entry by entry; hence
`g32r_CertifiedJet` for `b65e_numerator p O.residue`; and, by implication from the frames solving
the full systems near `0`, eventual equality with `b65q_numMatrix p O.residue` and
`g32r_CertifiedJet` for it.

The certified array is built from the residues of the record, the 5d frames and the 5d products
along the curve `b65p_curve p` of the same record: it is not a polynomial built from the exported
coefficients. The jet `J` of the PeriodBasisAlignment review is this array, on this path. These seven
statements are analytic preparation for stage 5e. Geometric identification needs full kernels
for `θ ≠ 0` and the cover dictionary. The 6e comparison belongs on the `b65z_` family at the
G32 centre (F-2266, F-2267).

Not claimed: that the frames solve the full systems for `θ ≠ 0` (G32 Lemma 5.4(2), which goes
through the covers); the identification of the array with the multiplication `μ_{C_θ}` of
invariant differentials on the covers `C_θ`; the comparison with `b66m_jet`, i.e. units `A θ`,
`B θ` with `J θ = A θ · b66m_jet · B θ` near `0` (6e); the codifferential (B6-6).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- **Residue jets.** Through order seven, the Taylor coefficients at `θ = 0` of every residue of
the record are the listed data: rational matrices at the fixed poles, and at a moving pole the
polynomial `Σ_c (p j)^c · b65e_movingJet n e c` in its labelled root.
Source: G32 v0.16, §5.5(1) (rationality: the Taylor coefficients are traces over `E₅ ⊗ E₋₇`),
Lemma 5.6 (Schlesinger); the record fields `residue_zero`, `residue_analytic`, `schlesinger` and
`base_coefficient` (the labels over `5`, `−7` are the roots of `P₅`, `P₋₇`). -/
theorem b65e_residue_jet (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ q : Fin 4 ⊕ Fin 12, ∀ i j : Fin 4, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = b65e_residueJet p n q i j :=
  b65e_residue_jet_aux p O

example := @b65e_residue_jet

/-- **Frame jets.** Through order seven, the Taylor coefficients at `θ = 0` of the 5d
inverse-block frames along the path are the listed rational matrices.
Source: G32 v0.16, Lemma 5.4 (kernel)(3), §5.5(2)–(6), Lemma 5.8 and its proof; the definitions
`b65q_rFrame`, `b65q_qFrame`; `b65q_frames` (analyticity). -/
theorem b65e_frame_jet (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    (∀ i : Fin 36, ∀ f : Fin 3, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_rFrame p O.residue θ i f) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_rFrameJet n i f : ℂ)) ∧
    ∀ i : Fin 48, ∀ f : Fin 3, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_qFrame p O.residue θ i f) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_qFrameJet n i f : ℂ) :=
  b65e_frame_jet_aux p O

example := @b65e_frame_jet

/-- **The numerator array is analytic.** Near `θ = 0` every entry of `b65e_numerator` is
analytic; wherever the frames solve the full systems it is the 5d array `b65q_numMatrix`; at
`θ = 0` it is the printed base array.
Source: G32 v0.16, Lemma 5.8 (jets) and its proof, §5.5(7); `b65q_frames` (analytic frames),
`b65q_normalizations` (analytic left eigenvectors), `b65q_family_numerators`,
`b65k_base_numerator`. -/
theorem b65e_numerator_analytic (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ i : Fin 9, ∀ j : Fin 10,
        AnalyticOnNhd ℂ (fun θ ↦ b65e_numerator p O.residue θ i j) (ball 0 ε)) ∧
      (∀ θ ∈ ball (0 : ℂ) ε,
        b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 →
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 →
        b65e_numerator p O.residue θ = b65q_numMatrix p O.residue θ) ∧
      b65e_numerator p O.residue 0 = b65k_baseMatrix.map (Rat.castHom ℂ) :=
  b65e_numerator_analytic_aux p O

example := @b65e_numerator_analytic

/-- **Numerator jets.** Through order seven, the Taylor coefficients at `θ = 0` of the numerator
array are the explicit rational matrices `b65e_N0`, …, `b65e_N7`.
Source: G32 v0.16, §5.5(1)–(7), Lemma 5.8 (jets); `NumeratorJetData.lean` (exact computation
from the recursions of 5d). -/
theorem b65e_numerator_jet (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ i : Fin 9, ∀ j : Fin 10, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65e_numerator p O.residue θ i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_N n i j : ℂ) :=
  b65e_numerator_jet_aux p O

example := @b65e_numerator_jet

/-- **Agreement with the export.** For every order `n ≤ 7`, every entry of `b65e_N n` is the
coefficient of `θⁿ` of the same entry of `papers8_Mseries`.
Source: G32 v0.16, Proposition 5.9 and the appendix "The rank certificate";
`data/certificates/g32-rank/M_jets.json`; exact rational comparison. -/
theorem b65e_jet_eq_export :
    ∀ n : Fin 8, ∀ i : Fin 9, ∀ j : Fin 10,
      b65e_N n i j = PowerSeries.coeff (n : ℕ) (papers8_Mseries i j) :=
  b65e_jet_eq_export_aux

example := @b65e_jet_eq_export

/-- **Certified jet.** The numerator array along the path of the record is a certified jet.
Source: G32 v0.16, Lemma 5.8 (jets), Proposition 5.9; `b65e_numerator_jet`,
`b65e_jet_eq_export`. -/
theorem b65e_certified (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    g32r_CertifiedJet (b65e_numerator p O.residue) :=
  b65e_certified_aux p O

example := @b65e_certified

/-- **Certified 5d array, by implication from full kernels.** If near `θ = 0` the frames solve
the full systems (equivalently, by `b65q_frames_kernel`, both kernels are three-dimensional),
then the 5d array `b65q_numMatrix` agrees with `b65e_numerator` near `0` and is a certified jet.
Source: G32 v0.16, Lemma 5.4 (kernel)(2), Lemma 5.8; `b65q_family_numerators`,
`b65e_numerator_analytic`, `b65e_certified`. -/
theorem b65e_certified_numMatrix (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    (∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0) →
      b65q_numMatrix p O.residue =ᶠ[𝓝 0] b65e_numerator p O.residue ∧
        g32r_CertifiedJet (b65q_numMatrix p O.residue) :=
  b65e_certified_numMatrix_aux p O

example := @b65e_certified_numMatrix

/-- **Non-degeneracy of the frame jets.** The free-coordinate blocks of the frame jets are the
identity at order zero and zero at every positive order, as the free-coordinate block of each
frame is `1` at every parameter. -/
example : ∀ n : Fin 8, ∀ a f : Fin 3,
    b65e_rFrameJet n (b65k_rFree a) f = (if n = 0 ∧ a = f then 1 else 0) ∧
      b65e_qFrameJet n (b65k_qFree a) f = (if n = 0 ∧ a = f then 1 else 0) := by
  decide +kernel

/-- **Non-degeneracy of the numerator jet.** The order-one coefficient is not zero, so the
certified array is not constant along the path. -/
example : b65e_N 1 0 0 = 10672605 / 512 := rfl

example : b65e_N 1 ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h 0) 0
  change (10672605 / 512 : ℚ) = 0 at hentry
  norm_num at hentry

/-- **Chain check toward `g32r_PeriodMap`.** The certified array along the 5c path fills `jet`
and `jet_certified`, with the curve of the same record in `curve`, `curve_cont` and
`curve_zero`; `codiff` remains a binder stated for this same array and curve (B6-6, via the 6e
comparison with `b66m_jet`). This derives no other field. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p) (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (hsub : b6t_polydisc (b65p_curve p 0) ⊆ V)
    (period : (Fin 10 → ℂ) → Fin 9 → ℂ) (han : AnalyticOnNhd ℂ period V)
    (hmaps : MapsTo period V (g32m_Domain : Set (Fin 9 → ℂ)))
    (hisog : ∀ t (ht : t ∈ V), ∃ s, g32t_KIsog (P.fiber s) (F.univ ⟨period t, hmaps ht⟩))
    (hcodiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ period (b65p_curve p θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    Nonempty (g32r_PeriodMap F P) :=
  ⟨{ V := V, isOpen_V := hV, period := period, analytic := han, mapsTo := hmaps,
     isog := hisog, curve := b65p_curve p, curve_cont := O.curve_cont,
     curve_zero := hsub O.curve_zero, jet := b65e_numerator p O.residue,
     jet_certified := b65e_certified p O, codiff := hcodiff }⟩

/-- **Chain check for the 5d array.** With full kernels near `0`, the array of the 5d chain check
(`KernelFramesFamily.lean`) receives its certification from `b65e_certified_numMatrix`. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hker : ∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0) :
    g32r_CertifiedJet (b65q_numMatrix p O.residue) :=
  (b65e_certified_numMatrix p O hker).2

end HodgeLean.Foundations.Program
