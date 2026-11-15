import HodgeLean.Foundations.Program.CoverDictionaryBranch
import HodgeLean.Foundations.Program.CoverDictionaryKernels
import HodgeLean.Foundations.Program.CoverDictionaryUnique
import HodgeLean.Foundations.Program.CoverDictionarySolutions
import HodgeLean.Foundations.Program.CoverDictionaryForward

/-! # B6-5 stage 5d, geometric part: the cover dictionary at the G32 centre (auxiliaries)

One auxiliary per public statement of `CoverDictionary.lean`. The branch-point coordinates use
only the 5c record and Mathlib. Full kernels, frames, frame change, the numerator matrix and the
units are derived from the dictionary on the covers, Chevalley–Weil, the 5d bodies and the
richness of the regular locus. The pulled-back solutions come from all-loop transfer (stage
three) and continuation on the fibres (`CoverDictionarySolutions.lean`). The dictionary uses invariant coefficient descent, holomorphic extension and the 5d kernel images.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65g_cover_solutions_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    Nonempty (b65g_Solutions p O D) :=
  b65g_cover_solutions_main p O D e he x u₀ C hT

set_option maxHeartbeats 400000 in
theorem b65g_dictionary_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∀ c : Fin 36 → ℂ, b65q_rFamily p O.residue θ *ᵥ c = 0 →
        ∃! φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), φ ∈ b65g_homG D t S.conj ∧
          b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) c) φ) ∧
      (∀ φ ∈ b65g_homG D t S.conj, ∃! c : Fin 36 → ℂ, b65q_rFamily p O.residue θ *ᵥ c = 0 ∧
          b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) c) φ) ∧
      (∀ d : Fin 48 → ℂ, b65q_qFamily p O.residue θ *ᵥ d = 0 →
        ∃! ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), ψ ∈ b65g_homG D t (!S.conj) ∧
          b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ) ∧
      ∀ ψ ∈ b65g_homG D t (!S.conj), ∃! d : Fin 48 → ℂ, b65q_qFamily p O.residue θ *ᵥ d = 0 ∧
          b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ := by
  obtain ⟨εR, hεR, hεRS, hrat⟩ := b65g_rational_representations_near S
  obtain ⟨εG, hεG, -, hgauge⟩ := b65g_fixed_gauge O
  obtain ⟨εD, hεD, -, hdict⟩ := b65q_dictionary p O
  refine ⟨min εR (min εG εD), lt_min hεR (lt_min hεG hεD),
    (min_le_left _ _).trans hεRS, fun θ hθ t ht ↦ ?_⟩
  have hθR : θ ∈ ball (0 : ℂ) εR := ball_subset_ball (min_le_left _ _) hθ
  have hθG : θ ∈ ball (0 : ℂ) εG :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hθ
  have hθD : θ ∈ ball (0 : ℂ) εD :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hθ
  have hθS : θ ∈ ball (0 : ℂ) S.radius := ball_subset_ball hεRS hθR
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθS
  choose H hH G hGm hGu hGd using hgauge θ hθG
  have hHa : ∀ k i j, AnalyticAt ℂ (fun s ↦ H k s i j) (b65p_fixedPole k) := by
    intro k i j
    obtain ⟨δ, hδ, ha, -, -⟩ := hH k
    exact ha i j _ (mem_ball_self hδ)
  obtain ⟨hrSpace, hqSpace, hrInj, hqInj⟩ := hdict θ hθD H hH
  obtain ⟨hratR, hratQ⟩ := hrat θ hθR t ht
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' := mul_ne_zero ha hb
  have hba := sub_ne_zero.mpr (Ne.symm hab)
  have hY : ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ), IsUnit (b65g_Y S θ t x).det :=
    fun x hx ↦ b65g_mat_det_ne (S.unit θ hθS t ht x hx)
  have extR := b65g_rForm_extends_iff S θ hθS t ht H G hGm hHa hGu hGd
  have extQ := b65g_qForm_extends_iff S θ hθS t ht H G hGm hHa hGu hGd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    have hreg : ∀ i s, ((b65q_principal (b65p_poles p θ) c) i).denom.eval s = 0 →
        s ∈ Set.range (b65p_poles p θ) := by
      intro i s hs
      by_contra hp
      exact b65g_reg_principal _ c i hp hs
    have hspace : b65q_principal (b65p_poles p θ) c ∈
        b65q_rSpace (b65p_poles p θ) (b65q_basis O.residue θ) H := by
      rw [hrSpace]
      exact ⟨c, hc, rfl⟩
    have hext := (extR _ hreg).mpr hspace
    obtain ⟨φ, hφ, he⟩ := caf_extend_matrix_form_family
      (b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
      {u | u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)}
      (fun u ↦ (b65g_Y S θ t u.1)⁻¹)
      (fun u i ↦ b65q_eval (b65q_principal (b65p_poles p θ) c i)
        (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) u.1))
      (b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11)) hext
    have hrep : b65g_rRepresents D t _ _ _ (b65g_Y S θ t)
        (b65q_principal (b65p_poles p θ) c) φ := he
    refine ⟨φ, ⟨b65g_homG_of_rRepresents S θ hθS t ht _ φ hφ hrep, hrep⟩, ?_⟩
    intro ψ hψ
    exact b65g_rRepresents_unique D t hab' hba _ _ _ ψ φ hψ.1.1 hφ hψ.2 hrep
  · intro φ hφ
    obtain ⟨r, hr, hrep⟩ := hratR φ hφ
    have hspace := (extR r hr).mp (fun v ↦ ⟨φ v, hφ.1 v, hrep v⟩)
    rw [hrSpace] at hspace
    obtain ⟨c, hc, rfl⟩ := hspace
    refine ⟨c, ⟨hc, hrep⟩, ?_⟩
    intro c' hc'
    apply hrInj
    exact b65g_r_eq_of_rep D t hab' hba _ _ hY _ _
      (fun i s hs ↦ ⟨b65g_reg_principal _ _ _ hs, b65g_reg_principal _ _ _ hs⟩)
      φ hc'.2 hrep
  · intro d hd
    have hreg : ∀ i s, ((b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) i).denom.eval s = 0 →
        s ∈ Set.range (b65p_poles p θ) := by
      intro i s hs
      by_contra hp
      exact b65g_reg_qVector _ p _ d i hp hs
    have hspace : b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d ∈
        b65q_qSpace (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) H := by
      rw [hqSpace]
      exact ⟨d, hd, rfl⟩
    have hext := (extQ _ hreg).mpr hspace
    obtain ⟨ψ, hψ, he⟩ := caf_extend_matrix_form_family
      (b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
      {u | u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)}
      (fun u ↦ (b65g_Y S θ t u.1)ᵀ)
      (fun u i ↦ b65q_eval (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d i)
        (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) u.1))
      (b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11)) hext
    have hrep : b65g_qRepresents D t _ _ _ (b65g_Y S θ t)
        (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ := he
    refine ⟨ψ, ⟨b65g_homG_of_qRepresents S θ hθS t ht _ ψ hψ hrep, hrep⟩, ?_⟩
    intro φ hφ
    exact b65g_qRepresents_unique D t hab' hba _ _ _ φ ψ hφ.1.1 hψ hφ.2 hrep
  · intro ψ hψ
    obtain ⟨q, hq, hrep⟩ := hratQ ψ hψ
    have hspace := (extQ q hq).mp (fun v ↦ ⟨ψ v, hψ.1 v, hrep v⟩)
    rw [hqSpace] at hspace
    obtain ⟨d, hd, rfl⟩ := hspace
    refine ⟨d, ⟨hd, hrep⟩, ?_⟩
    intro d' hd'
    apply hqInj
    exact b65g_q_eq_of_rep D t hab' hba _ _ hY _ _
      (fun i s hs ↦ ⟨b65g_reg_qVector _ _ _ _ _ hs, b65g_reg_qVector _ _ _ _ _ hs⟩)
      ψ hd'.2 hrep

theorem b65g_full_kernels_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      Module.finrank ℂ (LinearMap.ker (b65q_rFamily p O.residue θ).mulVecLin) = 3 ∧
      Module.finrank ℂ (LinearMap.ker (b65q_qFamily p O.residue θ).mulVecLin) = 3 ∧
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
      b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 := by
  obtain ⟨ε1, hε1, hε1S, hd⟩ := b65g_dictionary_aux p O g D S
  obtain ⟨ε2, hε2, -, hfk⟩ := b65q_frames_kernel p O
  refine ⟨min ε1 ε2, lt_min hε1 hε2, (min_le_left _ _).trans hε1S, fun θ hθ ↦ ?_⟩
  have hθ1 : θ ∈ ball (0 : ℂ) ε1 := ball_subset_ball (min_le_left _ _) hθ
  have hθ2 : θ ∈ ball (0 : ℂ) ε2 := ball_subset_ball (min_le_right _ _) hθ
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball (hε1S.trans S.radius_le) hθ1
  let t : b6t_polydisc (b65z_centre p) := ⟨b65p_curve p θ, (O.curve_mem θ hθO).1⟩
  obtain ⟨hr1, hr2, hq1, hq2⟩ := hd θ hθ1 t rfl
  have hr : Module.finrank ℂ (LinearMap.ker (b65q_rFamily p O.residue θ).mulVecLin) = 3 := by
    rw [b65g_finrank_transfer (fun c φ ↦ b65g_rRepresents D t (b65p_moving p θ 10)
        (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) c) φ)
      (b65g_homG D t S.conj) _ (b65g_rRep_add D t _ _ _ _) (b65g_rRep_smul D t _ _ _ _)
      (fun c hc ↦ hr1 c (by simpa using hc)) (fun φ hφ ↦ by simpa using hr2 φ hφ),
      b65g_homG_finrank hg D t]
  have hq : Module.finrank ℂ (LinearMap.ker (b65q_qFamily p O.residue θ).mulVecLin) = 3 := by
    rw [b65g_finrank_transfer (fun d ψ ↦ b65g_qRepresents D t (b65p_moving p θ 10)
        (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
        (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ)
      (b65g_homG D t (!S.conj)) _ (b65g_qRep_add D t _ _ _ _ _ _) (b65g_qRep_smul D t _ _ _ _ _ _)
      (fun d hd ↦ hq1 d (by simpa using hd)) (fun ψ hψ ↦ by simpa using hq2 ψ hψ),
      b65g_homG_finrank hg D t]
  obtain ⟨-, -, -, -, hfr, hfq⟩ := hfk θ hθ2
  exact ⟨hr, hq, hfr.mpr hr, hfq.mpr hq⟩

theorem b65g_frames_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∃ φ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ a, φ a ∈ b65g_homG D t S.conj ∧ b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) (φ a)) ∧
        LinearIndependent ℂ φ ∧ Submodule.span ℂ (Set.range φ) = b65g_homG D t S.conj) ∧
      ∃ ψ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ b, ψ b ∈ b65g_homG D t (!S.conj) ∧ b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) (ψ b)) ∧
        LinearIndependent ℂ ψ ∧ Submodule.span ℂ (Set.range ψ) = b65g_homG D t (!S.conj) := by
  obtain ⟨ε1, hε1, hε1S, hd⟩ := b65g_dictionary_aux p O g D S
  obtain ⟨ε2, hε2, -, hk⟩ := b65g_full_kernels_aux p O g hg D S
  obtain ⟨ε3, hε3, -, -, -, hind, -⟩ := b65q_frames p O
  obtain ⟨ε4, hε4, -, hfk⟩ := b65q_frames_kernel p O
  refine ⟨min (min ε1 ε2) (min ε3 ε4), lt_min (lt_min hε1 hε2) (lt_min hε3 hε4),
    (min_le_left _ _).trans ((min_le_left _ _).trans hε1S), fun θ hθ t ht ↦ ?_⟩
  have hθ1 : θ ∈ ball (0 : ℂ) ε1 :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hθ
  have hθ2 : θ ∈ ball (0 : ℂ) ε2 :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hθ
  have hθ3 : θ ∈ ball (0 : ℂ) ε3 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hθ
  have hθ4 : θ ∈ ball (0 : ℂ) ε4 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hθ
  obtain ⟨hr1, hr2, hq1, hq2⟩ := hd θ hθ1 t ht
  obtain ⟨-, -, hkr, hkq⟩ := hk θ hθ2
  obtain ⟨ir, iq⟩ := hind θ hθ3
  obtain ⟨-, -, sr, sq, -, -⟩ := hfk θ hθ4
  constructor
  · refine b65g_basis_transfer (fun c φ ↦ b65g_rRepresents D t (b65p_moving p θ 10)
        (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) c) φ)
      (b65g_homG D t S.conj) _ (b65g_rRep_zero D t _ _ _ _) (b65g_rRep_add D t _ _ _ _)
      (b65g_rRep_smul D t _ _ _ _) (fun c hc ↦ hr1 c (by simpa using hc))
      (fun φ hφ ↦ by simpa using hr2 φ hφ) _ (fun a ↦ ?_) sr ir
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (congrFun hkr i) a
  · refine b65g_basis_transfer (fun d ψ ↦ b65g_qRepresents D t (b65p_moving p θ 10)
        (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
        (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ)
      (b65g_homG D t (!S.conj)) _ (b65g_qRep_zero D t _ _ _ _ _ _) (b65g_qRep_add D t _ _ _ _ _ _)
      (b65g_qRep_smul D t _ _ _ _ _ _) (fun d hd ↦ hq1 d (by simpa using hd))
      (fun ψ hψ ↦ by simpa using hq2 ψ hψ) _ (fun b ↦ ?_) sq iq
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (congrFun hkq i) b

theorem b65g_frame_change_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧
      (∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
        (∀ (β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ),
          (∀ a, β a ∈ b65g_homG D t S.conj) → LinearIndependent ℂ β →
          (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (β a)) →
          IsUnit (c.submatrix b65k_rFree id) ∧
            c = b65q_rFrame p O.residue θ * c.submatrix b65k_rFree id) ∧
        ∀ (β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (d : Matrix (Fin 48) (Fin 3) ℂ),
          (∀ b, β b ∈ b65g_homG D t (!S.conj)) → LinearIndependent ℂ β →
          (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (β b)) →
          IsUnit (d.submatrix b65k_qFree id) ∧
            d = b65q_qFrame p O.residue θ * d.submatrix b65k_qFree id) ∧
      (∀ c : ℂ → Matrix (Fin 36) (Fin 3) ℂ,
        (∀ i f, AnalyticOnNhd ℂ (fun θ ↦ c θ i f) (ball 0 ε)) →
        (∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
          ∃ β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), (∀ a, β a ∈ b65g_homG D t S.conj) ∧ LinearIndependent ℂ β ∧
            ∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c θ i a)) (β a)) →
        (∀ a f, AnalyticOnNhd ℂ (fun θ ↦ (c θ).submatrix b65k_rFree id a f) (ball 0 ε)) ∧
          ∀ θ ∈ ball (0 : ℂ) ε, IsUnit ((c θ).submatrix b65k_rFree id)) ∧
      ∀ d : ℂ → Matrix (Fin 48) (Fin 3) ℂ,
        (∀ i f, AnalyticOnNhd ℂ (fun θ ↦ d θ i f) (ball 0 ε)) →
        (∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
          ∃ β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), (∀ b, β b ∈ b65g_homG D t (!S.conj)) ∧ LinearIndependent ℂ β ∧
            ∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d θ i b)) (β b)) →
        (∀ b f, AnalyticOnNhd ℂ (fun θ ↦ (d θ).submatrix b65k_qFree id b f) (ball 0 ε)) ∧
          ∀ θ ∈ ball (0 : ℂ) ε, IsUnit ((d θ).submatrix b65k_qFree id) := by
  obtain ⟨ε1, hε1, hε1S, hd⟩ := b65g_dictionary_aux p O g D S
  obtain ⟨ε3, hε3, -, hfc⟩ := b65q_frame_change p O
  obtain ⟨ε4, hε4, -, -, -, hnorm⟩ := b65q_normalizations p O
  have hε : 0 < min ε1 (min ε3 ε4) := lt_min hε1 (lt_min hε3 hε4)
  have hεS : min ε1 (min ε3 ε4) ≤ S.radius := (min_le_left _ _).trans hε1S
  have hεO : ∀ θ ∈ ball (0 : ℂ) (min ε1 (min ε3 ε4)), θ ∈ ball (0 : ℂ) O.radius :=
    fun θ hθ ↦ ball_subset_ball (hεS.trans S.radius_le) hθ
  have key : ∀ θ ∈ ball (0 : ℂ) (min ε1 (min ε3 ε4)),
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
        (∀ (β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ),
          (∀ a, β a ∈ b65g_homG D t S.conj) → LinearIndependent ℂ β →
          (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (β a)) →
          IsUnit (c.submatrix b65k_rFree id) ∧
            c = b65q_rFrame p O.residue θ * c.submatrix b65k_rFree id) ∧
        ∀ (β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (d : Matrix (Fin 48) (Fin 3) ℂ),
          (∀ b, β b ∈ b65g_homG D t (!S.conj)) → LinearIndependent ℂ β →
          (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (β b)) →
          IsUnit (d.submatrix b65k_qFree id) ∧
            d = b65q_qFrame p O.residue θ * d.submatrix b65k_qFree id := by
    intro θ hθ t ht
    have hθ1 : θ ∈ ball (0 : ℂ) ε1 := ball_subset_ball (min_le_left _ _) hθ
    have hθ3 : θ ∈ ball (0 : ℂ) ε3 :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hθ
    have hθ4 : θ ∈ ball (0 : ℂ) ε4 :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hθ
    have hθS : θ ∈ ball (0 : ℂ) S.radius := ball_subset_ball hεS hθ
    have hinj := O.poles_injective θ (hεO θ hθ)
    have hinj0 := O.poles_injective 0 (Metric.mem_ball_self O.radius_pos)
    have hne : ∀ i j : Fin 12, i ≠ j → b65p_moving p θ i ≠ b65p_moving p θ j :=
      fun i j hij h ↦ hij (Sum.inr_injective (hinj h))
    have h00 : b65p_poles p θ (Sum.inl 0) = 0 := rfl
    have hne0 : ∀ j : Fin 12, b65p_moving p θ j ≠ 0 := fun j h ↦ by
      have := hinj (h.trans h00.symm); simp at this
    have hab : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero (hne0 _) (hne0 _)
    have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 :=
      sub_ne_zero.mpr (hne _ _ (by decide))
    have hY : ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
        IsUnit (b65g_Y S θ t x).det := fun x hx ↦ b65g_mat_det_ne (S.unit θ hθS t ht x hx)
    have htf : ∀ k b', b' ≠ k → b65p_poles p θ (Sum.inl k) ≠ b65p_poles p θ (Sum.inl b') :=
      fun k b' h e ↦ h (Sum.inl_injective (hinj e)).symm
    have htm : ∀ k x, b65p_poles p θ (Sum.inl k) ≠ b65p_poles p θ (Sum.inr x) :=
      fun k x e ↦ by simpa using hinj e
    have htmm : ∀ x y, y ≠ x → b65p_poles p θ (Sum.inr x) ≠ b65p_poles p θ (Sum.inr y) :=
      fun x y h e ↦ h (Sum.inr_injective (hinj e)).symm
    have hnode : ∀ e, Set.InjOn p (b65q_fibreSet e) := fun e x _ y _ hxy ↦ by
      have : b65p_poles p 0 (Sum.inr x) = b65p_poles p 0 (Sum.inr y) := by
        simpa [b65p_poles] using hxy
      exact Sum.inr_injective (hinj0 this)
    have hw : ∀ x, b65q_left O.residue θ x ≠ 0 := fun x ↦ ((hnorm θ hθ4).2 x).1
    obtain ⟨hr1, hr2, hq1, hq2⟩ := hd θ hθ1 t ht
    obtain ⟨hfr, hfq⟩ := hfc θ hθ3
    constructor
    · intro β c hβ hind hrep
      have hcol : ∀ a, b65q_rFamily p O.residue θ *ᵥ (fun i ↦ c i a) = 0 := by
        intro a
        obtain ⟨c', ⟨hc'K, hc'⟩, -⟩ := hr2 (β a) (hβ a)
        have := b65g_r_eq_of_rep D t hab hba _ _ hY _ _
          (fun j s hs ↦ ⟨b65g_reg_principal _ _ _ hs, b65g_reg_principal _ _ _ hs⟩) (β a)
          (hrep a) hc'
        rw [b65q_principal_injective _ htf this]
        exact hc'K
      have hker : b65q_rFamily p O.residue θ * c = 0 := by
        ext i a
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hcol a) i
      have hli : LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ c i f) := by
        rw [Fintype.linearIndependent_iff]
        intro l hl
        have hr := b65g_rep_finsum (fun c φ ↦ b65g_rRepresents D t (b65p_moving p θ 10)
            (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
            (b65q_principal (b65p_poles p θ) c) φ)
          (b65g_rRep_zero D t _ _ _ _) (b65g_rRep_add D t _ _ _ _) (b65g_rRep_smul D t _ _ _ _)
          Finset.univ l _ β fun a _ ↦ hrep a
        rw [hl] at hr
        obtain ⟨_, -, hu⟩ := hr1 0 (Matrix.mulVec_zero _)
        have e1 := hu _ ⟨Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (hβ a), hr⟩
        have e2 := hu 0 ⟨Submodule.zero_mem _, b65g_rRep_zero D t _ _ _ _⟩
        exact (Fintype.linearIndependent_iff.mp hind) l (e1.trans e2.symm)
      obtain ⟨hu, he, -⟩ := hfr c hker hli
      exact ⟨hu, he⟩
    · intro β d hβ hind hrep
      have hcol : ∀ b, b65q_qFamily p O.residue θ *ᵥ (fun i ↦ d i b) = 0 := by
        intro b
        obtain ⟨d', ⟨hd'K, hd'⟩, -⟩ := hq2 (β b) (hβ b)
        have := b65g_q_eq_of_rep D t hab hba _ _ hY _ _
          (fun j s hs ↦ ⟨b65g_reg_qVector _ _ _ _ _ hs, b65g_reg_qVector _ _ _ _ _ hs⟩) (β b)
          (hrep b) hd'
        rw [b65q_qVector_injective _ p _ htf htm htmm hnode hw this]
        exact hd'K
      have hker : b65q_qFamily p O.residue θ * d = 0 := by
        ext i b
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hcol b) i
      have hli : LinearIndependent ℂ (fun f : Fin 3 ↦ fun i ↦ d i f) := by
        rw [Fintype.linearIndependent_iff]
        intro l hl
        have hr := b65g_rep_finsum (fun d ψ ↦ b65g_qRepresents D t (b65p_moving p θ 10)
            (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
            (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ)
          (b65g_qRep_zero D t _ _ _ _ _ _) (b65g_qRep_add D t _ _ _ _ _ _)
          (b65g_qRep_smul D t _ _ _ _ _ _) Finset.univ l _ β fun b _ ↦ hrep b
        rw [hl] at hr
        obtain ⟨_, -, hu⟩ := hq1 0 (Matrix.mulVec_zero _)
        have e1 := hu _ ⟨Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (hβ b), hr⟩
        have e2 := hu 0 ⟨Submodule.zero_mem _, b65g_qRep_zero D t _ _ _ _ _ _⟩
        exact (Fintype.linearIndependent_iff.mp hind) l (e1.trans e2.symm)
      obtain ⟨hu, he, -⟩ := hfq d hker hli
      exact ⟨hu, he⟩
  refine ⟨min ε1 (min ε3 ε4), hε, hεS, key, ?_, ?_⟩
  · intro c hc hβ
    refine ⟨fun a f ↦ hc (b65k_rFree a) f, fun θ hθ ↦ ?_⟩
    obtain ⟨β, hβm, hind, hrep⟩ := hβ θ hθ ⟨b65p_curve p θ, (O.curve_mem θ (hεO θ hθ)).1⟩ rfl
    exact ((key θ hθ _ rfl).1 β (c θ) hβm hind hrep).1
  · intro d hd hβ
    refine ⟨fun b f ↦ hd (b65k_qFree b) f, fun θ hθ ↦ ?_⟩
    obtain ⟨β, hβm, hind, hrep⟩ := hβ θ hθ ⟨b65p_curve p θ, (O.curve_mem θ (hεO θ hθ)).1⟩ rfl
    exact ((key θ hθ _ rfl).2 β (d θ) hβm hind hrep).1

theorem b65g_numerator_matrix_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (a b : Fin 3) (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)),
        φ ∈ b65g_homG D t S.conj → ψ ∈ b65g_homG D t (!S.conj) →
        b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) φ →
        b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) ψ →
        ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t), u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
          b65g_contract φ ψ u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
            (b65q_numMatrix p O.residue θ (finProdFinEquiv (a, b))) u := by
  obtain ⟨ε, hε, hεS, hk⟩ := b65g_full_kernels_aux p O g hg D S
  exact b65g_numerator_of_kernels p O D S ε hε hεS fun θ hθ ↦ ⟨(hk θ hθ).2.2.1, (hk θ hθ).2.2.2⟩

theorem b65g_units_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
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
          b65q_numMatrix p O.residue θ = b65g_A c d * G := by
  obtain ⟨ε1, hε1, hε1S, hfc, -, -⟩ := b65g_frame_change_aux p O g hg D S
  obtain ⟨ε2, hε2, -, hk⟩ := b65g_full_kernels_aux p O g hg D S
  obtain ⟨ε3, hε3, -, -, hnum, -⟩ := b65q_family_numerators p O
  refine ⟨min ε1 (min ε2 ε3), lt_min hε1 (lt_min hε2 hε3), (min_le_left _ _).trans hε1S, ?_⟩
  intro θ hθ t ht βr βq c d hβr hβq hir hiq hrr hrq
  have hθ1 : θ ∈ ball (0 : ℂ) ε1 := ball_subset_ball (min_le_left _ _) hθ
  have hθ2 : θ ∈ ball (0 : ℂ) ε2 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hθ
  have hθ3 : θ ∈ ball (0 : ℂ) ε3 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hθ
  have hθS : θ ∈ ball (0 : ℂ) S.radius := ball_subset_ball hε1S hθ1
  have hinj := O.poles_injective θ (ball_subset_ball S.radius_le hθS)
  have hne : ∀ i j : Fin 12, i ≠ j → b65p_moving p θ i ≠ b65p_moving p θ j :=
    fun i j hij h ↦ hij (Sum.inr_injective (hinj h))
  have h00 : b65p_poles p θ (Sum.inl 0) = 0 := rfl
  have hne0 : ∀ j : Fin 12, b65p_moving p θ j ≠ 0 := fun j h ↦ by
    have := hinj (h.trans h00.symm); simp at this
  have hab : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero (hne0 _) (hne0 _)
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 :=
    sub_ne_zero.mpr (hne _ _ (by decide))
  obtain ⟨hcu, hce⟩ := (hfc θ hθ1 t ht).1 βr c hβr hir hrr
  obtain ⟨hdu, hde⟩ := (hfc θ hθ1 t ht).2 βq d hβq hiq hrq
  obtain ⟨-, -, hkr, hkq⟩ := hk θ hθ2
  have hcol : ∀ a, (fun i ↦ c i a) =
      ∑ f, c.submatrix b65k_rFree id f a • fun i ↦ b65q_rFrame p O.residue θ i f := fun a ↦ by
    funext i
    refine (congrFun (congrFun hce i) a).trans ?_
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  have hdol : ∀ b, (fun i ↦ d i b) =
      ∑ f, d.submatrix b65k_qFree id f b • fun i ↦ b65q_qFrame p O.residue θ i f := fun b ↦ by
    funext i
    refine (congrFun (congrFun hde i) b).trans ?_
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  set cF := c.submatrix b65k_rFree id
  set dF := d.submatrix b65k_qFree id
  set G0 := b66e_productChange cF dF * b65q_numMatrix p O.residue θ
  have hG0e : ∀ a b k, G0 (finProdFinEquiv (a, b)) k =
      ∑ f, ∑ g, cF f a * dF g b * b65q_numMatrix p O.residue θ (finProdFinEquiv (f, g)) k := by
    intro a b k
    simp only [G0, Matrix.mul_apply]
    rw [← (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp, Fintype.sum_prod_type]
    simp [b66e_productChange]
  have hG0 : ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
      u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
      b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10)
        (b65p_moving p θ 11) (b65p_poles p θ) (G0 (finProdFinEquiv (a, b))) u := by
    intro a b u hu
    refine b65g_numerator_pointwise D t _ _ _ _ _ _ (βr a) (βq b) (hrr a) (hrq b) _ ?_ u hu
      (b65g_mat_det_ne (S.unit θ hθS t ht u.1 hu)) fun j ↦
        ⟨b65g_reg_principal _ _ _ (b65g_good_sFun hu),
          b65g_reg_qVector _ _ _ _ _ (b65g_good_sFun hu)⟩
    simp only [hG0e, hcol a, hdol b, b65g_principal_comb, b65g_qVector_comb]
    have hfp : ∀ f g, (∑ k : Fin 10, RatFunc.C (b65q_numMatrix p O.residue θ
        (finProdFinEquiv (f, g)) k) * RatFunc.X ^ k.val) =
        algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator (b65p_poles p θ)) *
          ∑ j : Fin 4, b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ)
            (fun i ↦ b65q_qFrame p O.residue θ i g) j *
            b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i f) j :=
      fun f g ↦ hnum θ hθ3 hkr hkq f g
    calc _ = ∑ f, ∑ g, RatFunc.C (cF f a) * RatFunc.C (dF g b) *
          ∑ k : Fin 10, RatFunc.C (b65q_numMatrix p O.residue θ (finProdFinEquiv (f, g)) k) *
            RatFunc.X ^ k.val := by
          simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ ↦ ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
      _ = _ := by
          simp only [hfp, Finset.mul_sum, Finset.sum_mul]
          conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun g _ ↦
            Finset.sum_congr rfl fun f _ ↦ by ring
  have huniq : ∀ G : Matrix (Fin 9) (Fin 10) ℂ, (∀ (a b : Fin 3)
      (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
      u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
      b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10)
        (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) → G = G0 := by
    intro G hG
    ext w k
    obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective w
    exact congrFun (b65g_N_eq_of_quadratic D t hab hba _ ⟨Sum.inl 0, h00⟩ _ _
      fun u hu ↦ (hG a b u hu).symm.trans (hG0 a b u hu)) k
  have hcd : IsUnit cF.det := (Matrix.isUnit_iff_isUnit_det _).mp hcu
  have hdd : IsUnit dF.det := (Matrix.isUnit_iff_isUnit_det _).mp hdu
  refine ⟨⟨G0, hG0, fun G hG ↦ huniq G hG⟩, ?_, fun G hG ↦ ?_⟩
  · exact b66e_productChange_unit _ _ (Matrix.isUnit_nonsing_inv_iff.mpr hcu)
      (Matrix.isUnit_nonsing_inv_iff.mpr hdu)
  · rw [huniq G hG, b65g_A, ← Matrix.mul_assoc, b65g_productChange_mul,
      Matrix.mul_nonsing_inv _ hcd, Matrix.mul_nonsing_inv _ hdd, b65g_productChange_one,
      Matrix.one_mul]

theorem b65g_branch_coordinates_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ j k : Fin 10, AnalyticOnNhd ℂ (fun θ ↦ b65g_B p θ j k) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (b65g_branchMatrix p θ) ∧
        ∀ (N : Fin 10 → ℂ) (k : Fin 10),
          Tendsto (fun s : ℂ ↦ (s - b65p_moving p θ (Fin.castLE (by norm_num) k)) *
              (∑ j : Fin 10, N j * s ^ j.val) /
              ((b65q_denominator (b65p_poles p θ)).eval s *
                deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11)) s))
            (𝓝[≠] (b65p_moving p θ (Fin.castLE (by norm_num) k)))
            (𝓝 ((N ᵥ* b65g_branchMatrix p θ) k)) := by
  exact b65g_branch_coordinates_core p O

end HodgeLean.Foundations.Program
