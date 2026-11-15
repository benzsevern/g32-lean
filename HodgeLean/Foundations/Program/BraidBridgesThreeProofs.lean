import HodgeLean.Foundations.Program.BraidBridgesTwo
import HodgeLean.Foundations.Program.BraidCertificate
import HodgeLean.Foundations.Program.PullbackMonodromyFoundations
import HodgeLean.Foundations.Program.PrymFamilyExistsDefs
import HodgeLean.Foundations.Program.BraidBridgesThreeFill
import HodgeLean.Foundations.Program.BraidBridgesThreePath
import HodgeLean.Foundations.Program.BraidBridgesThreeLasso
import HodgeLean.Foundations.Program.BraidBridgesThreeMoving
import HodgeLean.Foundations.Program.BraidBridgesThreeRelation
import HodgeLean.Foundations.Program.BraidBridgesThreeMarking

/-! # Braid bridges stage three: open bodies. -/

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_apparent_kernel_aux (x : b65s_regular)
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val)
    (η : Path x x)
    (hη : FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦η⟧) = 1) :
    κ (FundamentalGroup.map b65x_phiMap x
      (FundamentalGroup.fromPath ⟦η⟧)) = 1 := by
  obtain ⟨σ, hσ⟩ := b65x_descend x κ C hC
  rw [← hσ, hη, map_one]

theorem b65x_sphere_marking_aux (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (g : Fin 3 → Path (b65x_phiMap x) (b65x_phiMap x))
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (hκ : ∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val) :
    ∃! ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      (∀ η : Path x x,
        ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)) =
          κ (FundamentalGroup.map b65x_phiMap x (FundamentalGroup.fromPath ⟦η⟧))) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      ∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val := by
  obtain ⟨σ, hσ⟩ := b65x_descend x κ C hC
  refine ⟨σ, ⟨fun η ↦ hσ _, fun i ↦ ?_, fun η ↦ ?_⟩, ?_⟩
  · rw [hσ]
    exact b65x_slot_value x δ hδ g hg κ hκ i
  · rw [hσ]
    exact b65x_pull_tied x κ C hC η
  · rintro ρ' ⟨h1, -, -⟩
    exact b65x_sphere_ext x ρ' σ fun η ↦ by rw [h1, hσ]

theorem b65x_moving_lasso_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :=
  b65x_moving_family p hp

theorem b65x_final_loops_aux (p : Fin 12 → ℂ)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :
    ∃ κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint,
      ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s) :=
  ⟨fun i ↦ b65x_endLoop p (K i) (hKb i) (hKa i), fun _ _ ↦ rfl⟩

theorem b65x_event_moves_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s))
    (χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group)
    (i : Fin 13) :
    χ (b63gP_loops i.rev) =
      b65s_word b65b_pathWord (fun j ↦ χ (FundamentalGroup.fromPath ⟦κ₁ j⟧)) i :=
  b65x_event_moves_body p hp K hK0 hKb hKa κ₁ hκ₁ χ i

theorem b65x_isotopy_marking_aux (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s)) :
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base, ∃ γ : Fin 13 → Path x x,
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      ∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∃ χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group,
          (∀ i, χ (b63gP_loops i) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i⟧))) ∧
          ∀ j, χ (FundamentalGroup.fromPath ⟦κ₁ j⟧) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦δ j⟧)) :=
  b65x_isotopy_marking_body p hp x δ hδ K hK0 hKb hKa κ₁ hκ₁

theorem b65b_path_lasso_transport_aux (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) ∧
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      (∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i.rev⟧)) =
          b65s_word [.positive 3, .positive 2]
            (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
              (FundamentalGroup.fromPath ⟦δ j⟧))) i) := by
  obtain ⟨K, hK0, hKb, hKa⟩ := b65x_moving_lasso_aux p hp
  obtain ⟨κ₁, hκ₁⟩ := b65x_final_loops_aux p K hKb hKa
  obtain ⟨h, γ, htrace, hsrc, hmark⟩ :=
    b65x_isotopy_marking_aux x δ hδ p hp K hK0 hKb hKa κ₁ hκ₁
  refine ⟨K, h, γ, hK0, hKb, hKa, htrace, hsrc, fun ρ i ↦ ?_⟩
  obtain ⟨χ, hχγ, hχκ⟩ := hmark ρ
  rw [← hχγ, b65x_event_moves_aux p hp K hK0 hKb hKa κ₁ hκ₁ χ i]
  change b65s_word b65b_pathWord _ i = b65s_word b65b_pathWord _ i
  congr 1
  funext j
  exact hχκ j

theorem b65b_transported_identification_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ x : b65s_regular,
    ∃ δ : Fin 13 → Path x x,
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
    ∃ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      (∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) ∧
      (∀ i (s : unitInterval),
        (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦γ i.rev⟧)) = b65b_final i) ∧
      (∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val) ∧
      (∀ i, b65f_transport (Fin 4 → ℂ) b65r_pullback
          (fun t ↦ ((γ i.rev).extend t).val) =
        C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) ∧
      b4_SameComponent b65s_columnRoot b65b_final := by
  let x := b65x_basePoint
  let δ : Fin 13 → Path x x := fun i ↦ b65x_lassoPath (b65x_slot i)
  have hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s) :=
    fun _ _ ↦ rfl
  have hy : ∀ k, ¬ b65x_OnCut k (b65x_phiMap x).val := by
    intro k hk
    obtain ⟨u, -, hpos, -, hcut, -⟩ :=
      b65x_trace_crossings x b65x_lassoPath (fun _ _ ↦ rfl) 0
    have h0 : (b65x_lassoPath 0).map b65x_phiMap.continuous 0 = b65x_phiMap x := Path.source _
    obtain ⟨m, -, hm⟩ := (hcut k 0).1 (by rw [h0]; exact hk)
    have hu := (hpos m).1
    rw [← hm] at hu
    simp at hu
  obtain ⟨g, hg⟩ := b65x_cut_generators _ hy
  obtain ⟨κ, hκ, C, hC⟩ := b65x_downstairs_marking _ g hg
  obtain ⟨ρ, ⟨-, hinit, htr⟩, -⟩ := b65x_sphere_marking_aux x δ hδ g hg κ hκ C hC
  obtain ⟨K, h, γ, -, -, -, htrace, -, hmove⟩ := b65b_path_lasso_transport_aux x δ hδ p hp
  have hvals : (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦δ j⟧))) = b65b_initial := funext hinit
  have hfin : ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦γ i.rev⟧)) = b65b_final i := by
    intro i
    rw [hmove ρ i, hvals]
    exact congrFun b65b_path_replay i
  refine ⟨x, δ, h, γ, ρ, C, hδ, htrace, hinit, hfin, htr, fun i ↦ ?_, b65b_component⟩
  rw [htr, hfin, b65b_literal_matrices.2 i]

end HodgeLean.Foundations.Program
