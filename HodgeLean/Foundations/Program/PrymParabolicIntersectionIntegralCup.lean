import HodgeLean.Foundations.Program.PrymParabolicIntersectionRestriction

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem hga_integral_evaluation_boundary (c : hg2_Edge b4b_Group 13 → ℤ) :
    hg2_orient.sum (fun τ n ↦ n * hg2_delta1 ℤ ℤ b4b_root c τ) = 0 := by
  let l : (hg2_Edge b4b_Group 13 →₀ ℤ) →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ c
  have he : l ∘ₗ hg2_bd2 ℤ b4b_root =
      Finsupp.linearCombination ℤ (hg2_delta1 ℤ ℤ b4b_root c) := by
    ext τ
    simp [l, hg2_bd2, hg2_delta1, LinearMap.funLeft]
  have h := LinearMap.congr_fun he hg2_orient
  rw [LinearMap.comp_apply, hga_bd2_orient, map_zero] at h
  simpa only [Finsupp.linearCombination_apply, smul_eq_mul] using h.symm

theorem hga_integral_cup_coboundary_left (φ : hg2_Vert b4b_root → ℤ)
    (β : hg2_Edge b4b_Group 13 → ℤ) (hβ : hg2_delta1 ℤ ℤ b4b_root β = 0) :
    hga_cupEval ℤ b4b_root (hg2_delta0 ℤ ℤ b4b_root φ) β = 0 := by
  let c : hg2_Edge b4b_Group 13 → ℤ := fun ε ↦ φ (hg2_src b4b_root ε) * β ε
  have he (τ : hg2_Tri b4b_Group 13) :
      hg2_delta0 ℤ ℤ b4b_root φ (hg2_face2 τ) * β (hg2_face0 b4b_root τ) =
        hg2_delta1 ℤ ℤ b4b_root c τ := by
    have hs : hg2_src b4b_root (hg2_face0 b4b_root τ) =
        hg2_tgt b4b_root (hg2_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · have hc : ((x * (b4b_root i)⁻¹ : b4b_Group) :
            b4b_Group ⧸ Subgroup.zpowers (b4b_root i)) = (x : b4b_Group ⧸ _) := by
          rw [QuotientGroup.eq]
          simp
        simp only [hg2_face0, hg2_src, hg2_face2, hg2_tgt, hc]
    have hs' : hg2_src b4b_root (hg2_face1 τ) =
        hg2_src b4b_root (hg2_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl
    have hb := congrFun hβ τ
    change β (hg2_face0 b4b_root τ) - β (hg2_face1 τ) + β (hg2_face2 τ) = 0 at hb
    change (φ (hg2_tgt b4b_root (hg2_face2 τ)) - φ (hg2_src b4b_root (hg2_face2 τ))) *
      β (hg2_face0 b4b_root τ) = c (hg2_face0 b4b_root τ) - c (hg2_face1 τ) + c (hg2_face2 τ)
    dsimp only [c]
    rw [hs, hs']
    linear_combination -φ (hg2_src b4b_root (hg2_face2 τ)) * hb
  unfold hga_cupEval
  simp_rw [he]
  exact hga_integral_evaluation_boundary c

theorem hga_integral_cup_coboundary_right (α : hg2_Edge b4b_Group 13 → ℤ)
    (hα : hg2_delta1 ℤ ℤ b4b_root α = 0) (φ : hg2_Vert b4b_root → ℤ) :
    hga_cupEval ℤ b4b_root α (hg2_delta0 ℤ ℤ b4b_root φ) = 0 := by
  let c : hg2_Edge b4b_Group 13 → ℤ := fun ε ↦ α ε * φ (hg2_tgt b4b_root ε)
  have he (τ : hg2_Tri b4b_Group 13) :
      α (hg2_face2 τ) * hg2_delta0 ℤ ℤ b4b_root φ (hg2_face0 b4b_root τ) =
        -hg2_delta1 ℤ ℤ b4b_root c τ := by
    have hs : hg2_src b4b_root (hg2_face0 b4b_root τ) =
        hg2_tgt b4b_root (hg2_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · have hc : ((x * (b4b_root i)⁻¹ : b4b_Group) :
            b4b_Group ⧸ Subgroup.zpowers (b4b_root i)) = (x : b4b_Group ⧸ _) := by
          rw [QuotientGroup.eq]
          simp
        simp only [hg2_face0, hg2_src, hg2_face2, hg2_tgt, hc]
    have ht : hg2_tgt b4b_root (hg2_face0 b4b_root τ) =
        hg2_tgt b4b_root (hg2_face1 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · simp only [hg2_face0, hg2_face1, hg2_tgt, hg2_Q_rotate b4b_root b63d_root_product,
          mul_inv_rev, mul_assoc]
    have ha := congrFun hα τ
    change α (hg2_face0 b4b_root τ) - α (hg2_face1 τ) + α (hg2_face2 τ) = 0 at ha
    change α (hg2_face2 τ) *
      (φ (hg2_tgt b4b_root (hg2_face0 b4b_root τ)) - φ (hg2_src b4b_root (hg2_face0 b4b_root τ))) =
        -(c (hg2_face0 b4b_root τ) - c (hg2_face1 τ) + c (hg2_face2 τ))
    dsimp only [c]
    rw [hs, ht]
    linear_combination φ (hg2_tgt b4b_root (hg2_face1 τ)) * ha
  unfold hga_cupEval
  simp_rw [he, mul_neg]
  rw [Finsupp.sum_neg]
  change -(hg2_orient.sum (fun τ n ↦ n * hg2_delta1 ℤ ℤ b4b_root c τ)) = 0
  rw [hga_integral_evaluation_boundary, neg_zero]

theorem hga_cupEval_sub_left (α α' β : hg2_Edge b4b_Group 13 → ℤ) :
    hga_cupEval ℤ b4b_root (α - α') β =
      hga_cupEval ℤ b4b_root α β - hga_cupEval ℤ b4b_root α' β := by
  simp only [hga_cupEval, Pi.sub_apply, sub_mul, mul_sub, Finsupp.sum_sub]

theorem hga_cupEval_sub_right (α β β' : hg2_Edge b4b_Group 13 → ℤ) :
    hga_cupEval ℤ b4b_root α (β - β') =
      hga_cupEval ℤ b4b_root α β - hga_cupEval ℤ b4b_root α β' := by
  simp only [hga_cupEval, Pi.sub_apply, mul_sub, Finsupp.sum_sub]

theorem hga_cupEval_eq_of_cycle_evaluations (α α' β β' : hg2_Edge b4b_Group 13 → ℤ)
    (hα : hg2_delta1 ℤ ℤ b4b_root α' = 0) (hβ : hg2_delta1 ℤ ℤ b4b_root β = 0)
    (ha : ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
      z.1.sum (fun ε n ↦ n * α ε) = z.1.sum (fun ε n ↦ n * α' ε))
    (hb : ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
      z.1.sum (fun ε n ↦ n * β ε) = z.1.sum (fun ε n ↦ n * β' ε)) :
    hga_cupEval ℤ b4b_root α β = hga_cupEval ℤ b4b_root α' β' := by
  obtain ⟨φ, hφ⟩ := hga_integral_coboundary_of_same_cycles b4b_root α α' ha
  obtain ⟨ψ, hψ⟩ := hga_integral_coboundary_of_same_cycles b4b_root β β' hb
  have hl := hga_integral_cup_coboundary_left φ β hβ
  have hr := hga_integral_cup_coboundary_right α' hα ψ
  rw [hφ, hga_cupEval_sub_left] at hl
  rw [hψ, hga_cupEval_sub_right] at hr
  exact (sub_eq_zero.mp hl).trans (sub_eq_zero.mp hr)

theorem hga_orient_evaluation_eq_fundEval {K : Type} [Field K]
    {G : Type} [Group G] [Fintype G] {r : ℕ} (c : hg2_Tri G r → K) :
    hg2_orient.sum (fun τ n ↦ (n : K) * c τ) = hg_fundEval c := by
  classical
  have he : (Finsupp.linearCombination ℤ c) hg2_orient = hg_fundEval c := by
    simp [hg2_orient, hg_fundEval]
  simpa only [Finsupp.linearCombination_apply, zsmul_eq_mul] using he

theorem hga_coefficient_evaluation_boundary {K : Type} [Field K] (c : hg2_Edge b4b_Group 13 → K) :
    hg2_orient.sum (fun τ n ↦ (n : K) * hg2_delta1 K K b4b_root c τ) = 0 := by
  let l : (hg2_Edge b4b_Group 13 →₀ ℤ) →ₗ[ℤ] K := Finsupp.linearCombination ℤ c
  have he : l ∘ₗ hg2_bd2 ℤ b4b_root =
      Finsupp.linearCombination ℤ (hg2_delta1 K K b4b_root c) := by
    ext τ
    simp [l, hg2_bd2, hg2_delta1, LinearMap.funLeft]
  have h := LinearMap.congr_fun he hg2_orient
  rw [LinearMap.comp_apply, hga_bd2_orient, map_zero] at h
  simpa only [Finsupp.linearCombination_apply, zsmul_eq_mul] using h.symm

theorem hga_coefficient_cup_coboundary_left {K : Type} [Field K] (φ : hg2_Vert b4b_root → K)
    (β : hg2_Edge b4b_Group 13 → K) (hβ : hg2_delta1 K K b4b_root β = 0) :
    hga_cupEval K b4b_root (hg2_delta0 K K b4b_root φ) β = 0 := by
  let c : hg2_Edge b4b_Group 13 → K := fun ε ↦ φ (hg2_src b4b_root ε) * β ε
  have he (τ : hg2_Tri b4b_Group 13) :
      hg2_delta0 K K b4b_root φ (hg2_face2 τ) * β (hg2_face0 b4b_root τ) =
        hg2_delta1 K K b4b_root c τ := by
    have hs : hg2_src b4b_root (hg2_face0 b4b_root τ) =
        hg2_tgt b4b_root (hg2_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · have hc : ((x * (b4b_root i)⁻¹ : b4b_Group) :
            b4b_Group ⧸ Subgroup.zpowers (b4b_root i)) = (x : b4b_Group ⧸ _) := by
          rw [QuotientGroup.eq]
          simp
        simp only [hg2_face0, hg2_src, hg2_face2, hg2_tgt, hc]
    have hs' : hg2_src b4b_root (hg2_face1 τ) =
        hg2_src b4b_root (hg2_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl
    have hb := congrFun hβ τ
    change β (hg2_face0 b4b_root τ) - β (hg2_face1 τ) + β (hg2_face2 τ) = 0 at hb
    change (φ (hg2_tgt b4b_root (hg2_face2 τ)) - φ (hg2_src b4b_root (hg2_face2 τ))) *
      β (hg2_face0 b4b_root τ) = c (hg2_face0 b4b_root τ) - c (hg2_face1 τ) + c (hg2_face2 τ)
    dsimp only [c]
    rw [hs, hs']
    linear_combination -φ (hg2_src b4b_root (hg2_face2 τ)) * hb
  unfold hga_cupEval
  simp_rw [he]
  exact hga_coefficient_evaluation_boundary c

theorem hga_coefficient_cup_coboundary_right {K : Type} [Field K] (α : hg2_Edge b4b_Group 13 → K)
    (hα : hg2_delta1 K K b4b_root α = 0) (φ : hg2_Vert b4b_root → K) :
    hga_cupEval K b4b_root α (hg2_delta0 K K b4b_root φ) = 0 := by
  let c : hg2_Edge b4b_Group 13 → K := fun ε ↦ α ε * φ (hg2_tgt b4b_root ε)
  have he (τ : hg2_Tri b4b_Group 13) :
      α (hg2_face2 τ) * hg2_delta0 K K b4b_root φ (hg2_face0 b4b_root τ) =
        -hg2_delta1 K K b4b_root c τ := by
    have hs : hg2_src b4b_root (hg2_face0 b4b_root τ) =
        hg2_tgt b4b_root (hg2_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · have hc : ((x * (b4b_root i)⁻¹ : b4b_Group) :
            b4b_Group ⧸ Subgroup.zpowers (b4b_root i)) = (x : b4b_Group ⧸ _) := by
          rw [QuotientGroup.eq]
          simp
        simp only [hg2_face0, hg2_src, hg2_face2, hg2_tgt, hc]
    have ht : hg2_tgt b4b_root (hg2_face0 b4b_root τ) =
        hg2_tgt b4b_root (hg2_face1 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · simp only [hg2_face0, hg2_face1, hg2_tgt, hg2_Q_rotate b4b_root b63d_root_product,
          mul_inv_rev, mul_assoc]
    have ha := congrFun hα τ
    change α (hg2_face0 b4b_root τ) - α (hg2_face1 τ) + α (hg2_face2 τ) = 0 at ha
    change α (hg2_face2 τ) *
      (φ (hg2_tgt b4b_root (hg2_face0 b4b_root τ)) - φ (hg2_src b4b_root (hg2_face0 b4b_root τ))) =
        -(c (hg2_face0 b4b_root τ) - c (hg2_face1 τ) + c (hg2_face2 τ))
    dsimp only [c]
    rw [hs, ht]
    linear_combination φ (hg2_tgt b4b_root (hg2_face1 τ)) * ha
  unfold hga_cupEval
  simp_rw [he, mul_neg]
  rw [Finsupp.sum_neg]
  change -(hg2_orient.sum (fun τ n ↦ n * hg2_delta1 K K b4b_root c τ)) = 0
  rw [hga_coefficient_evaluation_boundary, neg_zero]

theorem hga_field_cupEval_eq_of_cycle_evaluations {K : Type} [Field K]
    (α α' β β' : hg2_Edge b4b_Group 13 → K)
    (hα : hg2_delta1 K K b4b_root α' = 0) (hβ : hg2_delta1 K K b4b_root β = 0)
    (ha : ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
      z.1.sum (fun ε n ↦ (n : K) * α ε) = z.1.sum (fun ε n ↦ (n : K) * α' ε))
    (hb : ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
      z.1.sum (fun ε n ↦ (n : K) * β ε) = z.1.sum (fun ε n ↦ (n : K) * β' ε)) :
    hga_cupEval K b4b_root α β = hga_cupEval K b4b_root α' β' := by
  have ha0 (z : LinearMap.ker (hg2_bd1 ℤ b4b_root)) :
      z.1.sum (fun ε n ↦ (n : K) * (α - α') ε) = 0 := by
    change (∑ ε ∈ z.1.support, (z.1 ε : K) * (α ε - α' ε)) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (ha z)
  have hb0 (z : LinearMap.ker (hg2_bd1 ℤ b4b_root)) :
      z.1.sum (fun ε n ↦ (n : K) * (β - β') ε) = 0 := by
    change (∑ ε ∈ z.1.support, (z.1 ε : K) * (β ε - β' ε)) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hb z)
  obtain ⟨φ, hφ⟩ := hga_field_coboundary_of_zero_cycles b4b_root (α - α') ha0
  obtain ⟨ψ, hψ⟩ := hga_field_coboundary_of_zero_cycles b4b_root (β - β') hb0
  have hl := hga_coefficient_cup_coboundary_left φ β hβ
  have hr := hga_coefficient_cup_coboundary_right α' hα ψ
  rw [hφ] at hl
  rw [hψ] at hr
  have hleft : hga_cupEval K b4b_root (α - α') β =
      hga_cupEval K b4b_root α β - hga_cupEval K b4b_root α' β := by
    simp only [hga_cupEval, Pi.sub_apply, sub_mul, mul_sub, Finsupp.sum_sub]
  have hright : hga_cupEval K b4b_root α' (β - β') =
      hga_cupEval K b4b_root α' β - hga_cupEval K b4b_root α' β' := by
    simp only [hga_cupEval, Pi.sub_apply, mul_sub, Finsupp.sum_sub]
  rw [hleft] at hl
  rw [hright] at hr
  exact (sub_eq_zero.mp hl).trans (sub_eq_zero.mp hr)

#print axioms hga_field_cupEval_eq_of_cycle_evaluations
#print axioms hga_coefficient_cup_coboundary_right
#print axioms hga_coefficient_cup_coboundary_left
#print axioms hga_coefficient_evaluation_boundary
#print axioms hga_orient_evaluation_eq_fundEval
#print axioms hga_integral_evaluation_boundary
#print axioms hga_integral_cup_coboundary_left
#print axioms hga_integral_cup_coboundary_right

end HodgeLean.Foundations.Program
