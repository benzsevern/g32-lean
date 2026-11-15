import HodgeLean.Foundations.Program.BraidBridgesTwo
import HodgeLean.Foundations.Program.PullbackMonodromyFoundations

/-! # Apparent-puncture filling for the downstairs marking

The downstairs marking composed with the rational map is tied to the pullback transport, so it
descends through the filling of the apparent poles and source infinity. Inclusion of the regular
plane in the sphere is onto on fundamental groups, so the descended marking is unique.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The puncture-filling statement in the proposition form used by `b65t_descent`. -/
theorem b65x_fillProp : b65t_FillProp := fun X hX F x ↦ b65t_puncture_fill X hX F x

/-- The downstairs marking composed with the rational map is tied to the pullback transport. -/
theorem b65x_pull_tied (x : b65s_regular)
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val)
    (γ : Path x x) :
    b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
      (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
        b65r_operator (b4b_toMatrix ((κ.comp (FundamentalGroup.map b65x_phiMap x))
          (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹) := by
  rw [b65t_pullback_transport x x γ]
  exact hC (γ.map b65x_phiMap.continuous)

/-- The descended marking: a homomorphism on the sphere agreeing with the downstairs marking
on every regular loop. -/
theorem b65x_descend (x : b65s_regular)
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val) :
    ∃ σ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      ∀ c : FundamentalGroup b65s_regular x,
        σ (FundamentalGroup.map b65s_inclusion x c) = κ (FundamentalGroup.map b65x_phiMap x c) := by
  obtain ⟨σ, -, hσ⟩ := b65t_descent b65x_fillProp x
    (κ.comp (FundamentalGroup.map b65x_phiMap x)) C (b65x_pull_tied x κ C hC)
  exact ⟨σ, hσ⟩

/-- The plane chart is onto on fundamental groups. -/
theorem b65x_chart_surj (x : b65s_regular) :
    Function.Surjective (FundamentalGroup.map b65t_chart x) := by
  intro c
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep c.asHom
  have hc : c = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient _ _) = c.asHom from hγ]
  refine ⟨FundamentalGroup.fromPath ⟦γ.map b65t_unchart.continuous⟧, ?_⟩
  rw [hc]
  change FundamentalGroup.fromPath ⟦(γ.map b65t_unchart.continuous).map b65t_chart.continuous⟧ =
    FundamentalGroup.fromPath ⟦γ⟧
  congr 2
  ext t
  exact (b65t_elim_mem (γ t)).2

/-- Inclusion of the regular plane in the sphere is onto on fundamental groups. -/
theorem b65x_inclusion_surj (x : b65s_regular) :
    Function.Surjective (FundamentalGroup.map b65s_inclusion x) := by
  intro d
  obtain ⟨d', rfl⟩ := (b65t_puncture_fill b65s_sphere b65t_sphere_open b65t_F (b65t_chart x)).1 d
  obtain ⟨c, rfl⟩ := b65x_chart_surj x d'
  exact ⟨c, b65t_inclusion_map x c⟩

/-- Every class of loops on the sphere at the included base point is the class of a regular
loop. -/
theorem b65x_inclusion_rep (x : b65s_regular)
    (d : FundamentalGroup b65s_sphere (b65s_inclusion x)) :
    ∃ η : Path x x,
      FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧) = d := by
  obtain ⟨c, rfl⟩ := b65x_inclusion_surj x d
  obtain ⟨η, hη⟩ := Quotient.exists_rep c.asHom
  refine ⟨η, ?_⟩
  congr 1
  rw [show (⟦η⟧ : Path.Homotopic.Quotient x x) = c.asHom from hη]

/-- Two homomorphisms on the sphere that agree on every included regular loop are equal. -/
theorem b65x_sphere_ext (x : b65s_regular) {G : Type*} [Group G]
    (ρ ρ' : FundamentalGroup b65s_sphere (b65s_inclusion x) →* G)
    (h : ∀ η : Path x x,
      ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)) =
        ρ' (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧))) :
    ρ = ρ' := by
  ext d
  obtain ⟨η, rfl⟩ := b65x_inclusion_rep x d
  exact h η

/-- Inverse of the slot permutation. -/
def b65x_slotInv : Fin 13 → Fin 13 := ![0, 1, 4, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12]

theorem b65x_slot_slotInv (i : Fin 13) : b65x_slot (b65x_slotInv i) = i := by
  fin_cases i <;> rfl

theorem b65x_slotInv_slot (i : Fin 13) : b65x_slotInv (b65x_slot i) = i := by
  fin_cases i <;> rfl

/-- The downstairs marking sends the image of slot lasso `i` to the initial cut value of slot
`i`: crossing word of the column trace, cut-word lemma and free reduction. -/
theorem b65x_slot_value (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (g : Fin 3 → Path (b65x_phiMap x) (b65x_phiMap x))
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (hκ : ∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j) (i : Fin 13) :
    κ (FundamentalGroup.map b65x_phiMap x (FundamentalGroup.fromPath ⟦δ i⟧)) =
      b65b_initial i := by
  let δc : Fin 13 → Path x x := fun k ↦ δ (b65x_slotInv k)
  have hδc : ∀ k s, (δc k s).val = b65b_inverseNormalization (b65b_lasso k s) := by
    intro k s
    change (δ (b65x_slotInv k) s).val = _
    rw [hδ, b65x_slot_slotInv]
  have htr := b65x_trace_crossings x δc hδc (b65x_slot i)
  have hδi : δc (b65x_slot i) = δ i := by
    change δ (b65x_slotInv (b65x_slot i)) = δ i
    rw [b65x_slotInv_slot]
  rw [hδi] at htr
  have hw := b65x_cut_word g hg _ _ htr
  change κ (FundamentalGroup.fromPath ⟦(δ i).map b65x_phiMap.continuous⟧) = _
  rw [hw, map_list_prod, List.map_map]
  have hfun : (⇑κ ∘ fun a : Fin 3 × ℤ ↦ FundamentalGroup.fromPath ⟦g a.1⟧ ^ a.2) =
      fun a ↦ b65b_cut a.1 ^ a.2 := by
    funext a
    simp only [Function.comp_apply, map_zpow, hκ]
  rw [hfun, b65x_raw_reduction]
  rfl

end HodgeLean.Foundations.Program
