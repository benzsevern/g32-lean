import HodgeLean.Foundations.Program.HurwitzFamilyDefs

/-! # B6-1 proof obligations for the normalized chart and selected fibres -/

noncomputable section

open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6_chart_coordinates_aux (t : Fin 10 → ℂ) :
    t ∈ b6_chart ↔ Function.Injective t ∧ ∀ i, t i ≠ 0 ∧ t i ≠ 1 := by
  change Function.Injective (Fin.append (fun i ↦ (t i : OnePoint ℂ))
    ![((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), OnePoint.infty]) ↔ _
  rw [Fin.append_injective_iff]
  constructor
  · rintro ⟨ht, -, hcross⟩
    constructor
    · intro i j hij
      apply ht
      exact congrArg (fun z : ℂ ↦ (z : OnePoint ℂ)) hij
    · intro i
      constructor
      · intro hi
        apply hcross i 0
        simp [hi]
      · intro hi
        apply hcross i 1
        simp [hi]
  · rintro ⟨ht, havoid⟩
    refine ⟨fun i j hij ↦ ht (OnePoint.coe_injective hij), ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i j
      fin_cases j <;> simp_all

theorem b6_chart_open_aux  :
    IsOpen b6_chart := by
  rw [show b6_chart = {t | Function.Injective t ∧ ∀ i, t i ≠ 0 ∧ t i ≠ 1} by
    ext t
    exact b6_chart_coordinates_aux t]
  have hinj : IsOpen {t : Fin 10 → ℂ | Function.Injective t} := by
    rw [show {t : Fin 10 → ℂ | Function.Injective t} =
        ⋂ i, ⋂ j, ⋂ (_h : i ≠ j), {t | t i ≠ t j} by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro ht i j hij
        exact fun h ↦ hij (ht h)
      · intro ht i j h
        by_contra hij
        exact ht i j hij h]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_iInter_of_finite fun _ ↦
        isOpen_ne_fun (continuous_apply i) (continuous_apply j)
  have hzero : IsOpen {t : Fin 10 → ℂ | ∀ i, t i ≠ 0} := by
    rw [show {t : Fin 10 → ℂ | ∀ i, t i ≠ 0} = ⋂ i, {t | t i ≠ 0} by ext; simp]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_ne_fun (continuous_apply i) continuous_const
  have hone : IsOpen {t : Fin 10 → ℂ | ∀ i, t i ≠ 1} := by
    rw [show {t : Fin 10 → ℂ | ∀ i, t i ≠ 1} = ⋂ i, {t | t i ≠ 1} by ext; simp]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_ne_fun (continuous_apply i) continuous_const
  rw [show {t : Fin 10 → ℂ | Function.Injective t ∧ ∀ i, t i ≠ 0 ∧ t i ≠ 1} =
      {t | Function.Injective t} ∩ {t | ∀ i, t i ≠ 0} ∩ {t | ∀ i, t i ≠ 1} by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    aesop]
  exact (hinj.inter hzero).inter hone

theorem b6_base_mem_aux  :
    b6_base ∈ b6_chart := by
  rw [b6_chart_coordinates_aux]
  constructor
  · intro i j hij
    apply Fin.ext
    simp only [b6_base] at hij
    have h := congrArg Complex.re hij
    simpa using h
  · intro i
    constructor <;> intro h
    · have hr := congrArg Complex.re h
      norm_num [b6_base] at hr
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      linarith
    · have hr := congrArg Complex.re h
      norm_num [b6_base] at hr
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      linarith

theorem b6_branch_continuous_aux (j : Fin 13) :
    Continuous (fun t : (Fin 10 → ℂ) ↦ b6_branch t j) := by
  fin_cases j <;> simp [b6_branch] <;> fun_prop

theorem b6_projection_surjective_aux (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) :
    Function.Surjective (b6_projection G g hg) := by
  intro t
  exact ⟨⟨t, Classical.choice (inferInstance : Nonempty (b6_Cover G g hg t))⟩, rfl⟩

theorem b6_fiber_holomorphic_aux (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b6_coverMap G g hg t) := by
  have hY : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
    have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
    rw [h, finrank_bot]
  exact (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) hY g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1

theorem b6_fiber_geometry_aux (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    b4_IsGaloisCover G (b6_coverMap G g hg t) ∧
      (∀ x, b6_coverMap G g hg t x ∉ Set.range (b6_branch t.val) →
        MulAction.stabilizer G x = ⊥) ∧
      ∀ j, ∃ x, b6_coverMap G g hg t x = b6_branch t.val j ∧
        b4_IsRotGen ℂ x (g j) := by
  have hY : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
    have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
    rw [h, finrank_bot]
  exact (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) hY g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2

theorem b6_fiber_action_holomorphic_aux (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    ∀ a : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b6_Cover G g hg t ↦ a • x) := by
  have hY : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
    have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
    rw [h, finrank_bot]
  exact (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) hY g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1

end HodgeLean.Foundations.Program
