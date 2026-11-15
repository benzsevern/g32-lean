import HodgeLean.Foundations.HermitianClassC7

noncomputable section
namespace HodgeLean.Foundations.HermitianClass
open HermitianForm

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Rank six, inertia three-three and determinant class minus two give the standard
Hermitian diagonal model.
Source: Landherr classification specialized to the imaginary quadratic field of discriminant
minus twelve, via Meyer isotropy and norm rescaling. -/
theorem hermClass_rank_six_standard (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [FiniteDimensional ℚ W] [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (hrank : Module.finrank (QuadraticAlgebra ℚ (-3) 0) W = 6)
    (hsig : hermSignature h = (3, 3))
    (hdet : detClass h hh hn =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))) :
    ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, diagForm ![1, 1, 1, -1, -1, -2] (e x) (e y) = h x y := by
  let K := QuadraticAlgebra ℚ (-3) 0
  obtain ⟨V₀, V₁, e₁, hn₁, hrank₁', hsig₁', he₁⟩ :=
    hermClass_split_indefinite_pair W h hh hn (hrank ▸ by norm_num)
      (hsig ▸ by norm_num) (hsig ▸ by norm_num)
  let h₁ := (h.domRestrict₁₂ V₀ V₀).domRestrict₁₂ V₁ V₁
  have hh₁ : h₁.IsSymm := (hh.domRestrict V₀).domRestrict V₁
  have hrank₁ : Module.finrank K V₁ = 4 := by
    have heq : 6 = Module.finrank K V₁ + 2 := by
      simpa [K, hrank] using hrank₁'
    omega
  have hsig₁ : hermSignature h₁ = (2, 2) := by
    have heq : (3, 3) =
        ((hermSignature h₁).1 + 1, (hermSignature h₁).2 + 1) := by
      simpa [h₁, hsig] using hsig₁'
    have hp := congrArg Prod.fst heq
    have hm := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  letI : FiniteDimensional ℚ V₀ :=
    FiniteDimensional.of_injective (V₀.subtype.restrictScalars ℚ) V₀.injective_subtype
  letI : FiniteDimensional ℚ V₁ :=
    FiniteDimensional.of_injective (V₁.subtype.restrictScalars ℚ) V₁.injective_subtype
  obtain ⟨U₀, V₂, e₂, hn₂, hrank₂', hsig₂', he₂⟩ :=
    hermClass_split_indefinite_pair V₁ h₁ hh₁ hn₁ (hrank₁ ▸ by norm_num)
      (hsig₁ ▸ by norm_num) (hsig₁ ▸ by norm_num)
  letI : FiniteDimensional ℚ U₀ :=
    FiniteDimensional.of_injective (U₀.subtype.restrictScalars ℚ) U₀.injective_subtype
  letI : FiniteDimensional ℚ V₂ :=
    FiniteDimensional.of_injective (V₂.subtype.restrictScalars ℚ) V₂.injective_subtype
  letI : AddCommGroup V₂ := Submodule.addCommGroup V₂
  let h₂ := (h₁.domRestrict₁₂ U₀ U₀).domRestrict₁₂ V₂ V₂
  have hh₂ : h₂.IsSymm := (hh₁.domRestrict U₀).domRestrict V₂
  have hrank₂ : Module.finrank K V₂ = 2 := by
    have heq : 4 = Module.finrank K V₂ + 2 := by
      simpa [K, hrank₁] using hrank₂'
    omega
  have hsig₂ : hermSignature (a := (-3 : ℚ)) (b := 0) h₂ = (1, 1) := by
    have heq : (2, 2) =
        ((hermSignature (a := (-3 : ℚ)) (b := 0) h₂).1 + 1,
          (hermSignature (a := (-3 : ℚ)) (b := 0) h₂).2 + 1) := by
      simpa [h₂, hsig₁] using hsig₂'
    have hp := congrArg Prod.fst heq
    have hm := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  obtain ⟨hp₂, hm₂⟩ := hermSignature_trace_signs V₂ h₂ hh₂ hn₂
    (hsig₂ ▸ by norm_num) (hsig₂ ▸ by norm_num)
  obtain ⟨c, hc, e₃, he₃⟩ :=
    hermClass_binary_coordinates V₂ h₂ hh₂ hn₂ hrank₂ hp₂ hm₂
  obtain ⟨e₆, he₆⟩ := hermClass_assemble_six_coordinates W V₁ V₂ h h₁ h₂ c
    e₁ e₂ e₃ he₁ he₂ he₃
  let d : Fin 6 → ℚ := ![1, -1, 1, -1, 1, c]
  let D := diagForm (a := (-3 : ℚ)) (b := 0) d
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    fin_cases i <;> simp [d, hc]
  have heD : ∀ x y, D (e₆ x) (e₆ y) = h x y := by
    simpa [D, d] using he₆
  have hchange := detClass_eq_of_equiv W (Fin 6 → K) h D hh hn
    (diagForm_isSymm d) (diagForm_nondegenerate hd) e₆ heD
  have hcclass :
      ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup K) =
        ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) : ℚˣ ⧸ normSubgroup K) := by
    calc
      ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup K) =
          detClass D (diagForm_isSymm d) (diagForm_nondegenerate hd) := by
        rw [detClass_diagForm hd]
        congr 1
        apply Units.ext
        simp [d, Fin.prod_univ_succ]
      _ = detClass h hh hn := hchange.symm
      _ = _ := hdet
  let uc : ℚˣ := Units.mk0 c hc
  let un : ℚˣ := Units.mk0 (-2 : ℚ) (by norm_num)
  have hmem : uc / un ∈ normSubgroup K := QuotientGroup.eq_iff_div_mem.mp hcclass
  obtain ⟨z, hz⟩ := mem_normSubgroup_iff.mp hmem
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, QuadraticAlgebra.norm_zero] at hz
    exact (Units.ne_zero (uc / un)) hz.symm
  let ep : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
    { toFun := fun f ↦ ![f 0, f 2, f 4, f 1, f 3, z * f 5]
      invFun := fun f ↦ ![f 0, f 3, f 1, f 4, f 2, z⁻¹ * f 5]
      left_inv := fun f ↦ by
        funext i
        fin_cases i <;> simp [hz0]
      right_inv := fun f ↦ by
        funext i
        fin_cases i <;> simp [hz0]
      map_add' := fun f g ↦ by
        funext i
        fin_cases i <;> simp [mul_add]
      map_smul' := fun r f ↦ by
        funext i
        fin_cases i <;> simp
        ring }
  let e := e₆.trans ep
  refine ⟨e, fun x y ↦ ?_⟩
  rw [← heD x y]
  have hrat : c = -2 * QuadraticAlgebra.norm z := by
    rw [hz]
    change c = -2 * (c / -2)
    ring
  have hnorm : algebraMap ℚ K c = -2 * algebraMap ℚ K (QuadraticAlgebra.norm z) := by
    calc
      algebraMap ℚ K c = algebraMap ℚ K (-2 * QuadraticAlgebra.norm z) :=
        congrArg (algebraMap ℚ K) hrat
      _ = _ := by simp only [map_neg, map_mul, map_ofNat]
  simp [e, ep, D, d, diagForm_apply, Fin.sum_univ_succ]
  rw [show (c : K) = -2 * algebraMap ℚ K (QuadraticAlgebra.norm z) from hnorm,
    QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  ring

#print axioms hermClass_rank_six_standard

end HodgeLean.Foundations.HermitianClass
