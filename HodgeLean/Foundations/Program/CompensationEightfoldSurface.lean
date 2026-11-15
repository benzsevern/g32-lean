import HodgeLean.Foundations.Program.CompensationEightfoldLinear

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations ComplexConjugate

namespace HodgeLean.Foundations.Program

variable (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
  [IsProjective E.hom]

theorem cq8_surface_split (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) (s : ℂ) :
    let FA := (homPullback (fst E E) 1).baseChange ℂ
    let FY := (homPullback (snd E E) 1).baseChange ℂ
    let T := (cp_weilOperator E ρ).baseChange ℂ
    let P := (Module.End.eigenspace T s).map FA
    let Q := (Module.End.eigenspace T (-s)).map FY
    Module.End.eigenspace W.Jc s = P ⊔ Q ∧
      (∀ u ∈ P, (homPullback (cq8_surfaceEnd E ρ) 1).baseChange ℂ u =
        ((1 + s) / 2) • u) ∧
      (∀ v ∈ Q, (homPullback (cq8_surfaceEnd E ρ) 1).baseChange ℂ v = v) := by
  let iA : E ⟶ E ⊗ E := lift (𝟙 E) 1
  let iY : E ⟶ E ⊗ E := lift 1 (𝟙 E)
  have : IsMonHom iA := by dsimp [iA]; simp only [Hom.one_def]; infer_instance
  have : IsMonHom iY := by dsimp [iY]; simp only [Hom.one_def]; infer_instance
  let FA := (homPullback (fst E E) 1).baseChange ℂ
  let FY := (homPullback (snd E E) 1).baseChange ℂ
  let GA := (homPullback iA 1).baseChange ℂ
  let GY := (homPullback iY 1).baseChange ℂ
  let T := (cp_weilOperator E ρ).baseChange ℂ
  let F := (homPullback (cq8_surfaceEnd E ρ) 1).baseChange ℂ
  have hAA (x) : GA (FA x) = x := by
    simp only [GA, FA, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iA, lift_fst, spec_homPullback_id,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hAY (x) : GA (FY x) = 0 := by
    simp only [GA, FY, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iA, lift_snd, spec_homPullback_one,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hYA (x) : GY (FA x) = 0 := by
    simp only [GY, FA, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iY, lift_fst, spec_homPullback_one,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hYY (x) : GY (FY x) = x := by
    simp only [GY, FY, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iY, lift_snd, spec_homPullback_id,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hcat : fst E E ≫ iA * (snd E E ≫ iY) = 𝟙 (E ⊗ E) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.mul_comp, iA, iY, MonObj.comp_one]
  have hsplit (z) : FA (GA z) + FY (GY z) = z := by
    have hh : homPullback (fst E E) 1 ∘ₗ homPullback iA 1 +
        homPullback (snd E E) 1 ∘ₗ homPullback iY 1 = LinearMap.id := by
      rw [← spec_homPullback_comp, ← spec_homPullback_comp,
        ← spec_homPullback_mul, hcat, spec_homPullback_id]
    have hc := congrArg (fun f : Module.End ℚ (HQ (E ⊗ E) 1) => f.baseChange ℂ) hh
    exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_add,
      LinearMap.baseChange_comp, LinearMap.baseChange_id] using hc) z
  have hAc (x) : W.Jc (FA x) = FA (T x) := by
    have hh : W.J ∘ₗ homPullback (fst E E) 1 =
        homPullback (fst E E) 1 ∘ₗ cp_weilOperator E ρ := by
      ext x
      rw [hJ]
      exact (cp_conjAut_weil_restrictions E ρ hρ).1 x
    have hc := congrArg (fun f : HQ E 1 →ₗ[ℚ] HQ (E ⊗ E) 1 => f.baseChange ℂ) hh
    exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_comp] using hc) x
  have hYc (x) : W.Jc (FY x) = FY (-(T x)) := by
    have hh : W.J ∘ₗ homPullback (snd E E) 1 =
        homPullback (snd E E) 1 ∘ₗ (-cp_weilOperator E ρ) := by
      ext x
      rw [hJ]
      exact (cp_conjAut_weil_restrictions E ρ hρ).2 x
    have hc := congrArg (fun f : HQ E 1 →ₗ[ℚ] HQ (E ⊗ E) 1 => f.baseChange ℂ) hh
    exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_comp,
      LinearMap.baseChange_neg] using hc) x
  have hGA (z) : GA (W.Jc z) = T (GA z) := by
    calc
      _ = GA (W.Jc (FA (GA z) + FY (GY z))) := by rw [hsplit]
      _ = _ := by simp only [map_add, hAc, hYc, hAA, hAY, add_zero]
  have hGY (z) : GY (W.Jc z) = -(T (GY z)) := by
    calc
      _ = GY (W.Jc (FA (GA z) + FY (GY z))) := by rw [hsplit]
      _ = _ := by simp only [map_add, hAc, hYc, hYA, hYY, zero_add]
  constructor
  · apply le_antisymm
    · intro z hz
      have hz' := Module.End.mem_eigenspace_iff.mp hz
      rw [← hsplit z]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_left
        refine ⟨GA z, Module.End.mem_eigenspace_iff.mpr ?_, rfl⟩
        rw [← hGA, hz', map_smul]
      · apply Submodule.mem_sup_right
        refine ⟨GY z, Module.End.mem_eigenspace_iff.mpr ?_, rfl⟩
        have hh := congrArg GY hz'
        rw [hGY, map_smul] at hh
        simpa only [neg_smul, neg_neg] using congrArg Neg.neg hh
    · apply sup_le
      · rintro _ ⟨x, hx, rfl⟩
        apply Module.End.mem_eigenspace_iff.mpr
        rw [hAc, Module.End.mem_eigenspace_iff.mp hx, map_smul]
      · rintro _ ⟨x, hx, rfl⟩
        apply Module.End.mem_eigenspace_iff.mpr
        rw [hYc, Module.End.mem_eigenspace_iff.mp hx, neg_smul, neg_neg, map_smul]
  · constructor
    · rintro _ ⟨x, hx, rfl⟩
      have hfirst (x) : F (FA x) =
          FA x + FA ((homPullback ρ 1).baseChange ℂ x) := by
        have hh : homPullback (cq8_surfaceEnd E ρ) 1 ∘ₗ homPullback (fst E E) 1 =
            homPullback (fst E E) 1 +
              homPullback (fst E E) 1 ∘ₗ homPullback ρ 1 := by
          rw [← spec_homPullback_comp, ← spec_homPullback_comp,
            cq8_surfaceEnd, lift_fst, spec_homPullback_mul]
        have hc := congrArg (fun f : HQ E 1 →ₗ[ℚ] HQ (E ⊗ E) 1 => f.baseChange ℂ) hh
        exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_comp,
          LinearMap.baseChange_add] using hc) x
      have hT (x) : T x = x + (2 : ℂ) • (homPullback ρ 1).baseChange ℂ x := by
        simp only [T, cp_weilOperator, LinearMap.baseChange_add, LinearMap.baseChange_id,
          LinearMap.baseChange_smul, LinearMap.add_apply, LinearMap.id_apply,
          LinearMap.smul_apply]
        norm_cast
      have hx' := Module.End.mem_eigenspace_iff.mp hx
      rw [hT] at hx'
      change F (FA x) = _
      rw [hfirst, ← map_smul]
      have hh : x + (homPullback ρ 1).baseChange ℂ x = ((1 + s) / 2) • x := by
        calc
          _ = (1 / 2 : ℂ) • (x + (2 : ℂ) • (homPullback ρ 1).baseChange ℂ x) +
              (1 / 2 : ℂ) • x := by module
          _ = _ := by rw [hx']; module
      rw [← map_add, hh]
    · rintro _ ⟨x, hx, rfl⟩
      have hh : homPullback (cq8_surfaceEnd E ρ) 1 ∘ₗ homPullback (snd E E) 1 =
          homPullback (snd E E) 1 := by
        rw [← spec_homPullback_comp, cq8_surfaceEnd, lift_snd]
      have hc := congrArg (fun f : HQ E 1 →ₗ[ℚ] HQ (E ⊗ E) 1 => f.baseChange ℂ) hh
      exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_comp] using hc) x

theorem cq8_curve_ranks (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    letI := (finiteBetti_abelian E).finite 1
    let WE := cp_weilAction E ρ (cp_weilOperator_sq E ρ hρ)
    Module.finrank ℂ WE.Vs = 1 ∧ Module.finrank ℂ WE.Vsbar = 1 := by
  letI := (finiteBetti_abelian E).finite 1
  let WE := cp_weilAction E ρ (cp_weilOperator_sq E ρ hρ)
  have hdim : Module.finrank ℚ (HQ E 1) = 2 := by
    rw [(torusCohomology_cupProductOf E).finrank_eq, hE]
  have hs := Submodule.finrank_sup_add_finrank_inf_eq WE.Vs WE.Vsbar
  have hc := WE.isCompl_Vs_Vsbar (by norm_num : (0 : ℚ) < 3)
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero,
    Module.finrank_baseChange, hdim, WE.finrank_Vsbar_eq_Vs] at hs
  change Module.finrank ℂ WE.Vs = 1 ∧ Module.finrank ℂ WE.Vsbar = 1
  rw [WE.finrank_Vsbar_eq_Vs]
  omega

theorem cq8_surface_square (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) (s : ℂ)
    (hp : Module.finrank ℂ (Module.End.eigenspace ((cp_weilOperator E ρ).baseChange ℂ) s) ≤ 1)
    (hm : Module.finrank ℂ (Module.End.eigenspace ((cp_weilOperator E ρ).baseChange ℂ) (-s)) ≤ 1) :
    ∀ x ∈ LinearMap.range
      (exteriorPower.map 2 (Module.End.eigenspace W.Jc s).subtype),
      exteriorPower.map 2 ((homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ) x =
        (((1 + s) / 2) ^ 2) • x := by
  letI := (finiteBetti_abelian E).finite 1
  letI := (finiteBetti_abelian (E ⊗ E)).finite 1
  let FA := (homPullback (fst E E) 1).baseChange ℂ
  let FY := (homPullback (snd E E) 1).baseChange ℂ
  let T := (cp_weilOperator E ρ).baseChange ℂ
  let P := (Module.End.eigenspace T s).map FA
  let Q := (Module.End.eigenspace T (-s)).map FY
  let F := (homPullback (cq8_surfaceEnd E ρ) 1).baseChange ℂ
  have hp' : Module.finrank ℂ P ≤ 1 := (Submodule.finrank_map_le FA _).trans hp
  have hm' : Module.finrank ℂ Q ≤ 1 := (Submodule.finrank_map_le FY _).trans hm
  have hs := cq8_surface_split E ρ hρ W hJ s
  change Module.End.eigenspace W.Jc s = P ⊔ Q ∧
    (∀ u ∈ P, F u = ((1 + s) / 2) • u) ∧ (∀ v ∈ Q, F v = v) at hs
  have hf := cq8_exterior_two_sup P Q hp' hm' F ((1 + s) / 2) 1 hs.2.1
    (by simpa only [one_smul] using hs.2.2)
  simp only [mul_one] at hf
  have hc : (homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ = F.comp F := by
    rw [cq8_surfaceEnd2, spec_homPullback_comp, LinearMap.baseChange_comp]
  intro x hx
  have hrange := congrArg
    (fun R : Submodule ℂ (ℂ ⊗[ℚ] HQ (E ⊗ E) 1) =>
      LinearMap.range (exteriorPower.map 2 R.subtype)) hs.1
  have hfx := hf x (hrange ▸ hx)
  rw [hc, exteriorPower.map_comp, LinearMap.comp_apply, hfx, map_smul, hfx,
    smul_smul, ← pow_two]


theorem cq8_surface_preserves_eigenspace (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) (s : ℂ) :
    ∀ x ∈ Module.End.eigenspace W.Jc s,
      (homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ x ∈
        Module.End.eigenspace W.Jc s := by
  let F := (homPullback (cq8_surfaceEnd E ρ) 1).baseChange ℂ
  have hs := cq8_surface_split E ρ hρ W hJ s
  have hf : ∀ x ∈ Module.End.eigenspace W.Jc s, F x ∈ Module.End.eigenspace W.Jc s := by
    intro x hx
    rw [hs.1] at hx ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hs.2.1 u hu, hs.2.2 v hv]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ hu))
      (Submodule.mem_sup_right hv)
  have hc : (homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ = F.comp F := by
    rw [cq8_surfaceEnd2, spec_homPullback_comp, LinearMap.baseChange_comp]
  intro x hx
  rw [hc, LinearMap.comp_apply]
  exact hf _ (hf x hx)

end HodgeLean.Foundations.Program
