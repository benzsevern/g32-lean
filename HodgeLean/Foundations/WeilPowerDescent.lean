import HodgeLean.Foundations.WeilPowerPullback
import HodgeLean.Foundations.RationalPolarization

/-! # Scalar extension of the rational power generators -/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
open InvariantsExterior

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The complex realization of a rational exterior subspace.
Source: scalar extension followed by the exterior base-change equivalence. -/
def exteriorSpanC {k : ℕ} (P : Submodule ℚ (⋀[ℚ]^k V)) :
    Submodule ℂ (⋀[ℂ]^k (ℂ ⊗[ℚ] V)) :=
  (P.baseChange ℂ).map (exteriorBaseChange k).toLinearMap

example {k : ℕ} (P : Submodule ℚ (⋀[ℚ]^k V)) :
    Submodule ℂ (⋀[ℂ]^k (ℂ ⊗[ℚ] V)) := exteriorSpanC P

theorem exteriorBaseChange_one (k : ℕ) (v : ⋀[ℚ]^k V) :
    exteriorBaseChange k (1 ⊗ₜ[ℚ] v) = exteriorComplexify k v := by
  change (exteriorBaseChange k).toLinearMap _ = _
  rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul]

theorem exteriorSpanC_eq_span {k : ℕ} (P : Submodule ℚ (⋀[ℚ]^k V)) :
    exteriorSpanC P = Submodule.span ℂ (exteriorComplexify k '' (P : Set _)) := by
  rw [exteriorSpanC, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (exteriorBaseChange_one k v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨1 ⊗ₜ[ℚ] v, ⟨v, hv, rfl⟩, exteriorBaseChange_one k v⟩

theorem exteriorComplexify_mem {k : ℕ} {P : Submodule ℚ (⋀[ℚ]^k V)}
    {v : ⋀[ℚ]^k V} (hv : v ∈ P) : exteriorComplexify k v ∈ exteriorSpanC P := by
  rw [exteriorSpanC_eq_span]
  exact Submodule.subset_span ⟨v, hv, rfl⟩

theorem exteriorSpanC_mono {k : ℕ} {P Q : Submodule ℚ (⋀[ℚ]^k V)} (h : P ≤ Q) :
    exteriorSpanC P ≤ exteriorSpanC Q := by
  simp only [exteriorSpanC_eq_span]
  apply Submodule.span_mono
  exact Set.image_mono h

omit [Module.Finite ℚ V] in
theorem exteriorComplexify_wedge (i j : ℕ) (v : ⋀[ℚ]^i V) (w : ⋀[ℚ]^j V) :
    exteriorComplexify (i + j) (exteriorPower.wedge ℚ V i j v w) =
      exteriorPower.wedge ℂ (ℂ ⊗[ℚ] V) i j
        (exteriorComplexify i v) (exteriorComplexify j w) := by
  have hh : (exteriorPower.wedge ℚ V i j).compr₂ (exteriorComplexify (i + j)) =
      ((LinearMap.restrictScalarsₗ (R := ℚ) (R₁ := ℚ) (S := ℂ)
        (M := ⋀[ℂ]^j (ℂ ⊗[ℚ] V)) (N := ⋀[ℂ]^(i + j) (ℂ ⊗[ℚ] V))).comp
        ((exteriorPower.wedge ℂ (ℂ ⊗[ℚ] V) i j).restrictScalars ℚ)).compl₁₂
          (exteriorComplexify i) (exteriorComplexify j) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro b
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalarsₗ_apply, wedge_ιMulti, exteriorComplexify_ιMulti]
    congr 1
    funext s
    refine Fin.addCases (fun s => ?_) (fun s => ?_) s <;> simp
  exact LinearMap.congr_fun₂ hh v w

/-- Scalar extension preserves wedge closure of rational exterior subspaces. -/
theorem exteriorSpanC_wedge {i j : ℕ}
    (P : Submodule ℚ (⋀[ℚ]^i V)) (Q : Submodule ℚ (⋀[ℚ]^j V))
    (R : Submodule ℚ (⋀[ℚ]^(i + j) V))
    (h : ∀ v ∈ P, ∀ w ∈ Q, exteriorPower.wedge ℚ V i j v w ∈ R)
    {v : ⋀[ℂ]^i (ℂ ⊗[ℚ] V)} {w : ⋀[ℂ]^j (ℂ ⊗[ℚ] V)}
    (hv : v ∈ exteriorSpanC P) (hw : w ∈ exteriorSpanC Q) :
    exteriorPower.wedge ℂ _ i j v w ∈ exteriorSpanC R := by
  rw [exteriorSpanC_eq_span] at hv hw
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, hv, rfl⟩ := hv
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨w, hw, rfl⟩ := hw
      rw [← exteriorComplexify_wedge]
      exact exteriorComplexify_mem (h v hv w hw)
    | zero => simp only [map_zero, Submodule.zero_mem]
    | add w z _ _ hw hz => simpa only [map_add] using (exteriorSpanC R).add_mem hw hz
    | smul c w _ hw => simpa only [map_smul] using (exteriorSpanC R).smul_mem c hw
  | zero => simp only [map_zero, LinearMap.zero_apply, Submodule.zero_mem]
  | add v z _ _ hv hz =>
    simpa only [map_add, LinearMap.add_apply] using (exteriorSpanC R).add_mem hv hz
  | smul c v _ hv =>
    simpa only [map_smul, LinearMap.smul_apply] using (exteriorSpanC R).smul_mem c hv

/-- Rational pullback membership extends to the complex span of the source. -/
theorem exteriorSpanC_map {V' : Type*} [AddCommGroup V'] [Module ℚ V']
    [Module.Finite ℚ V'] {k : ℕ} (f : V →ₗ[ℚ] V')
    (P : Submodule ℚ (⋀[ℚ]^k V)) (Q : Submodule ℚ (⋀[ℚ]^k V'))
    (hf : ∀ v ∈ P, exteriorPower.map k f v ∈ Q)
    {v : ⋀[ℂ]^k (ℂ ⊗[ℚ] V)} (hv : v ∈ exteriorSpanC P) :
    exteriorPower.map k (f.baseChange ℂ) v ∈ exteriorSpanC Q := by
  rw [exteriorSpanC_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, hv, rfl⟩ := hv
    have he := LinearMap.congr_fun (exteriorBaseChange_map k f) (1 ⊗ₜ[ℚ] v)
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      exteriorBaseChange_one] at he
    rw [← he]
    exact exteriorComplexify_mem (hf v hv)
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add v w _ _ hv hw => simpa only [map_add] using (exteriorSpanC Q).add_mem hv hw
  | smul c v _ hv => simpa only [map_smul] using (exteriorSpanC Q).smul_mem c hv

section Determinants
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] {m : ℕ}

theorem multiplicityEquiv_one (r : Fin m → ℚ) :
    multiplicityEquiv m (1 ⊗ₜ[ℚ] r) = (fun i => (r i : ℂ)) := by
  ext i
  simp [multiplicityEquiv, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]

/-- Descent of a rational-parameter vector determinant through the actual power model. -/
theorem detWOf_rat_mem_exteriorSpanC
    (J : Module.End ℚ V) (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (T : Submodule ℚ (⋀[ℚ]^(Module.finrank ℂ W) V))
    (P : Submodule ℚ (⋀[ℚ]^(Module.finrank ℂ W) (V ⊗[ℚ] (Fin m → ℚ))))
    (hp : ∀ r s w, w ∈ T → exteriorPower.map _ (weilPowerPullback J r s) w ∈ P)
    (t : ⋀[ℂ]^(Module.finrank ℂ W) W)
    (ht : exteriorPower.map _
      (e.symm.toLinearMap.comp (LinearMap.inl ℂ W (Module.Dual ℂ W))) t ∈ exteriorSpanC T)
    (r : Fin m → ℚ) :
    (exteriorEquiv _ (powerModel m e)).symm (detWOf t (fun i => (r i : ℂ))) ∈
      exteriorSpanC P := by
  have h := exteriorSpanC_map (weilPowerPullback J r 0) T P (hp r 0) ht
  have he := powerModel_pullback_exterior_vector J e hJe r 0 t
  simp only [TensorProduct.tmul_zero, map_zero, smul_zero, add_zero,
    multiplicityEquiv_one] at he
  rw [exteriorPower.map_comp, LinearMap.comp_apply] at he
  change exteriorEquiv _ (powerModel m e) _ = _ at he
  rw [← he, LinearEquiv.symm_apply_apply]
  exact h

/-- Descent of a rational-parameter dual determinant through the actual power model. -/
theorem detWDualOf_rat_mem_exteriorSpanC
    (J : Module.End ℚ V) (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (T : Submodule ℚ (⋀[ℚ]^(Module.finrank ℂ W) V))
    (P : Submodule ℚ (⋀[ℚ]^(Module.finrank ℂ W) (V ⊗[ℚ] (Fin m → ℚ))))
    (hp : ∀ r s w, w ∈ T → exteriorPower.map _ (weilPowerPullback J r s) w ∈ P)
    (t : ⋀[ℂ]^(Module.finrank ℂ W) (Module.Dual ℂ W))
    (ht : exteriorPower.map _
      (e.symm.toLinearMap.comp (LinearMap.inr ℂ W (Module.Dual ℂ W))) t ∈ exteriorSpanC T)
    (r : Fin m → ℚ) :
    (exteriorEquiv _ (powerModel m e)).symm (detWDualOf t (fun i => (r i : ℂ))) ∈
      exteriorSpanC P := by
  have h := exteriorSpanC_map (weilPowerPullback J r 0) T P (hp r 0) ht
  have he := powerModel_pullback_exterior_dual J e hJe r 0 t
  simp only [TensorProduct.tmul_zero, map_zero, smul_zero, sub_zero,
    multiplicityEquiv_one] at he
  rw [exteriorPower.map_comp, LinearMap.comp_apply] at he
  change exteriorEquiv _ (powerModel m e) _ = _ at he
  rw [← he, LinearEquiv.symm_apply_apply]
  exact h

/-- Complex vector determinant parameters are spanned by rational parameters. -/
theorem detW_mem_span_rat (a : Fin m → ℂ) :
    detW (K := ℂ) (W := W) (U' := Fin m → ℂ) a ∈ Submodule.span ℂ
      (Set.range (fun r : Fin m → ℚ =>
        detW (K := ℂ) (W := W) (U' := Fin m → ℂ) (fun i => (r i : ℂ)))) := by
  simpa only [multiplicityWedge_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply,
    LinearMap.inl_apply, ← detW_eq] using
    multilinear_diagonal_mem_span_rat
      (multiplicityWedge ((TensorProduct.mk ℂ W (Fin m → ℂ)).compr₂
        (LinearMap.inl ℂ (W ⊗[ℂ] (Fin m → ℂ))
          (Module.Dual ℂ W ⊗[ℂ] (Fin m → ℂ)))) (Module.finBasis ℂ W)) a

/-- Complex dual determinant parameters are spanned by rational parameters. -/
theorem detWDual_mem_span_rat (a : Fin m → ℂ) :
    detWDual (K := ℂ) (W := W) (U := Fin m → ℂ) a ∈ Submodule.span ℂ
      (Set.range (fun r : Fin m → ℚ =>
        detWDual (K := ℂ) (W := W) (U := Fin m → ℂ) (fun i => (r i : ℂ)))) := by
  simpa only [multiplicityWedge_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply,
    LinearMap.inr_apply, ← detWDual_eq] using
    multilinear_diagonal_mem_span_rat
      (multiplicityWedge ((TensorProduct.mk ℂ (Module.Dual ℂ W) (Fin m → ℂ)).compr₂
        (LinearMap.inr ℂ (W ⊗[ℂ] (Fin m → ℂ))
          (Module.Dual ℂ W ⊗[ℂ] (Fin m → ℂ)))) (Module.finBasis ℂ W).dualBasis) a

end Determinants

#print axioms exteriorBaseChange_one
#print axioms exteriorSpanC_eq_span
#print axioms exteriorComplexify_mem
#print axioms exteriorSpanC_mono
#print axioms exteriorComplexify_wedge
#print axioms exteriorSpanC_wedge
#print axioms exteriorSpanC_map
#print axioms multiplicityEquiv_one
#print axioms detWOf_rat_mem_exteriorSpanC
#print axioms detWDualOf_rat_mem_exteriorSpanC
#print axioms detW_mem_span_rat
#print axioms detWDual_mem_span_rat

end HodgeLean.Foundations.WeilPower
