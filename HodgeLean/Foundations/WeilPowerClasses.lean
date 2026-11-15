import HodgeLean.Foundations.WeilPowerDecomposition

/-! # Hodge classes of Weil powers

F-1575's step from (1) to the Hodge classes of `Aᵐ`, at the level of `⋀ H¹`.
The conclusion is conditional on `hSU`, the explicit Hodge-group input.
We construct the exterior Hodge pieces by total bidegree and identify their
diagonal sum with the induced grading kernel. The classes below are the complex
span of rational vectors in that diagonal sum, not the whole complex kernel. C7, the identification with `H^*(Aᵐ)`, is not proved here.
Algebraicity requires F-1569, Lefschetz (1,1), and closure under pullback and
products. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 800000
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
open InvariantsExterior

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The rational exterior-power representation, with trivial multiplicities.
Source: constructed here from the tensor action and exterior derivations. -/
def rationalPowerLie (m k : ℕ) : Module.End ℚ V →ₗ⁅ℚ⁆
    Module.End ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :=
  (exteriorLie k).comp
    { toFun := fun f => f.rTensor (Fin m → ℚ)
      map_add' := fun f g => by simp only [LinearMap.rTensor_add]
      map_smul' := fun c f => by simp only [LinearMap.rTensor_smul, RingHom.id_apply]
      map_lie' := by
        intro f g
        simp only [Ring.lie_def, LinearMap.rTensor_sub, LinearMap.rTensor_mul] }

instance (m k : ℕ) : LieRingModule (Module.End ℚ V)
    (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :=
  LieRingModule.compLieHom _ (rationalPowerLie m k)

instance (m k : ℕ) : LieModule ℚ (Module.End ℚ V)
    (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :=
  LieModule.compLieHom _ (rationalPowerLie m k)

example (m k : ℕ) (f : Module.End ℚ V) :
    rationalPowerLie m k f = exteriorDer k (f.rTensor (Fin m → ℚ)) := rfl

variable [FiniteDimensional ℚ V]

theorem exteriorBaseChange_complexAction (m k : ℕ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    (exteriorBaseChange (V := V ⊗[ℚ] (Fin m → ℚ)) k).conj
      (complexAction (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) X) =
      exteriorDer k (powerAction m X) := by
  let e := exteriorBaseChange (V := V ⊗[ℚ] (Fin m → ℚ)) k
  let a : Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ]
      Module.End ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))) :=
    { toFun := powerAction m
      map_add' := powerAction_add m
      map_smul' := powerAction_smul m }
  have hh : e.conj.toLinearMap.comp (complexAction (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ)))) =
      (exteriorLie (K := ℂ) (M := ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))) k).toLinearMap.comp a := by
    apply LinearMap.ext_on (complexSpan_top (V := V))
    rintro _ ⟨f, _, rfl⟩
    change e.conj (complexAction _ (f.baseChange ℂ)) = exteriorDer k (powerAction m (f.baseChange ℂ))
    rw [complexAction_baseChange, powerAction_baseChange]
    change e.conj ((exteriorDer k (f.rTensor (Fin m → ℚ))).baseChange ℂ) = _
    apply LinearMap.ext
    intro v
    have h := congrArg (fun g => g (e.symm v)) (exteriorBaseChange_der k (f.rTensor (Fin m → ℚ)))
    change e ((exteriorDer k (f.rTensor (Fin m → ℚ))).baseChange ℂ (e.symm v)) =
      exteriorDer k ((f.rTensor (Fin m → ℚ)).baseChange ℂ) (e (e.symm v)) at h
    rw [e.apply_symm_apply] at h
    exact h
  exact LinearMap.congr_fun hh X

variable (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- Rational exterior Hodge classes, defined by the induced Hodge grading.
Source: van Geemen, An introduction to the Hodge conjecture for abelian varieties, §5–6;
constructed here as the rational kernel of the induced grading operator. -/
def rationalExteriorHodge (m k : ℕ) : Submodule ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :=
  LinearMap.ker (((exteriorDer k (powerAction m (gradingOperator H hH))).restrictScalars ℚ).comp
    (exteriorComplexify k))

example (m k : ℕ) (v : ⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :
    v ∈ rationalExteriorHodge H hH m k ↔
      exteriorDer k (powerAction m (gradingOperator H hH)) (exteriorComplexify k v) = 0 := Iff.rfl

theorem mem_maxTrivSubmodule_hodgeLieAlgebra_exterior_iff_grading (m k : ℕ)
    (v : ⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :
    v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) _ ↔
      v ∈ rationalExteriorHodge H hH m k := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff]
  change complexAction _ (gradingOperator H hH) (1 ⊗ₜ[ℚ] v) = 0 ↔
    exteriorDer k (powerAction m (gradingOperator H hH)) (exteriorComplexify k v) = 0
  let e := exteriorBaseChange (V := V ⊗[ℚ] (Fin m → ℚ)) k
  have he : e (1 ⊗ₜ[ℚ] v) = exteriorComplexify k v := by
    change (exteriorBaseChange k).toLinearMap _ = _
    rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul]
  have ha := LinearMap.congr_fun (exteriorBaseChange_complexAction (V := V) m k
    (gradingOperator H hH)) (e (1 ⊗ₜ[ℚ] v))
  change e (complexAction _ (gradingOperator H hH) (e.symm (e (1 ⊗ₜ[ℚ] v)))) = _ at ha
  rw [e.symm_apply_apply] at ha
  rw [← he, ← ha]
  exact (e.map_eq_zero_iff).symm

omit [FiniteDimensional ℚ V] in
/-- Rational exterior Hodge classes are precisely the rational vectors whose
complexifications lie in the sum of the actual exterior `(p,p)` pieces. -/
theorem mem_rationalExteriorHodge_iff (m k : ℕ)
    (v : ⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :
    v ∈ rationalExteriorHodge H hH m k ↔
      exteriorComplexify k v ∈ ⨆ p : ℤ, exteriorHodge H m k (p, p) := by
  change exteriorComplexify k v ∈ LinearMap.ker
    (exteriorDer k (powerAction m (gradingOperator H hH))) ↔ _
  rw [ker_exterior_hodge_grading H hH]

/-- Exterior-power analogue of the tensor Hodge-invariant characterization. -/
theorem mem_maxTrivSubmodule_hodgeLieAlgebra_exterior_iff (m k : ℕ)
    (v : ⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :
    v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) _ ↔
      exteriorComplexify k v ∈ ⨆ p : ℤ, exteriorHodge H m k (p, p) := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_exterior_iff_grading,
    mem_rationalExteriorHodge_iff]

/-- Complex span of rational exterior Hodge classes.
Source: constructed here by scalar extension of the rational grading kernel. -/
def exteriorHodgeClasses (m k : ℕ) :
    Submodule ℂ (⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ)))) :=
  ((rationalExteriorHodge H hH m k).baseChange ℂ).map (exteriorBaseChange k).toLinearMap

example (m k : ℕ) (v : ℂ ⊗[ℚ] (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))))
    (hv : v ∈ (rationalExteriorHodge H hH m k).baseChange ℂ) :
    exteriorBaseChange k v ∈ exteriorHodgeClasses H hH m k := ⟨v, hv, rfl⟩


theorem mem_exteriorHodgeClasses_iff (m k : ℕ)
    (v : ⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ)))) :
    v ∈ exteriorHodgeClasses H hH m k ↔
      ∀ X ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule,
        exteriorDer k (powerAction m X) v = 0 := by
  have hr : rationalExteriorHodge H hH m k =
      (LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
        (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) : Submodule ℚ _) := by
    ext w
    exact (mem_maxTrivSubmodule_hodgeLieAlgebra_exterior_iff_grading H hH m k w).symm
  let e := exteriorBaseChange (V := V ⊗[ℚ] (Fin m → ℚ)) k
  have ha (X : Module.End ℂ (ℂ ⊗[ℚ] V)) (w : ℂ ⊗[ℚ] (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ)))) :
      e (complexAction _ X w) = exteriorDer k (powerAction m X) (e w) := by
    have h := LinearMap.congr_fun (exteriorBaseChange_complexAction (V := V) m k X) (e w)
    change e (complexAction _ X (e.symm (e w))) = _ at h
    simpa only [e.symm_apply_apply] using h
  change v ∈ ((rationalExteriorHodge H hH m k).baseChange ℂ).map e.toLinearMap ↔ _
  rw [hr]
  constructor
  · rintro ⟨w, hw, rfl⟩ X hX
    have hw' := (mem_baseChange_invariants_iff (hodgeLieAlgebra H hH) w).mp hw X hX
    change exteriorDer k (powerAction m X) (e w) = 0
    rw [← ha, hw', map_zero]
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply (mem_baseChange_invariants_iff (hodgeLieAlgebra H hH) (e.symm v)).mpr
    intro X hX
    apply e.injective
    rw [ha, e.apply_symm_apply, hv X hX, map_zero]

variable (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
  (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
  (hskew : ∀ x y, E (J x) y = -E x (J y))

/-- F-1575's step from (1) to the Hodge classes of a power, at the level of `⋀ H¹`.
The explicit equality `hSU` is the Hodge-group input. C7 and algebraicity are not asserted.
Source: van Geemen, An introduction to the Hodge conjecture for abelian varieties, §5–6;
constructed here by equivariant transport and the rational Hodge Lie algebra criterion. -/
theorem exteriorHodgeClasses_eq_generated (m k : ℕ)
    (hSU : complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU E hE J hJ hskew).toSubmodule) :
    exteriorHodgeClasses H hH m k =
      (generatedDegree (K := ℂ) (W := Module.End.eigenspace (J.baseChange ℂ) root)
        (U := Fin m → ℂ) (U' := Fin m → ℂ) k).map
        (exteriorEquiv k (powerModel m (polarizedSplitting E hE J hJ hskew))).symm.toLinearMap := by
  ext v
  rw [mem_exteriorHodgeClasses_iff, hSU]
  let e := exteriorEquiv k (powerModel m (polarizedSplitting E hE J hJ hskew))
  constructor
  · intro hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    exact (power_invariants_iff E hE J hJ hskew m k v).mp (fun X => hv X.1 X.2)
  · rintro ⟨w, hw, he⟩ X hX
    have hv : e v ∈ generatedDegree (K := ℂ)
        (W := Module.End.eigenspace (J.baseChange ℂ) root)
        (U := Fin m → ℂ) (U' := Fin m → ℂ) k := by
      change e.symm w = v at he
      rw [← he, e.apply_symm_apply]
      exact hw
    exact (power_invariants_iff E hE J hJ hskew m k v).mpr hv ⟨X, hX⟩

end HodgeLean.Foundations.WeilPower
