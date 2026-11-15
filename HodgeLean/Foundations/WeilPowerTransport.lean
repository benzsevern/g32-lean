import HodgeLean.Foundations.WeilPowerLie

/-! # Equivariant Weil-power models and transported invariant spans

F-1575's step from (1) towards the Hodge classes of `Aᵐ`, at the level of `⋀ H¹`.
The model and Lie-invariant theorem here are unconditional representation theory.
A Hodge-class conclusion requires the explicit Hodge-group input `hSU`.
C7's cohomology comparison and algebraicity (F-1569, Lefschetz (1,1), pullbacks,
and products) are separate. HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
open InvariantsExterior SchurWeyl

variable {M N : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]

/-- Exterior powers of a linear equivalence.
Source: constructed here using functoriality of the exterior power. -/
def exteriorEquiv (k : ℕ) (e : M ≃ₗ[ℂ] N) : (⋀[ℂ]^k M) ≃ₗ[ℂ] (⋀[ℂ]^k N) :=
  LinearEquiv.ofBijective (exteriorPower.map k e.toLinearMap)
    ⟨exteriorPower.map_injective_field e.injective,
      exteriorPower.map_surjective e.surjective⟩

example (k : ℕ) (e : M ≃ₗ[ℂ] N) (v : Fin k → M) :
    exteriorEquiv k e (exteriorPower.ιMulti ℂ k v) =
      exteriorPower.ιMulti ℂ k (e ∘ v) := by
  exact exteriorPower.map_apply_ιMulti _ _

theorem exteriorEquiv_intertwines (k : ℕ) (e : M ≃ₗ[ℂ] N)
    (X : Module.End ℂ M) (Y : Module.End ℂ N)
    (h : ∀ x, e (X x) = Y (e x)) (v : ⋀[ℂ]^k M) :
    exteriorEquiv k e (exteriorDer k X v) =
      exteriorDer k Y (exteriorEquiv k e v) := by
  symm
  exact exteriorDer_map k X Y e.toLinearMap (LinearMap.ext fun x => (h x).symm) v

variable {W U U' : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  [AddCommGroup U'] [Module ℂ U'] [FiniteDimensional ℂ U']

/-- Exact transport of F-1575 (1) along an equivariant model.
This statement concerns Lie invariants, not yet Hodge classes.
Source: constructed here from `invariants_eq_generatedDegree`. -/
theorem transported_invariants_iff (e : M ≃ₗ[ℂ] Space ℂ W U U')
    (ρ : slEnd ℂ W → Module.End ℂ M)
    (hρ : ∀ f x, e (ρ f x) = multiplicityLie ℂ W U U' f (e x))
    (k : ℕ) (v : ⋀[ℂ]^k M) :
    (∀ f, exteriorDer k (ρ f) v = 0) ↔
      exteriorEquiv k e v ∈ generatedDegree (K := ℂ) (W := W) (U := U) (U' := U') k := by
  rw [← invariants_eq_generatedDegree]
  change (∀ f, exteriorDer k (ρ f) v = 0) ↔
    ∀ f : slEnd ℂ W, exteriorDer k (multiplicityLie ℂ W U U' f) (exteriorEquiv k e v) = 0
  constructor
  · intro hv f
    rw [← exteriorEquiv_intertwines k e (ρ f) _ (hρ f), hv]
    change exteriorPower.map k e.toLinearMap 0 = 0
    exact map_zero _
  · intro hv f
    apply (exteriorEquiv k e).injective
    rw [exteriorEquiv_intertwines k e (ρ f) _ (hρ f), hv]
    change 0 = exteriorPower.map k e.toLinearMap 0
    exact (map_zero _).symm

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Scalar extension of the standard rational multiplicity space.
Source: constructed here from its standard basis. -/
def multiplicityEquiv (m : ℕ) : (ℂ ⊗[ℚ] (Fin m → ℚ)) ≃ₗ[ℂ] (Fin m → ℂ) :=
  ((Pi.basisFun ℚ (Fin m)).baseChange ℂ).equivFun

example (m : ℕ) : Function.Bijective (multiplicityEquiv m) := (multiplicityEquiv m).bijective

/-- Base change of the power `V ⊗ ℚᵐ`.
Source: constructed here using scalar extension of tensor products. -/
def powerBaseChange (m : ℕ) :
    (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))) ≃ₗ[ℂ] ((ℂ ⊗[ℚ] V) ⊗[ℂ] (Fin m → ℂ)) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange ℚ ℂ V (Fin m → ℚ)).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ _) (multiplicityEquiv m))

example (m : ℕ) : Function.Bijective (powerBaseChange (V := V) m) :=
  (powerBaseChange (V := V) m).bijective

/-- The linear model of a power, given the polarized splitting of its first cohomology.
Source: constructed here for F-1575's transport at the level of `H¹`. -/
def powerModel (m : ℕ) (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W)) :
    (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))) ≃ₗ[ℂ]
      Space ℂ W (Fin m → ℂ) (Fin m → ℂ) :=
  (powerBaseChange m).trans ((TensorProduct.congr e (LinearEquiv.refl ℂ _)).trans
    (TensorProduct.prodLeft ℂ ℂ W (Module.Dual ℂ W) (Fin m → ℂ)))

example (m : ℕ) (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W)) :
    Function.Bijective (powerModel m e) := (powerModel m e).bijective

/-- The complexified action on a power, trivial on the multiplicity space.
Source: constructed here by the natural tensor-product base-change equivalence. -/
def powerAction (m : ℕ) (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    Module.End ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))) :=
  (powerBaseChange m).symm.conj (X.rTensor (Fin m → ℂ))

example (m : ℕ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (x : ℂ ⊗[ℚ] V) (u : Fin m → ℂ) :
    powerAction m X ((powerBaseChange m).symm (x ⊗ₜ[ℂ] u)) =
      (powerBaseChange m).symm (X x ⊗ₜ[ℂ] u) := by simp [powerAction]

/-- The power action is the actual scalar extension of the rational tensor action. -/
theorem powerAction_baseChange (m : ℕ) (f : Module.End ℚ V) :
    powerAction m (f.baseChange ℂ) = (f.rTensor (Fin m → ℚ)).baseChange ℂ := by
  apply LinearMap.ext
  intro z
  apply (powerBaseChange m).injective
  simp only [powerAction, LinearEquiv.conj_apply]
  induction z using TensorProduct.inductionOn with
  | tmul a p =>
    induction p using TensorProduct.inductionOn with
    | tmul v u => simp [powerBaseChange]
    | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem powerAction_add (m : ℕ) (X Y : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    powerAction m (X + Y) = powerAction m X + powerAction m Y := by
  simp only [powerAction, LinearMap.rTensor_add, map_add]

theorem powerAction_smul (m : ℕ) (c : ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    powerAction m (c • X) = c • powerAction m X := by
  simp only [powerAction, LinearMap.rTensor_smul, map_smul]

omit [FiniteDimensional ℂ W] in
theorem powerModel_intertwines (m : ℕ)
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) (f : Module.End ℂ W)
    (h : ∀ x, e (X x) = blockLie W f (e x))
    (z : ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))) :
    powerModel m e (powerAction m X z) =
      multiplicityLie ℂ W (Fin m → ℂ) (Fin m → ℂ) f (powerModel m e z) := by
  obtain ⟨z, rfl⟩ := (powerBaseChange (V := V) m).symm.surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    have hp (z : W × Module.Dual ℂ W) :
        TensorProduct.prodLeft ℂ ℂ W (Module.Dual ℂ W) (Fin m → ℂ) (z ⊗ₜ[ℂ] u) =
          (z.1 ⊗ₜ[ℂ] u, z.2 ⊗ₜ[ℂ] u) := by cases z; rfl
    simp [powerAction, powerModel, h, hp, blockLie, multiplicityLie, TensorProduct.neg_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [FiniteDimensional ℚ V]
variable (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
  (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
  (hskew : ∀ x y, E (J x) y = -E x (J y))

/-- The exact invariant span on the complex exterior power of a rational power.
No Hodge-group equality is assumed in this purely representation-theoretic statement.
Source: constructed here by transport of F-1575 (1). -/
theorem power_invariants_iff (m k : ℕ)
    (v : ⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ)))) :
    (∀ X : complexSU E hE J hJ hskew, exteriorDer k (powerAction m X.1) v = 0) ↔
      exteriorEquiv k (powerModel m (polarizedSplitting E hE J hJ hskew)) v ∈
        generatedDegree (K := ℂ) (W := Module.End.eigenspace (J.baseChange ℂ) root)
          (U := Fin m → ℂ) (U' := Fin m → ℂ) k := by
  let e := powerModel m (polarizedSplitting E hE J hJ hskew)
  let ρ := fun f : slEnd ℂ (Module.End.eigenspace (J.baseChange ℂ) root) =>
    powerAction m ((complexSUEquiv E hE J hJ hskew).symm f).1
  have hρ : ∀ f x, e (ρ f x) = multiplicityLie ℂ _ (Fin m → ℂ) (Fin m → ℂ) f (e x) := by
    intro f x
    apply powerModel_intertwines m _ _ _ _ x
    intro z
    have h := complexSU_action E hE J hJ hskew
      ((complexSUEquiv E hE J hJ hskew).symm f) z
    simpa only [LieEquiv.apply_symm_apply, LieEquiv.coe_coe] using h
  rw [← transported_invariants_iff e ρ hρ k v]
  constructor
  · intro hv f
    exact hv _
  · intro hv X
    obtain ⟨f, rfl⟩ := (complexSUEquiv E hE J hJ hskew).symm.surjective X
    exact hv f

end HodgeLean.Foundations.WeilPower
