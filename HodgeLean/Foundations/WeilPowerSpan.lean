import HodgeLean.Foundations.WeilPowerClasses

/-! # Rational generators on powers

The coefficients of a map to the original Weil space are pairs of rational
multiplicity vectors: `r + s √(-3)`. The input `W` below is the rational Weil
space of the original variety, in its original degree `n`, independent of `m`.
This file defines the span; it does not assert generation under `hSU`.
-/

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Foundations.WeilPower

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Pullback on degree one with coefficients `r + s √(-3)`, where `J` represents
`√(-3)`. This formula also makes sense without imposing the quadratic relation.
Source: F-1575 / TR54 §3, the maps from a power to its original Weil space. -/
def weilPowerPullback (J : Module.End ℚ V) {m : ℕ} (r s : Fin m → ℚ) :
    V →ₗ[ℚ] V ⊗[ℚ] (Fin m → ℚ) :=
  (TensorProduct.mk ℚ V (Fin m → ℚ)).flip r +
    ((TensorProduct.mk ℚ V (Fin m → ℚ)).flip s).comp J

example (J : Module.End ℚ V) {m : ℕ} (r s : Fin m → ℚ) (x : V) :
    weilPowerPullback J r s x = x ⊗ₜ[ℚ] r + J x ⊗ₜ[ℚ] s := rfl

/-- The degree-one pullback commutes with the quadratic action. -/
theorem weilPowerPullback_commutes (J : Module.End ℚ V) {m : ℕ}
    (r s : Fin m → ℚ) (x : V) :
    weilPowerPullback J r s (J x) =
      J.rTensor (Fin m → ℚ) (weilPowerPullback J r s x) := by
  simp [weilPowerPullback]

/-- A graded family containing the unit, divisors `D`, and all rational
pullbacks of the original Weil space `W`, closed under wedge product.
Source: F-1575 / TR54 §3; van Geemen, *An introduction to the Hodge conjecture
for abelian varieties*, §§5–6.

Consistency and non-vacuity: the family constantly equal to the full space
satisfies these closure conditions for every input. This is an untagged
closure predicate, not a generation or algebraicity hypothesis. -/
structure IsDivisorPulledWeilClosed (J : Module.End ℚ V) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ))))
    (W : Submodule ℚ (⋀[ℚ]^n V))
    (F : ∀ k, Submodule ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ)))) : Prop where
  unit_mem : exteriorPower.ιMulti ℚ 0 Fin.elim0 ∈ F 0
  divisor_le : D ≤ F 2
  pullback_mem : ∀ r s w, w ∈ W → exteriorPower.map n (weilPowerPullback J r s) w ∈ F n
  wedge_mem : ∀ i j v w, v ∈ F i → w ∈ F j → exteriorPower.wedge ℚ _ i j v w ∈ F (i + j)

example (J : Module.End ℚ V) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ))))
    (W : Submodule ℚ (⋀[ℚ]^n V)) :
    IsDivisorPulledWeilClosed J D W (fun _ => ⊤) := by
  constructor
  · trivial
  · exact le_top
  · intros; trivial
  · intros; trivial

/-- The rational span of products of divisors and pulled-back original Weil
classes, in cohomological degree `k`. For the Hodge application take
`D = rationalExteriorHodge H hH m 2` and the original rational Weil space `W`.
The Weil generators retain degree `n`, not `m * n`.
Source: F-1575 / TR54 §3; van Geemen, *An introduction to the Hodge conjecture
for abelian varieties*, §§5–6. -/
def divisorPulledWeilSpan (J : Module.End ℚ V) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ))))
    (W : Submodule ℚ (⋀[ℚ]^n V)) (k : ℕ) :
    Submodule ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ))) :=
  ⨅ (F : ∀ i, Submodule ℚ (⋀[ℚ]^i (V ⊗[ℚ] (Fin m → ℚ))))
    (_ : IsDivisorPulledWeilClosed J D W F), F k

variable (J : Module.End ℚ V) {m n : ℕ}
  (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ))))
  (W : Submodule ℚ (⋀[ℚ]^n V))

theorem divisorPulledWeilSpan_le
    {F : ∀ i, Submodule ℚ (⋀[ℚ]^i (V ⊗[ℚ] (Fin m → ℚ)))}
    (hF : IsDivisorPulledWeilClosed J D W F) (k : ℕ) :
    divisorPulledWeilSpan J D W k ≤ F k := iInf₂_le F hF

theorem isDivisorPulledWeilClosed_span :
    IsDivisorPulledWeilClosed J D W (divisorPulledWeilSpan J D W) where
  unit_mem := by
    simp only [divisorPulledWeilSpan, Submodule.mem_iInf]
    exact fun F hF => hF.unit_mem
  divisor_le := le_iInf₂ fun _ hF => hF.divisor_le
  pullback_mem r s w hw := by
    simp only [divisorPulledWeilSpan, Submodule.mem_iInf]
    exact fun F hF => hF.pullback_mem r s w hw
  wedge_mem i j v w hv hw := by
    simp only [divisorPulledWeilSpan, Submodule.mem_iInf] at hv hw ⊢
    exact fun F hF => hF.wedge_mem i j v w (hv F hF) (hw F hF)

example (r s : Fin m → ℚ) (w : ⋀[ℚ]^n V) (hw : w ∈ W) :
    exteriorPower.map n (weilPowerPullback J r s) w ∈ divisorPulledWeilSpan J D W n :=
  (isDivisorPulledWeilClosed_span J D W).pullback_mem r s w hw

/-- In particular the first projection pullback on a square has the original degree. -/
theorem firstProjection_mem_divisorPulledWeilSpan
    (D₂ : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin 2 → ℚ))))
    (w : ⋀[ℚ]^n V) (hw : w ∈ W) :
    exteriorPower.map n (weilPowerPullback J (Pi.single 0 1 : Fin 2 → ℚ) 0) w ∈
      divisorPulledWeilSpan J D₂ W n :=
  (isDivisorPulledWeilClosed_span J D₂ W).pullback_mem _ _ w hw

/-- Restriction to the `i`-th factor is a left inverse to its projection pullback. -/
theorem factorRestriction_comp_pullback {l : ℕ} (i : Fin l) :
    ((TensorProduct.rid ℚ V).toLinearMap.comp
      ((LinearMap.proj i : (Fin l → ℚ) →ₗ[ℚ] ℚ).lTensor V)).comp
        (weilPowerPullback J (Pi.single i 1) 0) = LinearMap.id := by
  ext x
  simp [weilPowerPullback]

/-- Retraction falsification: an exceptional original class remains outside any
power subspace whose restriction lies in the original divisor subspace.
Taking `P` and `Q` to be the respective divisor subrings gives the restriction
argument in `WeilClasses.lean`. The premise about restriction is explicit. -/
theorem projection_pullback_not_mem {l : ℕ} (i : Fin l)
    (P : Submodule ℚ (⋀[ℚ]^n V))
    (Q : Submodule ℚ (⋀[ℚ]^n (V ⊗[ℚ] (Fin l → ℚ))))
    (hQ : Q.map (exteriorPower.map n ((TensorProduct.rid ℚ V).toLinearMap.comp
      ((LinearMap.proj i : (Fin l → ℚ) →ₗ[ℚ] ℚ).lTensor V))) ≤ P)
    (w : ⋀[ℚ]^n V) (hw : w ∉ P) :
    exteriorPower.map n (weilPowerPullback J (Pi.single i 1) 0) w ∉ Q := by
  intro h
  have hh := hQ (Submodule.mem_map_of_mem h)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    factorRestriction_comp_pullback, exteriorPower.map_id] at hh
  exact hw hh

end HodgeLean.Foundations.WeilPower
