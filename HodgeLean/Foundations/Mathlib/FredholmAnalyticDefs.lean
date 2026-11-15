module

public import Mathlib

/-! # Definitions for the Fredholm and bounded holomorphic layer of the relative-frame plan -/

@[expose] public noncomputable section

open Set
open scoped BoundedContinuousFunction

namespace HodgeLean.Foundations

/-- Bounded holomorphic functions on `U ⊆ ℂ`: the bounded continuous functions on `U` that agree
on `U` with a function holomorphic on `U`. It is a submodule of `U →ᵇ ℂ`; it is the intended
space when `U` is open.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 17 (the space `H^∞`). -/
def b63r_bddHol (U : Set ℂ) : Submodule ℂ (U →ᵇ ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z : U, f z = g z}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, hf₁⟩ ⟨g₂, hg₂, hf₂⟩
    exact ⟨g₁ + g₂, hg₁.add hg₂, fun z => by simp [hf₁ z, hf₂ z]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, fun _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hf⟩
    exact ⟨c • g, hg.const_smul c, fun z => by simp [hf z]⟩

example (U : Set ℂ) : BoundedContinuousFunction.const U (1 : ℂ) ∈ b63r_bddHol U :=
  ⟨fun _ => 1, differentiableOn_const 1, fun _ => rfl⟩

/-- The continuous map `U' → U` induced by a map `ψ : ℂ → ℂ` continuous on `U'` with
`ψ(U') ⊆ U`.
Source: Munkres, *Topology*, 2nd ed., Theorem 18.2 (restricting domain and range). -/
def b63r_restrictMap {U U' : Set ℂ} (ψ : ℂ → ℂ) (hψ : ContinuousOn ψ U') (hmaps : MapsTo ψ U' U) :
    C(U', U) :=
  ⟨fun z => ⟨ψ z, hmaps z.2⟩, hψ.mapsToRestrict hmaps⟩

example : (b63r_restrictMap (U := univ) (U' := univ) id continuousOn_id (mapsTo_univ _ _)
    ⟨(2 : ℂ), trivial⟩ : ℂ) = 2 := rfl

/-- Composition with a fixed holomorphic map `ψ` sending `U'` into `U`, as a continuous linear map
of bounded holomorphic function spaces.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 10 (holomorphy of compositions). -/
def b63r_bddHol_comp {U U' : Set ℂ} (ψ : ℂ → ℂ) (hψ : DifferentiableOn ℂ ψ U')
    (hmaps : MapsTo ψ U' U) : b63r_bddHol U →L[ℂ] b63r_bddHol U' :=
  ((BoundedContinuousFunction.compContinuousCLM ℂ ℂ
      (b63r_restrictMap ψ hψ.continuousOn hmaps)).comp (b63r_bddHol U).subtypeL).codRestrict
    (b63r_bddHol U') (by
      rintro ⟨f, g, hg, hf⟩
      exact ⟨g ∘ ψ, hg.comp hψ hmaps, fun z => hf ⟨ψ z, hmaps z.2⟩⟩)

example (U : Set ℂ) (f : b63r_bddHol U) (z : U) :
    ((b63r_bddHol_comp id differentiableOn_id (mapsTo_id U) f : b63r_bddHol U) : U →ᵇ ℂ) z =
      (f : U →ᵇ ℂ) z := rfl

/-- Restriction of bounded holomorphic functions from `U` to `U' ⊆ U`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 17. -/
def b63r_bddHol_restrict {U U' : Set ℂ} (h : U' ⊆ U) : b63r_bddHol U →L[ℂ] b63r_bddHol U' :=
  b63r_bddHol_comp id differentiableOn_id h

example {U U' : Set ℂ} (h : U' ⊆ U) (f : b63r_bddHol U) (z : U') :
    ((b63r_bddHol_restrict h f : b63r_bddHol U') : U' →ᵇ ℂ) z = (f : U →ᵇ ℂ) (inclusion h z) :=
  rfl

/-- Multiplication by a fixed bounded holomorphic function `m`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 17 (`H^∞` is an algebra). -/
def b63r_bddHol_mul {U : Set ℂ} (m : b63r_bddHol U) : b63r_bddHol U →L[ℂ] b63r_bddHol U :=
  ((ContinuousLinearMap.mul ℂ (U →ᵇ ℂ) (m : U →ᵇ ℂ)).comp (b63r_bddHol U).subtypeL).codRestrict
    (b63r_bddHol U) (by
      obtain ⟨_, gm, hgm, hm⟩ := m
      rintro ⟨f, g, hg, hf⟩
      exact ⟨gm * g, hgm.mul hg, fun z => by simp [hm z, hf z]⟩)

example {U : Set ℂ} (m f : b63r_bddHol U) (z : U) :
    ((b63r_bddHol_mul m f : b63r_bddHol U) : U →ᵇ ℂ) z = (m : U →ᵇ ℂ) z * (f : U →ᵇ ℂ) z :=
  rfl

/-- The annulus `A_n = {u : r < |u|ⁿ < 2r}` of the plumbing description.
Source: `docs/specs/RelativeFrame.md`, §4.2; Ahlfors, *Complex Analysis*, 3rd ed., Ch. 5. -/
def b63r_annulus (n : ℕ) (r : ℝ) : Set ℂ :=
  {u | r < ‖u‖ ^ n ∧ ‖u‖ ^ n < 2 * r}

example : (3 / 2 : ℂ) ∈ b63r_annulus 1 1 := by
  constructor <;> norm_num [b63r_annulus, Complex.norm_div]

end HodgeLean.Foundations
