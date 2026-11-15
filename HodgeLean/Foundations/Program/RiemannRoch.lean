import HodgeLean.Foundations.Program.RiemannRochProofs

set_option maxHeartbeats 400000

/-! # Riemann--Roch for compact Riemann surfaces (frozen specification)

This file states the divisor, residue, Riemann--Roch, genus-zero, punctured-sphere and Eichler
trace inputs needed by track B4.  It claims implications from the displayed compact Riemann
surface hypotheses and the analytic constructions in `RiemannRochDefs`; it does not claim an
algebraic-curve comparison or a general uniformization theorem.

HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open TauCeti.Contour
open scoped ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The order support of a meromorphic function on a compact surface is finite.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
theorem b4c_meroFun_orderSupport_finite [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C) :
    (Function.support (b4c_ord E f)).Finite :=
  b4c_meroFun_orderSupport_finite_aux hE f

/-- The order support of a meromorphic form on a compact surface is finite.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_meroForm_orderSupport_finite [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (w : b4c_MeroForm E C hE) :
    (Function.support (b4c_ordForm (hE := hE) w)).Finite :=
  b4c_meroForm_orderSupport_finite_aux hE w

/-- The constructed ratio has finite order support.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_formRatio_spec [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (w₁ w₂ : b4c_MeroForm E C hE)
    (hw₁ : (w₁ : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hw₂ : (w₂ : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hg₁ : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w₁ x) 0 ≠ ⊤)
    (hg₂ : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w₂ x) 0 ≠ ⊤) :
    (Function.support (b4c_ord E (b4c_formRatio (hE := hE) w₁ w₂))).Finite :=
  b4c_formRatio_spec_aux hE w₁ w₂ hw₁ hw₂ hg₁ hg₂

/-- The quotient of meromorphic forms is a meromorphic function when the denominator is nonzero.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_formRatio_isMeroFun [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (w₁ w₂ : b4c_MeroForm E C hE)
    (hw₁ : (w₁ : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hw₂ : (w₂ : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hg₁ : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w₁ x) 0 ≠ ⊤)
    (hg₂ : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w₂ x) 0 ≠ ⊤) :
    b4c_IsMeroFun E (b4c_formRatio (hE := hE) w₁ w₂) :=
  b4c_formRatio_isMeroFun_aux hE w₁ w₂ hw₁ hw₂ hg₁ hg₂

/-- Pullback along a nonconstant holomorphic map preserves meromorphic forms.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_pullback_isMeroForm (hE : Module.finrank ℂ E = 1)
    {E' Y : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x')
    (w : b4c_MeroForm E' Y hE') :
    b4c_IsMeroForm hE (b4c_pullback (hE := hE) (hE' := hE') f w) :=
  b4c_pullback_isMeroForm_aux hE hE' f hf hnc w

/-- Pullback along a nonconstant holomorphic map has finite order support.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_pullback_mem [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {E' Y : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x')
    (w : b4c_MeroForm E' Y hE') :
    (Function.support (b4c_ordForm (hE := hE)
      (b4c_pullback (hE := hE) (hE' := hE') f w))).Finite :=
  b4c_pullback_mem_aux hE hE' f hf hnc w

/-- The tangent scalar agrees with its centred-chart expression.
Source: Farkas--Kra, *Riemann Surfaces*, 2nd ed., V.2. -/
theorem b4c_rotation_chart_independent (hE : Module.finrank ℂ E = 1) (s : C → C)
    (hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω s) (p : C) (hp : s p = p)
    (φ : OpenPartialHomeomorph C E) (hφ : φ ∈ atlas E C) (hpφ : p ∈ φ.source) :
    b4c_rotation hE s p = (b4cov_lineEquiv hE).symm
      (fderiv ℂ (φ ∘ s ∘ φ.symm) (φ p) (b4cov_lineEquiv hE 1)) :=
  b4c_rotation_chart_independent_aux hE s hs p hp φ hφ hpφ

/-- Principal divisors have degree zero.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
theorem b4c_deg_div_meroFun [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hf : ∃ x, f x ≠ (0 : ℂ)) : b4c_deg (b4c_div E f) = 0 :=
  b4c_deg_div_meroFun_aux hE f hf
example := @b4c_deg_div_meroFun

/-- Divisors turn the quotient of meromorphic forms into subtraction.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_divForm_sub [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (w₁ w₂ : b4c_MeroForm E C hE)
    (hw₁ : (w₁ : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hw₂ : (w₂ : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hg₁ : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w₁ x) 0 ≠ ⊤)
    (hg₂ : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w₂ x) 0 ≠ ⊤) :
    b4c_divForm (hE := hE) w₁ - b4c_divForm (hE := hE) w₂ =
      b4c_div E (b4c_formRatio (hE := hE) w₁ w₂) :=
  b4c_divForm_sub_aux hE w₁ w₂ hw₁ hw₂ hg₁ hg₂
example := @b4c_divForm_sub

/-- The sum of the residues of a meromorphic form on a compact surface is zero.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
theorem b4c_residue_sum [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (w : b4c_MeroForm E C hE) :
    ∑ᶠ x : C, b4c_res (hE := hE) w x = 0 :=
  b4c_residue_sum_aux hE w
example := @b4c_residue_sum

/-- The Dolbeault finiteness input in genus degree one.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15; Farkas--Kra, III.4. -/
theorem b4c_dolbeault_finite [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) : Module.Finite ℂ (b4c_Dolbeault01 E C) ∧
      Module.finrank ℂ (b4c_Dolbeault01 E C) = Module.finrank ℂ (b3_HolForm E C) :=
  b4c_dolbeault_finite_aux hE
example := @b4c_dolbeault_finite

/-- `g + 1` prescribed points support a nonconstant meromorphic function with simple poles.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
theorem b4c_exists_meroFun [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p : Fin (Module.finrank ℂ (b3_HolForm E C) + 1) → C)
    (hp : Function.Injective p) : ∃ f : b4c_MeroFun E C, (∃ x y, f x ≠ f y) ∧
      ∀ x, -(1 : ℤ) ≤ b4c_ord E f x ∧ (x ∉ Set.range p → 0 ≤ b4c_ord E f x) :=
  b4c_exists_meroFun_aux hE p hp
example := @b4c_exists_meroFun

/-- Riemann--Roch for a divisor and a nonzero meromorphic canonical form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §16. -/
theorem b4c_riemannRoch [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 ≠ ⊤) :
    (Module.finrank ℂ (b4c_L (E := E) D) : ℤ) - Module.finrank ℂ
      (b4c_L (E := E) (b4c_divForm (hE := hE) w - D)) =
        b4c_deg D - Module.finrank ℂ (b3_HolForm E C) + 1 :=
  b4c_riemannRoch_aux hE D w hw hgw
example := @b4c_riemannRoch

/-- Every compact Riemann surface carries a nonzero meromorphic `1`-form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14--16. -/
theorem b4c_exists_meroForm [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) : ∃ w : b4c_MeroForm E C hE,
      (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 ∧
      ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 ≠ ⊤ :=
  b4c_exists_meroForm_aux hE
example := @b4c_exists_meroForm

/-- A canonical divisor has degree `2g - 2`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §16--17. -/
theorem b4c_deg_canonical [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 ≠ ⊤) :
    b4c_deg (b4c_divForm (hE := hE) w) =
      2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 :=
  b4c_deg_canonical_aux hE w hw hgw
example := @b4c_deg_canonical

/-- A compact connected Riemann surface of genus zero is biholomorphic to the sphere.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §17. -/
theorem b4c_genusZero_equiv [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (hg : Module.finrank ℂ (b3_HolForm E C) = 0) :
    ∃ e : C ≃ₜ OnePoint ℂ, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e.symm :=
  b4c_genusZero_equiv_aux hE hg
example := @b4c_genusZero_equiv

/-- Riemann--Hurwitz in the signature used by track B4.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §17. -/
theorem b4c_riemannHurwitz [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {E' Y : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y : Y) :
    2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 = b4_fiberDegree E E' f y *
      (2 * (Module.finrank ℂ (b3_HolForm E' Y) : ℤ) - 2) + ∑ᶠ x : C, ((b4_ramIndex E E' f x : ℤ) - 1) :=
  b4c_riemannHurwitz_aux hE hE' f hf hnc y
example := @b4c_riemannHurwitz

/-- Standard generators, relation and universal property for a punctured Riemann sphere.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13--17; Farkas--Kra, III.4--III.6. -/
theorem b4c_pi1_puncturedSphere {r : ℕ} (b : Fin r → OnePoint ℂ)
    (hb : Function.Injective b) (y₀ : {y : OnePoint ℂ // y ∉ Set.range b}) :
    ∃ γ : Fin r → FundamentalGroup {y : OnePoint ℂ // y ∉ Set.range b} y₀,
      (List.ofFn γ).prod = 1 ∧
      (∀ (H : Type) [Group H] (k : Fin r → H), (List.ofFn k).prod = 1 →
        ∃! φ : FundamentalGroup {y : OnePoint ℂ // y ∉ Set.range b} y₀ →* H, ∀ j, φ (γ j) = k j) ∧
      ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E']
        (hE' : Module.finrank ℂ E' = 1) (C' : Type) [TopologicalSpace C'] [ChartedSpace E' C'] [IsManifold 𝓘(ℂ, E') ω C']
        [T2Space C'] [CompactSpace C'] [ConnectedSpace C'] (G : Type) [Group G] [Finite G]
        [MulAction G C'] [FaithfulSMul G C'],
        (∀ g : G, ContMDiff 𝓘(ℂ, E') 𝓘(ℂ, E') ω (fun x : C' ↦ g • x)) →
        ∀ f : C' → OnePoint ℂ, ContMDiff 𝓘(ℂ, E') 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover G f →
        (∀ x, f x ∉ Set.range b → MulAction.stabilizer G x = ⊥) →
        ∀ (j : Fin r) (c : Path y₀ y₀), FundamentalGroup.fromPath ⟦c⟧ = γ j →
        ∀ (Γ : C(unitInterval, C')) (k : G), (∀ t, f (Γ t) = (c t : OnePoint ℂ)) →
          Γ 1 = k • Γ 0 → ∃ x, f x = b j ∧ b4_IsRotGen E' x k :=
  b4c_pi1_puncturedSphere_aux b hb y₀
example := @b4c_pi1_puncturedSphere

/-- Eichler's trace formula for a nontrivial finite-order automorphism.
B4 uses `b4_formAct g = (g⁻¹)^*`, so apply this to `s = g⁻¹` with inverse rotation.
Source: Farkas--Kra, *Riemann Surfaces*, 2nd ed., V.2.9. -/
theorem b4c_eichler_trace [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (s : C ≃ₜ C) (hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω s)
    (hne : s ≠ Homeomorph.refl C) (n : ℕ) (hn : 0 < n) (hord : s^[n] = id) :
    LinearMap.trace ℂ (b3_HolForm E C) (b4c_formPullbackEnd s hs) =
      1 + ∑ᶠ p : C, if s p = p then b4c_rotation hE s p / (1 - b4c_rotation hE s p) else 0 :=
  b4c_eichler_trace_aux hE s hs hne n hn hord
example := @b4c_eichler_trace

/-- The affine coordinate differential on the sphere has divisor degree `-2`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 and §16. -/
theorem b4c_sphere_dz : b4c_divForm (hE := by simp) b4c_dz_sphere =
    -2 • Finsupp.single OnePoint.infty 1 ∧
      b4c_deg (b4c_divForm (hE := by simp) b4c_dz_sphere) = -2 :=
  b4c_sphere_dz_aux
example : b4c_deg (b4c_divForm (hE := by simp) b4c_dz_sphere) = -2 :=
  b4c_sphere_dz.2

/-- The invariant differential on B3's elliptic curve has zero divisor.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 and §21. -/
theorem b4c_elliptic_dz :
    b4c_divForm (hE := b3_ellipticModel_finrank) b4c_dz_elliptic = 0 :=
  b4c_elliptic_dz_aux
example := b4c_elliptic_dz

/-- Membership of the coordinate differential.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 and §21. -/
theorem b4c_dz_sphere_mem : b4c_IsMeroForm (E := ℂ) (C := OnePoint ℂ) (by simp) b4c_dz_sphere :=
  b4c_dz_sphere_mem_aux

/-- Membership of the coordinate differential.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 and §21. -/
theorem b4c_dz_elliptic_mem : b4c_IsMeroForm b3_ellipticModel_finrank b4c_dz_elliptic :=
  b4c_dz_elliptic_mem_aux

/-- The span consists exactly of the allowed restrictions and zero.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §16. -/
theorem b4c_L_eq_restrictions [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (D : C →₀ ℤ) :
    (b4c_L (E := E) D : Set ({x : C // x ∉ D.support} → ℂ)) =
      {g | g = 0 ∨ ∃ f : b4c_MeroFun E C,
        (∃ x, f x ≠ (0 : ℂ)) ∧
        (∀ x, x ∉ D.support → f x ≠ OnePoint.infty) ∧
        (∀ x, 0 ≤ b4c_ord E f x + D x) ∧
        g = fun x ↦ (f x.1).elim 0 id} :=
  b4c_L_eq_restrictions_aux hE D

/-- The analytic Dolbeault operator takes smooth functions to smooth `(0,1)`-forms.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
theorem b4c_dbar_mem (u : b4c_SmoothFun E C) :
    b4c_dbar E C u ∈ b4c_Smooth01 E C :=
  b4c_dbar_mem_aux u

/-- The image of the analytic Dolbeault operator is already a complex vector subspace.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
theorem b4c_dbar_image_eq (hE : Module.finrank ℂ E = 1) :
    (Submodule.span ℂ (b4c_dbar E C '' (b4c_SmoothFun E C : Set (C → ℂ))) :
      Set (TangentBundle 𝓘(ℂ, E) C → ℂ)) =
      b4c_dbar E C '' (b4c_SmoothFun E C : Set (C → ℂ)) :=
  b4c_dbar_image_eq_aux hE

/-- The conjugate-linear differential of a holomorphic function vanishes.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
theorem b4c_dbar_holomorphic (u : C → ℂ) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω u) :
    b4c_dbar E C u = 0 :=
  b4c_dbar_holomorphic_aux u hu

example (u : C → ℂ) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω u)
    (p : TangentBundle 𝓘(ℂ, E) C) : b4c_dbar E C u p = 0 :=
  congrFun (b4c_dbar_holomorphic u hu) p

end HodgeLean.Foundations.Program
