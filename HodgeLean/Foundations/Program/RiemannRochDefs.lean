import HodgeLean.Foundations.Program.HurwitzPrymRRForm
import HodgeLean.Foundations.Program.HurwitzPrymCovSphere
import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Residue.Basic

set_option maxHeartbeats 400000

/-! # Riemann--Roch for compact Riemann surfaces: definitions

Meromorphic functions are sphere-valued holomorphic maps, with the constant infinity map
excluded.  Their order is computed in the zero and infinity charts.  Meromorphic forms are
fibrewise-linear functions on the tangent bundle whose coefficient in every centred chart is
meromorphic.  Finiteness of divisor support is established separately.

HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open TauCeti.Contour
open scoped ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
local instance : DecidableEq (OnePoint ℂ) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p

section Functions

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The analytic condition defining meromorphic functions on `C`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
def b4c_IsMeroFun (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (f : C → OnePoint ℂ) : Prop :=
  ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω f ∧ ∃ x, f x ≠ OnePoint.infty

/-- Meromorphic functions on `C`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
def b4c_MeroFun (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] :=
  {f : C → OnePoint ℂ // b4c_IsMeroFun E f}

instance : CoeFun (b4c_MeroFun E C) (fun _ ↦ C → OnePoint ℂ) := ⟨Subtype.val⟩

/-- The order of a meromorphic function: positive at a zero, negative at a pole, and zero
elsewhere.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
def b4c_ord (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (f : C → OnePoint ℂ) (x : C) : ℤ :=
  if f x = (0 : ℂ) then
    b4_ramIndex E ℂ f x
  else if f x = OnePoint.infty then
    -(b4_ramIndex E ℂ f x : ℤ)
  else 0

/-- The divisor of a meromorphic function.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
noncomputable def b4c_div (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (f : C → OnePoint ℂ) : C →₀ ℤ :=
  if h : (Function.support (b4c_ord E f)).Finite then
    Finsupp.onFinset h.toFinset (b4c_ord E f) (fun x hx ↦ h.mem_toFinset.mpr hx)
  else 0

end Functions

section Forms

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The analytic condition defining meromorphic `1`-forms.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_IsMeroForm (hE : Module.finrank ℂ E = 1)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) : Prop :=
  HurwitzPrymRR_IsLinear θ ∧ ∀ x, MeromorphicAt (HurwitzPrymRR_loc hE θ x) 0

/-- Meromorphic `1`-forms on `C`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_MeroForm (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (hE : Module.finrank ℂ E = 1) :=
  {θ : TangentBundle 𝓘(ℂ, E) C → ℂ // b4c_IsMeroForm hE θ}

instance (hE : Module.finrank ℂ E = 1) : CoeFun (b4c_MeroForm E C hE)
    (fun _ ↦ TangentBundle 𝓘(ℂ, E) C → ℂ) := ⟨Subtype.val⟩

/-- The order of a meromorphic `1`-form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_ordForm {hE : Module.finrank ℂ E = 1}
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) (x : C) : ℤ :=
  (meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0).untop₀

/-- The divisor of a meromorphic `1`-form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
noncomputable def b4c_divForm {hE : Module.finrank ℂ E = 1}
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) : C →₀ ℤ :=
  if h : (Function.support (b4c_ordForm (hE := hE) w)).Finite then
    Finsupp.onFinset h.toFinset (b4c_ordForm (hE := hE) w)
      (fun x hx ↦ h.mem_toFinset.mpr hx)
  else 0

/-- The pullback of a meromorphic form along a nonconstant holomorphic map.  The analytic and
support arguments certify that the explicit tangent pullback is meromorphic with finite divisor.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_pullback {E' Y : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    {hE : Module.finrank ℂ E = 1} {hE' : Module.finrank ℂ E' = 1}
    (f : C → Y) (w : TangentBundle 𝓘(ℂ, E') Y → ℂ) :
    TangentBundle 𝓘(ℂ, E) C → ℂ :=
  b3_pullback E E' f w

/-- The quotient of two meromorphic forms, given by the quotient of their local coefficients.
The certification arguments package that explicit quotient as a sphere-valued meromorphic map.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_formRatio {hE : Module.finrank ℂ E = 1}
    (w₁ w₂ : TangentBundle 𝓘(ℂ, E) C → ℂ) : C → OnePoint ℂ :=
  fun x ↦
    let q := fun z ↦ HurwitzPrymRR_loc hE w₁ x z / HurwitzPrymRR_loc hE w₂ x z
    if meromorphicOrderAt q 0 < 0 then OnePoint.infty
    else if meromorphicOrderAt q 0 = 0 then
      ((meromorphicTrailingCoeffAt q 0 : ℂ) : OnePoint ℂ)
    else (0 : ℂ)

/-- The residue, defined as the one-variable residue of the centred local coefficient.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_res {hE : Module.finrank ℂ E = 1}
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) (x : C) : ℂ :=
  residue (HurwitzPrymRR_loc hE w x) 0

end Forms

section FormAction

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Pullback by a holomorphic self-map as an endomorphism of holomorphic `1`-forms.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9. -/
def b4c_formPullbackEnd (f : C → C) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f) :
    Module.End ℂ (b3_HolForm E C) where
  toFun w := ⟨b3_pullback E E f w, b3_pullback_mem_holForm f hf w w.2⟩
  map_add' w v := by ext p; rfl
  map_smul' a w := by ext p; rfl

example (f : C → C) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f) :
    b4c_formPullbackEnd f hf 0 = 0 := map_zero _

end FormAction

section Dolbeault

variable (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E

/-- Smooth complex-valued functions on the underlying real surface.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
def b4c_SmoothFun : Submodule ℂ (C → ℂ) where
  carrier := {f | ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f}
  zero_mem' := contMDiff_const
  add_mem' hf hg := hf.add hg
  smul_mem' a f hf := by
    have ha : ContDiff ℝ ∞ (fun z : ℂ ↦ a * z) := contDiff_const.mul contDiff_id
    exact ha.contMDiff.comp hf

example (c : ℂ) : (fun _ : ℂ ↦ c) ∈ b4c_SmoothFun ℂ ℂ :=
  contMDiff_const

example : (fun z : ℂ ↦ z) ∈ b4c_SmoothFun ℂ ℂ :=
  contMDiff_id

/-- Real smooth fibrewise conjugate-linear `(0,1)`-forms on the complex tangent bundle.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
def b4c_Smooth01 : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ) where
  carrier := {θ | ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, ℂ) ∞ θ ∧
    ∀ (x : C) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, E) x),
      θ ⟨x, a • v + w⟩ = star a * θ ⟨x, v⟩ + θ ⟨x, w⟩}
  zero_mem' := ⟨contMDiff_const, by simp⟩
  add_mem' := by
    rintro θ η ⟨hθ, hθ'⟩ ⟨hη, hη'⟩
    refine ⟨hθ.add hη, ?_⟩
    intro x a v w
    simp only [Pi.add_apply, hθ', hη']
    ring
  smul_mem' := by
    rintro a θ ⟨hθ, hθ'⟩
    have ha : ContDiff ℝ ∞ (fun z : ℂ ↦ a * z) := contDiff_const.mul contDiff_id
    refine ⟨ha.contMDiff.comp hθ, ?_⟩
    intro x b v w
    simp only [Pi.smul_apply, smul_eq_mul, hθ']
    ring

/-- The conjugate-linear part of the real differential, with `J v = i • v` in tangent
coordinates. Smoothness and the image description are stated separately.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
def b4c_dbar (u : C → ℂ) : TangentBundle 𝓘(ℂ, E) C → ℂ :=
  fun p ↦
    let du : E →L[ℝ] ℂ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) u p.1
    (du p.2 + Complex.I * du (Complex.I • p.2)) / 2

/-- Degree `(0,1)` Dolbeault cohomology. The denominator is the span of real smooth
`∂̄` images, pulled back to smooth `(0,1)`-forms by the subtype inclusion.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
abbrev b4c_Dolbeault01 : Type := (b4c_Smooth01 E C) ⧸
  (Submodule.span ℂ (b4c_dbar E C '' (b4c_SmoothFun E C : Set (C → ℂ)))).comap
    (b4c_Smooth01 E C).subtype

end Dolbeault

/-- On the identity chart of the complex plane, `∂̄` of conjugation is nonzero.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §15. -/
example (z : ℂ) : b4c_dbar ℂ ℂ (starRingEnd ℂ) ⟨z, (1 : ℂ)⟩ = 1 := by
  simp only [b4c_dbar, mfderiv_eq_fderiv]
  change (fderiv ℝ (starRingEnd ℂ) z (1 : ℂ) +
    Complex.I * fderiv ℝ (starRingEnd ℂ) z (Complex.I * 1)) / 2 = 1
  rw [show fderiv ℝ (starRingEnd ℂ) z = (Complex.conjCLE : ℂ →L[ℝ] ℂ) from
    Complex.conjCLE.fderiv]
  simp [Complex.conjCLE_apply, Complex.I_mul_I]



section Rotation

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The scalar by which a holomorphic self-map acts on the tangent line at a fixed point.
Source: Farkas--Kra, *Riemann Surfaces*, 2nd ed., V.2.9. -/
def b4c_rotation (hE : Module.finrank ℂ E = 1) (s : C → C) (p : C) : ℂ :=
  (b4cov_lineEquiv hE).symm
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) s p (b4cov_lineEquiv hE 1))

end Rotation

section Examples

/-- The affine coordinate differential in the chosen sphere atlas. At infinity its coefficient
is assigned zero; on the punctured infinity chart the coefficient is `-1 / w²`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14. -/
def b4c_dz_sphere : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ) → ℂ :=
  fun p ↦ if p.1 = OnePoint.infty then 0 else p.2

example (v : ℂ) : b4c_dz_sphere ⟨OnePoint.infty, v⟩ = 0 := by
  simp [b4c_dz_sphere]

/-- The invariant differential in the translation charts of B3's quotient torus.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §21. -/
def b4c_dz_elliptic : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ :=
  fun p ↦ (b4cov_lineEquiv b3_ellipticModel_finrank).symm p.2

example (x : b3_Elliptic) : b4c_dz_elliptic ⟨x, 0⟩ = 0 := map_zero _

end Examples

section Divisors

variable {C : Type}

/-- The degree of a divisor.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §13. -/
def b4c_deg (D : C →₀ ℤ) : ℤ := D.sum fun _ n ↦ n

example (x : C) (n : ℤ) : b4c_deg (Finsupp.single x n) = n := by simp [b4c_deg]

end Divisors

section RRSpace

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The vector space `L(D)`, encoded on the complement of `supp D`.  Its generators are the
restrictions of meromorphic functions whose poles lie in `supp D` and whose orders satisfy
`ord_x(f) + D_x ≥ 0`; taking their span supplies the zero function and vector-space operations.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §16. -/
def b4c_L (D : C →₀ ℤ) : Submodule ℂ ({x : C // x ∉ D.support} → ℂ) :=
  Submodule.span ℂ {g | ∃ f : b4c_MeroFun E C,
    (∃ x, f x ≠ (0 : ℂ)) ∧
    (∀ x, x ∉ D.support → f x ≠ OnePoint.infty) ∧
    (∀ x, 0 ≤ b4c_ord E f x + D x) ∧
    g = fun x ↦ (f x.1).elim 0 id}

example (D : C →₀ ℤ) : (0 : {x : C // x ∉ D.support} → ℂ) ∈ b4c_L (E := E) D :=
  (b4c_L D).zero_mem

end RRSpace

end HodgeLean.Foundations.Program
