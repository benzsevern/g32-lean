import HodgeLean.Foundations.Program.RelativeFrameGateProofs
import HodgeLean.Foundations.Program.PrymVariationFramesDefs

/-! # C8 and bounded chart forms: statement draft
Implication from explicit compact surface and meromorphic differential data to the canonical
Dolbeault bound, and from finite analytic chart pieces to Banach coefficient spaces. This draft
supplies no plumbing charts, family operator, relative frame or period map. The coordinate model
is one-dimensional over `ℂ`; transport from other one-dimensional models is later work.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program
local instance rf2_decidableSpec (p : Prop) : Decidable p := Classical.propDecidable p

/-- Piecewise uniform limits preserve the overlap identities; bounded forms form a Banach space.
Source: RelativeFrame §5, A15--A16; Rudin, *Functional Analysis*, 2nd ed., Ch. 1. -/
theorem rf2_bddForm_banach {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) :
    IsClosed (rf2_bddForm P : Set (∀ i, b63r_bddHol (P.piece i))) ∧
      CompleteSpace (rf2_bddForm P) :=
  rf2_bddForm_banach_aux P

example := @rf2_bddForm_banach

/-- Coefficient projections have norm at most one.
Source: RelativeFrame §5, A17; Rudin, *Functional Analysis*, Ch. 1. -/
theorem rf2_bddForm_coeff_bound {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) (i : Fin P.n) :
    ‖rf2_bddForm_coeff P i‖ ≤ 1 :=
  rf2_bddForm_coeff_bound_aux P i

example := @rf2_bddForm_coeff_bound

/-- The signed chart differential takes smooth `(1,0)` forms to smooth `(1,1)` forms.
Source: Forster, *Lectures on Riemann Surfaces*, §15; RelativeFrame §4.5, step 1. -/
theorem rf2_dbar10_smooth (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (v : rf2_smoothForms C 1 0) :
    rf2_dbar10 C v.val ∈ rf2_smoothForms C 1 1 :=
  rf2_dbar10_smooth_aux C v

example := @rf2_dbar10_smooth

/-- The chart quotient agrees with the tangent-bundle Dolbeault quotient.
Source: Forster, §15; `b4c_Dolbeault01`; RelativeFrame §4.5, step 3. -/
theorem rf2_dolbeault01_compare (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    Nonempty (((rf2_smoothForms C 0 1) ⧸ rf2_boundaries01 C) ≃ₗ[ℂ]
      b4c_Dolbeault01 ℂ C) :=
  rf2_dolbeault01_compare_aux C

example := @rf2_dolbeault01_compare

/-- Two cutoffs give a supported local Cauchy solution with the form sign.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
Theorem 1.2.2; RelativeFrame §4.5, step 1. -/
theorem rf2_local_cauchy (a : ℂ → ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (ha : ContDiffOn ℝ ∞ a (Metric.ball 0 R)) :
    ∃ χ ψ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ ContDiff ℝ ∞ ψ ∧
      HasCompactSupport χ ∧ HasCompactSupport ψ ∧
      tsupport χ ⊆ Metric.ball 0 R ∧ tsupport ψ ⊆ Metric.ball 0 ((r + R) / 2) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ((r + R) / 2), χ z = 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ψ z = 1) ∧
      let v := fun z ↦ ψ z * cauchyTransform
        (fun ζ ↦ if ζ ∈ Metric.ball (0 : ℂ) R then -(χ ζ * a ζ) else 0) z
      ContDiff ℝ ∞ v ∧ tsupport v ⊆ Metric.ball 0 R ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, -wirtingerDbar v z = a z :=
  rf2_local_cauchy_aux a r R hr hrR ha

example := @rf2_local_cauchy

/-- Subtracting a supported differential makes a top-degree form vanish near any finite set.
Source: Forster, §13, Theorem 13.2; RelativeFrame §4.5, step 1. -/
theorem rf2_dbar11_localize (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (Z : Finset C) (τ : rf2_smoothForms C 1 1) :
    ∃ (N : Set C) (v : rf2_smoothForms C 1 0), IsOpen N ∧ (↑Z : Set C) ⊆ N ∧
      ∀ x (z : (chartAt ℂ x).target), (chartAt ℂ x).symm z ∈ N →
        τ.val x z - rf2_dbar10 C v.val x z = 0 :=
  rf2_dbar11_localize_aux C Z τ

example := @rf2_dbar11_localize

/-- Multiplication by the differential is invertible on forms vanishing near its divisor.
Source: Forster, §§14--15; RelativeFrame §4.5, step 2. Division takes place only on the
holomorphic nonzero locus. -/
theorem rf2_divide_by_form (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤) (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N) :
    ∃ e : rf2_vanishing C 0 1 N ≃ₗ[ℂ] rf2_vanishing C 1 1 N,
      ∀ (θ : rf2_vanishing C 0 1 N) x (z : (chartAt ℂ x).target),
        (e θ).val.val x z = rf2_meroCoeff C w x z * θ.val.val x z :=
  rf2_divide_by_form_aux C w hw hgw N hN hZN

example := @rf2_divide_by_form

/-- The finite jet map detects removal of a pole of order `m`.
Source: Forster, §14; RelativeFrame §4.5, step 5 (Laurent coefficients). -/
theorem rf2_principalPart_removable (m : ℕ) (hm : 0 < m) (c h : ℂ → ℂ)
    (hc : AnalyticAt ℂ c 0) (hc0 : c 0 ≠ 0) (hh : AnalyticAt ℂ h 0) :
    (∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      (fun z ↦ z ^ (-(m : ℤ)) * c z * h z) =ᶠ[𝓝[≠] 0] F) ↔
      rf2_principalPart m (fun k ↦ iteratedDeriv k.val c 0 / (k.val.factorial : ℂ))
        (fun k ↦ iteratedDeriv k.val h 0 / (k.val.factorial : ℂ)) = 0 :=
  rf2_principalPart_removable_aux m hm c h hc hc0 hh

example := @rf2_principalPart_removable

/-- A normalized primitive gives a finite principal-part obstruction whose kernel gives smooth
canonical boundaries. The target retains all pole coefficients; primitive normalization removes
constants before taking jets.
Source: Forster, §§14--15; RelativeFrame §4.5, steps 4--5. -/
theorem rf2_principal_obstruction (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤) (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N) :
    ∃ π : rf2_exactAway C N →ₗ[ℂ] (Fin (rf2_poleBudget C w) → ℂ),
      ∀ θ ∈ π.ker,
        (fun x z ↦ rf2_meroCoeff C w x z * θ.val.val x z) ∈
          Submodule.span ℂ (rf2_dbar10 C ''
            (rf2_smoothForms C 1 0 : Set (rf2_Coeff C))) :=
  rf2_principal_obstruction_aux C w hw hgw N hN hZN

example := @rf2_principal_obstruction

/-- Localization, scalar Dolbeault cohomology and principal parts bound canonical cohomology.
Source: Forster, §§13--17; RelativeFrame §4.5, step 6; `b4c_dolbeault_finite`. -/
theorem rf2_dbar_forms (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤) :
    Module.Finite ℂ ((rf2_smoothForms C 1 1) ⧸ rf2_boundaries C) ∧
      Module.finrank ℂ ((rf2_smoothForms C 1 1) ⧸ rf2_boundaries C) ≤
        Module.finrank ℂ (b3_HolForm ℂ C) + rf2_poleBudget C w :=
  rf2_dbar_forms_aux C w hw hgw

example := @rf2_dbar_forms

/-- Chain check: an analytic bounded chart-form family has jointly analytic coefficients,
which is the outer-chart analytic input of `b63e_relForm`.
Source: RelativeFrame §4.4; `b63r_eval_analytic`; `PrymVariationFramesDefs.b63e_relForm`. -/
example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O)
    {k : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (e : (Fin k → ℂ) → rf2_bddForm P) (he : AnalyticOnNhd ℂ e W) (i : Fin P.n) :
    AnalyticOn ℂ (fun p : (Fin k → ℂ) × ℂ ↦
      if h : p.2 ∈ P.piece i then
        ((rf2_bddForm_coeff P i (e p.1) : b63r_bddHol (P.piece i)) : P.piece i →ᵇ ℂ)
          ⟨p.2, h⟩ else 0) (W ×ˢ P.piece i) :=
  (b63r_eval_analytic (P.isOpen i) W hW _
    ((rf2_bddForm_coeff P i).comp_analyticOnNhd he)).analyticOn

#check @b63e_relForm

end HodgeLean.Foundations.Program
