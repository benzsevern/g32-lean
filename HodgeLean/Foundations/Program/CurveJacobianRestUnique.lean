import HodgeLean.Foundations.Program.CurveJacobianRestTransverse
import HodgeLean.Foundations.Program.CurveJacobianAPlumbing

/-! # Track B3, lane Rest: uniqueness and skew-symmetry of intersection forms

Every pair of `C¹` loops `γ`, `δ` has a `C¹` loop `δ'` transverse to `γ` with the periods of `δ`
(`b3Rest_exists_transverse`). So a form computing intersection numbers of transverse loops is
determined on all pairs of generators `(λ_γ, λ_δ)` of the period lattice, hence everywhere
(`b3Rest_intersectionForm_unique`). With the antisymmetry of intersection numbers of transverse
pairs it is skew-symmetric and alternating (`b3Rest_intersectionForm_alt`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Manifold
open scoped ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The lattice periods generate the period lattice. -/
theorem b3Rest_closure_latticePeriod :
    AddSubgroup.closure (Set.range (b3_latticePeriod E C)) = ⊤ := by
  have hs : Set.range (b3_latticePeriod E C) =
      ((↑) : b3_periodLattice E C → (b3_HolForm E C → ℂ)) ⁻¹' Set.range (b3_period E C) := by
    ext x
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, rfl⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨γ, Subtype.ext hγ⟩
  rw [hs]
  exact AddSubgroup.closure_closure_coe_preimage

/-- **Bilinear forms on the period lattice agreeing on pairs of lattice periods are equal.** -/
theorem b3Rest_bilin_ext (Q Q' : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (h : ∀ γ δ : b3_SmoothLoop E C,
      Q (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) =
        Q' (b3_latticePeriod E C γ) (b3_latticePeriod E C δ)) : Q = Q' := by
  have hmem : ∀ y : b3_periodLattice E C,
      y ∈ AddSubgroup.closure (Set.range (b3_latticePeriod E C)) := fun y ↦ by
    rw [b3Rest_closure_latticePeriod]; exact AddSubgroup.mem_top y
  have h1 : ∀ (γ : b3_SmoothLoop E C) (y : b3_periodLattice E C),
      Q (b3_latticePeriod E C γ) y = Q' (b3_latticePeriod E C γ) y := by
    intro γ y
    induction hmem y using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨δ, rfl⟩ := hy
      exact h γ δ
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | neg y _ hy => simp [hy]
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  induction hmem x using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, rfl⟩ := hx
    exact h1 γ y
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | neg x _ hx => simp [hx]

/-- On pairs of lattice periods, an intersection form is the intersection number of `γ` with a
transverse representative of `δ`. -/
theorem b3Rest_intersectionForm_apply
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (γ δ δ' : b3_SmoothLoop E C) (htr : b3_Transverse E γ δ')
    (hper : b3_period E C δ' = b3_period E C δ) :
    Q (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) = b3_intersection E γ δ' := by
  have hl : b3_latticePeriod E C δ' = b3_latticePeriod E C δ := Subtype.ext hper
  rw [← hl, hQ γ δ' htr]

/-- **Intersection forms are unique.** -/
theorem b3Rest_intersectionForm_unique (hE : Module.finrank ℂ E = 1)
    (Q Q' : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) (hQ' : b3_IsIntersectionForm E Q') : Q = Q' := by
  refine b3Rest_bilin_ext Q Q' fun γ δ ↦ ?_
  obtain ⟨δ', htr, hper⟩ := b3Rest_exists_transverse hE γ δ
  rw [b3Rest_intersectionForm_apply Q hQ γ δ δ' htr hper,
    b3Rest_intersectionForm_apply Q' hQ' γ δ δ' htr hper]

omit [IsManifold 𝓘(ℂ, E) ω C] in
/-- Transversality is symmetric. -/
theorem b3Rest_transverse_symm {γ δ : b3_SmoothLoop E C} (h : b3_Transverse E γ δ) :
    b3_Transverse E δ γ := by
  intro s t hst
  have := h t s hst.symm
  intro h0
  apply this
  have hanti : b3_orient E (b3_velocity E C γ.1 t) (b3_velocity E C δ.1 s) =
      -b3_orient E (b3_velocity E C δ.1 s) (b3_velocity E C γ.1 t) := by
    simp only [b3_orient, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hanti, h0, neg_zero]

/-- **Intersection forms are skew-symmetric.** -/
theorem b3Rest_intersectionForm_skew (hE : Module.finrank ℂ E = 1)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (x y : b3_periodLattice E C) : Q y x = -Q x y := by
  let Q' : LinearMap.BilinForm ℤ (b3_periodLattice E C) := -Q.flip
  have hgen : ∀ γ δ : b3_SmoothLoop E C,
      Q (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) =
        Q' (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) := by
    intro γ δ
    obtain ⟨δ', htr, hper⟩ := b3Rest_exists_transverse hE γ δ
    have hl : b3_latticePeriod E C δ' = b3_latticePeriod E C δ := Subtype.ext hper
    show _ = -Q (b3_latticePeriod E C δ) (b3_latticePeriod E C γ)
    rw [← hl, hQ γ δ' htr, hQ δ' γ (b3Rest_transverse_symm htr),
      b3A_intersection_antisymm γ δ', neg_neg]
  have := congrArg (fun B : LinearMap.BilinForm ℤ (b3_periodLattice E C) ↦ B y x)
    (b3Rest_bilin_ext Q Q' hgen)
  simp only [Q', LinearMap.neg_apply] at this
  exact this

/-- **Intersection forms are alternating.** -/
theorem b3Rest_intersectionForm_alt (hE : Module.finrank ℂ E = 1)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (x : b3_periodLattice E C) : Q x x = 0 := by
  have := b3Rest_intersectionForm_skew hE Q hQ x x
  omega

end HodgeLean.Foundations.Program
