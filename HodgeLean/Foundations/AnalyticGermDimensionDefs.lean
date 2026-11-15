import HodgeLean.Foundations.AnalyticSetDimension

/-! # Set germs, vanishing ideals and local dimension

Concrete constructions at the origin; translation of a set supplies other anchors.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Set germs with equality on a neighbourhood of the origin.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.A, analytic germs. -/
abbrev adim2_SetGerm (n : ℕ) := Filter.Germ (𝓝 (0 : Fin n → ℂ)) Prop

example : adim2_SetGerm 1 := ⊥

/-- The germ at an anchor, translated to the origin.
Source: Gunning--Rossi, III.A, germs of subsets. -/
def adim2_germ (n : ℕ) (A : Set (Fin n → ℂ)) (x : Fin n → ℂ) : adim2_SetGerm n :=
  Filter.Germ.ofFun (fun z => x + z ∈ A)

example : adim2_germ 1 ∅ 0 = ⊥ := rfl

/-- The zero set germ of one analytic function germ.
Source: Gunning--Rossi, III.A, zero germs. -/
def adim2_zero (n : ℕ) (f : AnalyticGerm n) : adim2_SetGerm n :=
  f.val.map (· = 0)

example : adim2_zero 1 0 = ⊤ := by
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun _ => propext (by simp))

/-- Analytic functions vanishing along a set germ, with the usual ideal operations.
Source: Gunning--Rossi, III.A, the ideal of a set germ. -/
def adim2_ideal (n : ℕ) (S : adim2_SetGerm n) : Ideal (AnalyticGerm n) where
  carrier := {f | S ≤ adim2_zero n f}
  zero_mem' := by
    induction S using Filter.Germ.inductionOn with | h s =>
      exact Filter.Eventually.of_forall (fun _ _ => rfl)
  add_mem' := by
    intro f g hf hg
    obtain ⟨f, hf', ef⟩ := f.property
    obtain ⟨g, hg', eg⟩ := g.property
    change S ≤ Filter.Germ.map (· = 0) (_ + _)
    change S ≤ Filter.Germ.map (· = 0) _ at hf hg
    rw [← ef] at hf
    rw [← eg] at hg
    rw [← ef, ← eg]
    induction S using Filter.Germ.inductionOn with | h s =>
      change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), s z → f z + g z = 0
      filter_upwards [hf, hg] with z hz hz' hs
      have h : f z = 0 := hz hs
      have h' : g z = 0 := hz' hs
      simp only [h, h', zero_add]
  smul_mem' := by
    intro a f hf
    obtain ⟨a, ha, ea⟩ := a.property
    obtain ⟨f, hf', ef⟩ := f.property
    change S ≤ Filter.Germ.map (· = 0) (_ * _)
    change S ≤ Filter.Germ.map (· = 0) _ at hf
    rw [← ef] at hf
    rw [← ea, ← ef]
    induction S using Filter.Germ.inductionOn with | h s =>
      change ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), s z → a z * f z = 0
      filter_upwards [hf] with z hz hs
      have h : f z = 0 := hz hs
      simp only [h, mul_zero]

example : (1 : AnalyticGerm 1) ∈ adim2_ideal 1 ⊥ := (bot_le : (⊥ : adim2_SetGerm 1) ≤ adim2_zero 1 1)

/-- A finite generating set chosen using the established Noetherian germ theorem.
Source: Gunning--Rossi, II.B, Noetherianity of the analytic local ring. -/
def adim2_generators (n : ℕ) (I : Ideal (AnalyticGerm n)) : Finset (AnalyticGerm n) :=
  ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) I).choose

example : Finset (AnalyticGerm 1) := adim2_generators 1 ⊥

/-- The common zero germ of a finite generating set of an ideal.
Source: Gunning--Rossi, III.A, zero germ of an ideal. -/
def adim2_zeroSet (n : ℕ) (I : Ideal (AnalyticGerm n)) : adim2_SetGerm n :=
  (adim2_generators n I).inf (adim2_zero n)

example : adim2_SetGerm 1 := adim2_zeroSet 1 (Ideal.span {(1 : AnalyticGerm 1)})

/-- Local dimension as the Krull dimension of the reduced analytic local ring.
The empty germ has dimension bottom, retained rather than truncated to zero.
Source: de Jong--Pfister, Local Analytic Geometry, local analytic algebras and dimension. -/
def adim2_dimension (n : ℕ) (S : adim2_SetGerm n) : WithBot ℕ∞ :=
  ringKrullDim (AnalyticGerm n ⧸ adim2_ideal n S)

example : adim2_dimension 1 ⊥ =
    ringKrullDim (AnalyticGerm 1 ⧸ adim2_ideal 1 ⊥) := rfl

end HodgeLean.Foundations
