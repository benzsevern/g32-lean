import HodgeLean.Foundations.Program.TorusAlgebraizationB52Seeds
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Fourier

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_coverCharacter (l : Λ) (z : b5_V Λ F) : Circle :=
  Circle.exp (-2 * Real.pi * (b5_H Λ F hF Q (b5_lattice Λ F l) z).im)

theorem b52_coverCharacter_add (l : Λ) (z w : b5_V Λ F) :
    b52_coverCharacter Λ F hF Q l (z + w) =
      b52_coverCharacter Λ F hF Q l z * b52_coverCharacter Λ F hF Q l w := by
  unfold b52_coverCharacter
  rw [b5_H_add_right, Complex.add_im, mul_add, Circle.exp_add]

#print axioms b52_coverCharacter_add

theorem b52_coverCharacter_periodic
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ)) (l m : Λ) (z : b5_V Λ F) :
    b52_coverCharacter Λ F hF Q l (z + b5_lattice Λ F m) =
      b52_coverCharacter Λ F hF Q l z := by
  rw [b52_coverCharacter_add]
  have h : b52_coverCharacter Λ F hF Q l (b5_lattice Λ F m) = 1 := by
    unfold b52_coverCharacter
    rw [himag]
    have he : -2 * Real.pi * (Q l m : ℝ) = ((-Q l m : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [he, Circle.exp_int_mul_two_pi]
  rw [h, mul_one]

#print axioms b52_coverCharacter_periodic

theorem b52_coverCharacter_continuous (l : Λ) :
    Continuous (b52_coverCharacter Λ F hF Q l) := by
  have h : Continuous (fun z ↦ b5_H Λ F hF Q (b5_lattice Λ F l) z) := by
    simpa only [b52_H_continuousBilinear_apply] using
      (show Continuous (fun z : b5_V Λ F ↦
        b52_H_continuousBilinear Λ F hF Q (b5_lattice Λ F l) z) from
        (b52_H_continuousBilinear Λ F hF Q (b5_lattice Λ F l)).continuous)
  change Continuous (fun z ↦ Circle.exp
    (-2 * Real.pi * (b5_H Λ F hF Q (b5_lattice Λ F l) z).im))
  simpa only [Function.comp_def, Pi.mul_apply] using
    Circle.exp.continuous.comp (continuous_const.mul (Complex.continuous_im.comp h))

#print axioms b52_coverCharacter_continuous

theorem b52_H_smul_right (a : ℂ) (x y : b5_V Λ F) :
    b5_H Λ F hF Q x (a • y) = a * b5_H Λ F hF Q x y := by
  simp only [b5_H, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  ring

#print axioms b52_H_smul_right

theorem b52_coverCharacter_nontrivial
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (l : Λ) (hl : l ≠ 0) : ∃ z, b52_coverCharacter Λ F hF Q l z ≠ 1 := by
  have hl0 : b5_lattice Λ F l ≠ 0 := by
    intro hz
    exact hl (b52_lattice_injective Λ F hF (hz.trans (map_zero _).symm))
  have hh0 : b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l) ≠ 0 := by
    intro hz
    have hp := hpos (b5_lattice Λ F l) hl0
    simpa only [hz, Complex.zero_re, lt_self_iff_false] using hp
  let z := (-Complex.I /
    (2 * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l))) • b5_lattice Λ F l
  have he : b5_H Λ F hF Q (b5_lattice Λ F l) z = -Complex.I / 2 := by
    dsimp [z]
    rw [b52_H_smul_right]
    field_simp [hh0]
    <;> ring
  refine ⟨z, ?_⟩
  unfold b52_coverCharacter
  rw [he]
  have him : (-Complex.I / 2).im = -(1 / 2 : ℝ) := by norm_num
  rw [him]
  have hr : -2 * Real.pi * -(1 / 2 : ℝ) = Real.pi := by ring
  rw [hr]
  exact Circle.exp_pi_ne_one

#print axioms b52_coverCharacter_nontrivial

def b52_characterOnQuotientSpace (l : Λ) :
    ((ℂ ⊗[ℤ] Λ) ⧸ F) →+ Additive Circle where
  toFun w := Additive.ofMul (b52_coverCharacter Λ F hF Q l (b2_coord _ w))
  map_zero' := by
    change b52_coverCharacter Λ F hF Q l (b2_coord _ 0) = 1
    simp [b52_coverCharacter, b5_H]
  map_add' := by
    intro x y
    change b52_coverCharacter Λ F hF Q l (b2_coord _ (x + y)) =
      b52_coverCharacter Λ F hF Q l (b2_coord _ x) *
        b52_coverCharacter Λ F hF Q l (b2_coord _ y)
    rw [map_add, b52_coverCharacter_add]

#print axioms b52_characterOnQuotientSpace

def b52_torusCharacter
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ)) (l : Λ) : b2_torus Λ F →+ Additive Circle :=
  QuotientAddGroup.lift (b2_latticeMap Λ F).range
    (b52_characterOnQuotientSpace Λ F hF Q l) (by
      rintro w ⟨m, rfl⟩
      change b52_coverCharacter Λ F hF Q l (b5_lattice Λ F m) = 1
      have h := b52_coverCharacter_periodic Λ F hF Q himag l m 0
      simpa [b52_coverCharacter, b5_H] using h)

#print axioms b52_torusCharacter

theorem b52_torusCharacter_continuous
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ)) (l : Λ) : Continuous (b52_torusCharacter Λ F hF Q himag l) := by
  apply (QuotientAddGroup.isQuotientMap_mk (b2_latticeMap Λ F).range).continuous_iff.mpr
  change Continuous (fun w : (ℂ ⊗[ℤ] Λ) ⧸ F ↦
    Additive.ofMul (b52_coverCharacter Λ F hF Q l (b2_coord _ w)))
  exact (b52_coverCharacter_continuous Λ F hF Q l).comp
    (b2_coordHomeomorph Λ F).continuous

#print axioms b52_torusCharacter_continuous

theorem b52_torusCharacter_nontrivial
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ))
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (l : Λ) (hl : l ≠ 0) : ∃ x, b52_torusCharacter Λ F hF Q himag l x ≠ 0 := by
  obtain ⟨z, hz⟩ := b52_coverCharacter_nontrivial Λ F hF Q hpos l hl
  refine ⟨QuotientAddGroup.mk ((b2_coord _).symm z), ?_⟩
  change b52_coverCharacter Λ F hF Q l (b2_coord _ ((b2_coord _).symm z)) ≠ 1
  simpa only [LinearEquiv.apply_symm_apply] using hz

#print axioms b52_torusCharacter_nontrivial

theorem b52_torus_character_series_nonzero
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ))
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (c : Λ → ℂ) (hc : Summable (fun l ↦ ‖c l‖)) (hc0 : c 0 ≠ 0) :
    ∃ x : b2_torus Λ F, (∑' l : Λ, c l *
      (↑(Additive.toMul (b52_torusCharacter Λ F hF Q himag l x)) : ℂ)) ≠ 0 := by
  haveI := b2_latticeMap_discrete F hF
  haveI := b2_torus_t2Space F
  haveI := b2_torus_compactSpace F hF
  letI : MeasurableSpace (b2_torus Λ F) := borel (b2_torus Λ F)
  letI : BorelSpace (b2_torus Λ F) := ⟨rfl⟩
  haveI : Countable Λ := (Module.finBasis ℤ Λ).repr.injective.countable
  obtain ⟨μ, hleft, hprob⟩ := b52_probability_invariant_measure (b2_torus Λ F)
  haveI := hleft
  haveI := hprob
  refine b52_character_series_nonzero μ
    (fun l x ↦ (↑(Additive.toMul (b52_torusCharacter Λ F hF Q himag l x)) : ℂ))
    ?_ ?_ ?_ ?_ ?_ c hc hc0
  · intro l x y
    rw [map_add]
    rfl
  · intro x
    induction x using Quotient.inductionOn with
    | h w =>
      change (b52_coverCharacter Λ F hF Q 0 (b2_coord _ w) : ℂ) = 1
      simp [b52_coverCharacter, b5_H]
  · intro l hl
    obtain ⟨x, hx⟩ := b52_torusCharacter_nontrivial Λ F hF Q himag hpos l hl
    exact ⟨x, fun h ↦ hx (Subtype.ext h)⟩
  · intro l
    have hcont : Continuous (fun x : b2_torus Λ F ↦
        (↑(Additive.toMul (b52_torusCharacter Λ F hF Q himag l x)) : ℂ)) :=
      continuous_subtype_val.comp (b52_torusCharacter_continuous Λ F hF Q himag l)
    exact (MeasureTheory.integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ by simp))
  · intro l x
    exact (Additive.toMul (b52_torusCharacter Λ F hF Q himag l x)).norm_coe

#print axioms b52_torus_character_series_nonzero

end HodgeLean.Foundations.Program
