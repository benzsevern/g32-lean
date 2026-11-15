import HodgeLean.Foundations.Program.SchoenTowerFoundB2Defs
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldRescaling

/-! # Rees chart maps into the retained original field
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual Rees fraction algebra maps into the original field and generates the same coefficient subfield as the original ring.
Source: Mathlib, IsLocalization.Away.lift and Subfield.closure_le. -/
theorem s2v_i2a_rees_chart_original_field
    {R K : Type} [CommRing R] [Field K] (I : Ideal R)
    (φ : R →+* K) (x : R) (hx : φ x ≠ 0) :
    ∃ ψ : s2t_reesChart I x →+* K,
      ψ.comp (algebraMap R (s2t_reesChart I x)) = φ ∧
      Subfield.closure (Set.range ψ) = Subfield.closure (Set.range φ) := by
  let F := Subfield.closure (Set.range φ)
  let φF : R →+* F := φ.codRestrict F.toSubring (fun r => Subfield.subset_closure ⟨r, rfl⟩)
  have hunit : IsUnit (φF x) := by
    apply isUnit_iff_ne_zero.mpr
    intro H
    exact hx (congrArg Subtype.val H)
  let τ : Localization.Away x →+* F := IsLocalization.Away.lift x hunit
  let ψ : s2t_reesChart I x →+* K :=
    F.subtype.comp (τ.comp (s2t_reesChart I x).val.toRingHom)
  have hψ (r : R) : ψ (algebraMap R (s2t_reesChart I x) r) = φ r := by
    change (τ (algebraMap R (Localization.Away x) r) : K) = φ r
    rw [IsLocalization.Away.lift_eq]
    rfl
  refine ⟨ψ, RingHom.ext hψ, le_antisymm ?_ ?_⟩
  · apply Subfield.closure_le.mpr
    rintro z ⟨a, rfl⟩
    exact (τ a.val).property
  · apply Subfield.closure_le.mpr
    rintro z ⟨r, rfl⟩
    exact Subfield.subset_closure ⟨algebraMap R (s2t_reesChart I x) r, hψ r⟩

/-- The actual fraction generator y/x in the specified Rees chart.
Source: Mathlib, Algebra.adjoin and IsLocalization.Away.invSelf. -/
def s2v_i2a_reesFraction {R : Type} [CommRing R] (I : Ideal R) (x : R) (y : I) :
    s2t_reesChart I x :=
  ⟨algebraMap R (Localization.Away x) y.val * IsLocalization.Away.invSelf x,
    Algebra.subset_adjoin (Set.mem_range_self y)⟩

example {R : Type} [CommRing R] (I : Ideal R) (x : R) (y : I) :
    s2v_i2a_reesFraction I x y * algebraMap R (s2t_reesChart I x) x =
      algebraMap R (s2t_reesChart I x) y.val := by
  apply Subtype.ext
  change (algebraMap R (Localization.Away x) y.val * IsLocalization.Away.invSelf x) *
    algebraMap R (Localization.Away x) x = _
  rw [mul_right_comm, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  rfl

/-- Every compatible original-field chart map sends the actual Rees ratio to the corresponding field quotient.
Source: Mathlib, IsLocalization.Away.mul_invSelf and field division cancellation. -/
theorem s2v_i2a_reesFraction_field_value
    {R K : Type} [CommRing R] [Field K] (I : Ideal R) (x : R) (y : I)
    (φ : R →+* K) (hx : φ x ≠ 0) (ψ : s2t_reesChart I x →+* K)
    (hψ : ψ.comp (algebraMap R (s2t_reesChart I x)) = φ) :
    ψ (s2v_i2a_reesFraction I x y) = φ y.val / φ x := by
  have hratio : s2v_i2a_reesFraction I x y * algebraMap R (s2t_reesChart I x) x =
      algebraMap R (s2t_reesChart I x) y.val := by
    apply Subtype.ext
    change (algebraMap R (Localization.Away x) y.val * IsLocalization.Away.invSelf x) *
      algebraMap R (Localization.Away x) x = _
    rw [mul_right_comm, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    rfl
  apply (eq_div_iff hx).mpr
  have H := congrArg ψ hratio
  rw [map_mul] at H
  have hbase (r : R) : ψ (algebraMap R (s2t_reesChart I x) r) = φ r := RingHom.congr_fun hψ r
  rw [hbase, hbase] at H
  exact H

/-- Dividing the original generator by the exceptional parameter still generates the original field over the actual Rees chart coefficients.
Source: Mathlib, Subfield.closure_union and s2v_i2a_rescaled_generator_field. -/
theorem s2v_i2a_rees_chart_rescaled_field
    {R K : Type} [CommRing R] [Field K] (I : Ideal R)
    (φ : R →+* K) (x : R) (hx : φ x ≠ 0) (v : K)
    (hgen : Subfield.closure (Set.range φ ∪ {v}) = ⊤) :
    ∃ ψ : s2t_reesChart I x →+* K,
      ψ.comp (algebraMap R (s2t_reesChart I x)) = φ ∧
      Subfield.closure (Set.range ψ ∪ {v / φ x}) = ⊤ := by
  obtain ⟨ψ, hψ, hfields⟩ := s2v_i2a_rees_chart_original_field I φ x hx
  refine ⟨ψ, hψ, ?_⟩
  calc
    Subfield.closure (Set.range ψ ∪ {v / φ x}) =
        Subfield.closure (Set.range φ ∪ {v / φ x}) := by
      rw [Subfield.closure_union, hfields, ← Subfield.closure_union]
    _ = Subfield.closure (Set.range φ ∪ {v}) := s2v_i2a_rescaled_generator_field φ v x hx
    _ = ⊤ := hgen

end HodgeLean.Foundations.Program
