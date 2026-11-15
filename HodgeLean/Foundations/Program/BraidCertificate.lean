import HodgeLean.Foundations.Program.BraidCertificateProofs

/-! # Braid certificate: arithmetic replay and interval bounds

Explicit B65-BRAIDCERT data give the selected column component, track geometry
and normalization interval bounds. The geometric marking statements are set aside
in docs/specs/BraidCertificate.md.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The literal cut words agree with both independently exported integral matrix tuples.
Source: B65-BRAIDCERT JSON T_init and T_final; checker E–F. -/
theorem b65b_literal_matrices  :
    (∀ i, b4b_toMatrix (b65b_initial i) = b65b_decode (b65b_initialIntegral i)) ∧
    (∀ i, b4b_toMatrix (b65b_final i) = b65b_decode (b65b_finalIntegral i)) :=
  b65b_literal_matrices_aux

example :
    (∀ i, b4b_toMatrix (b65b_initial i) = b65b_decode (b65b_initialIntegral i)) ∧
    (∀ i, b4b_toMatrix (b65b_final i) = b65b_decode (b65b_finalIntegral i)) :=
  b65b_literal_matrices

/-- The 86 letters yield r₂ inverse times T times r₂, in the orientation of b4_conjTuple.
Source: B65-BRAIDCERT REPORT §1.5; checker G. -/
theorem b65b_replay  :
    b65s_word b65b_word b65s_columnRoot =
      b4_conjTuple (b4b_generators 1)⁻¹ b65b_final ∧
    ∀ i, b4b_toMatrix (b65s_word b65b_word b65s_columnRoot i) =
      b4b_toMatrix ((b4b_generators 1)⁻¹) *
        b65b_decode (b65b_finalIntegral i) * b4b_toMatrix (b4b_generators 1) :=
  b65b_replay_aux

example :
    b65s_word b65b_word b65s_columnRoot =
      b4_conjTuple (b4b_generators 1)⁻¹ b65b_final ∧
    ∀ i, b4b_toMatrix (b65s_word b65b_word b65s_columnRoot i) =
      b4b_toMatrix ((b4b_generators 1)⁻¹) *
        b65b_decode (b65b_finalIntegral i) * b4b_toMatrix (b4b_generators 1) :=
  b65b_replay

/-- The two positive moves take the initial tuple to the literal final tuple.
Source: B65-BRAIDCERT JSON path_moves; checker F. -/
theorem b65b_path_replay  :
    b65s_word b65b_pathWord b65b_initial = b65b_final :=
  b65b_path_replay_aux

example :
    b65s_word b65b_pathWord b65b_initial = b65b_final :=
  b65b_path_replay

/-- The literal final tuple belongs to the selected column component.
Source: B65-BRAIDCERT REPORT §1.5; b65s_word_orbit and b4_conjTuple. -/
theorem b65b_component  :
    b4_SameComponent b65s_columnRoot b65b_final :=
  b65b_component_aux

example :
    b4_SameComponent b65s_columnRoot b65b_final :=
  b65b_component

/-- The straight path has no collisions and precisely the two recorded angular events.
Source: B65-BRAIDCERT checker F; JSON events and path.vertices. -/
theorem b65b_path_geometry  :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (b65b_track t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, ‖b65b_track t i - (-11/2 : ℂ)‖ < 10) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i j : Fin 12, i < j →
      (((b65b_track t i - (-11/2 + 10 * Complex.I)) *
          star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
        (i = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
        (i = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) :=
  b65b_path_geometry_aux

example :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (b65b_track t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, ‖b65b_track t i - (-11/2 : ℂ)‖ < 10) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i j : Fin 12, i < j →
      (((b65b_track t i - (-11/2 + 10 * Complex.I)) *
          star (b65b_track t j - (-11/2 + 10 * Complex.I))).im = 0 ↔
        (i = 8 ∧ j = 10 ∧ t = (63109263/2063109263 : ℝ)) ∨
        (i = 9 ∧ j = 10 ∧ t = (48671253/298671253 : ℝ))) :=
  b65b_path_geometry

/-- The exported rational enclosure corners lie in the discs, whose cones are separated.
Source: B65-BRAIDCERT checker B–C, corner inequalities and coneok. -/
theorem b65b_rational_enclosures  :
    (∀ i : Fin 12, 0 < b65b_radius i ∧ b65b_radius i ≤ 1/4) ∧
    (∀ i : Fin 12, ∀ a b : Fin 2,
      (b65b_enclosure i ⟨a.val, by omega⟩ - (b65b_vertex0 i).1)^2 +
        (b65b_enclosure i ⟨b.val + 2, by omega⟩ - (b65b_vertex0 i).2)^2 < (b65b_radius i)^2) ∧
    ∀ i j : Fin 12, i < j →
      0 < b65b_dot i j ∧
      (b65b_cross i j)^2 > (b65b_radius i)^2 * b65b_dot j j +
        (b65b_radius j)^2 * b65b_dot i i +
        b65b_radius i * b65b_radius j * (b65b_dot i i + b65b_dot j j) :=
  b65b_rational_enclosures_aux

example :
    (∀ i : Fin 12, 0 < b65b_radius i ∧ b65b_radius i ≤ 1/4) ∧
    (∀ i : Fin 12, ∀ a b : Fin 2,
      (b65b_enclosure i ⟨a.val, by omega⟩ - (b65b_vertex0 i).1)^2 +
        (b65b_enclosure i ⟨b.val + 2, by omega⟩ - (b65b_vertex0 i).2)^2 < (b65b_radius i)^2) ∧
    ∀ i j : Fin 12, i < j →
      0 < b65b_dot i j ∧
      (b65b_cross i j)^2 > (b65b_radius i)^2 * b65b_dot j j +
        (b65b_radius j)^2 * b65b_dot i i +
        b65b_radius i * b65b_radius j * (b65b_dot i i + b65b_dot j j) :=
  b65b_rational_enclosures

/-- Every box point and both real normalization parameters satisfy the certified enclosure.
Source: B65-BRAIDCERT checker B, Nint and cinv; checker B–C corner inequalities. -/
theorem b65b_normalization_enclosure :
    ∀ (k : Fin 12) (z : ℂ) (a b : ℝ),
      |z.re - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ) →
      |z.im - ((b65b_boxCentre k).2 : ℝ)| ≤ (1/10000 : ℝ) →
      |a - ((b65b_boxCentre 0).1 : ℝ)| ≤ (1/10000 : ℝ) →
      |b - ((b65b_boxCentre 6).1 : ℝ)| ≤ (1/10000 : ℝ) →
      z * ((b : ℂ) - a) ≠ 0 ∧
      (b65s_normalize a b z).re ∈ Set.Icc
        (b65b_enclosure (b65b_boxIndex k) 0 : ℝ)
        (b65b_enclosure (b65b_boxIndex k) 1 : ℝ) ∧
      (b65s_normalize a b z).im ∈ Set.Icc
        (b65b_enclosure (b65b_boxIndex k) 2 : ℝ)
        (b65b_enclosure (b65b_boxIndex k) 3 : ℝ) ∧
      ‖b65s_normalize a b z - b65b_track 0 (b65b_boxIndex k)‖ <
        (b65b_radius (b65b_boxIndex k) : ℝ) :=
  b65b_normalization_enclosure_aux

example :
    ∀ (k : Fin 12) (z : ℂ) (a b : ℝ),
      |z.re - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ) →
      |z.im - ((b65b_boxCentre k).2 : ℝ)| ≤ (1/10000 : ℝ) →
      |a - ((b65b_boxCentre 0).1 : ℝ)| ≤ (1/10000 : ℝ) →
      |b - ((b65b_boxCentre 6).1 : ℝ)| ≤ (1/10000 : ℝ) →
      z * ((b : ℂ) - a) ≠ 0 ∧
      (b65s_normalize a b z).re ∈ Set.Icc
        (b65b_enclosure (b65b_boxIndex k) 0 : ℝ)
        (b65b_enclosure (b65b_boxIndex k) 1 : ℝ) ∧
      (b65s_normalize a b z).im ∈ Set.Icc
        (b65b_enclosure (b65b_boxIndex k) 2 : ℝ)
        (b65b_enclosure (b65b_boxIndex k) 3 : ℝ) ∧
      ‖b65s_normalize a b z - b65b_track 0 (b65b_boxIndex k)‖ <
        (b65b_radius (b65b_boxIndex k) : ℝ) :=
  b65b_normalization_enclosure

/-- A continuous normalized parameter curve has the two required period-map path types.
Source: G32DominanceDefs, g32r_PeriodMap.curve_cont and curve_zero. -/
example (c : C(ℂ, b6_chart)) :
    ContinuousAt (fun θ ↦ (c θ).val) 0 ∧
      (c 0).val ∈ b6t_polydisc (c 0).val := by
  exact ⟨(continuous_subtype_val.comp c.continuous).continuousAt,
    (b6t_polydisc_neighbourhood (c 0).val (c 0).property).1⟩

end HodgeLean.Foundations.Program
