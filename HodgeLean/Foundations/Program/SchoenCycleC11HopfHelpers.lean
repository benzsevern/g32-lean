import HodgeLean.Foundations.Program.SchoenCycleC11SphereHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11IntervalHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Metric Topology
namespace HodgeLean.Foundations.Program

/-- Unit complex scalars act continuously on the actual coordinate sphere.
Source: Mathlib, norm_smul and Continuous.smul. -/
def s2e_c11_hopfScalarAction (k : ℕ) :
    C(sphere (0 : ℂ) 1 ×
      sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1,
      sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1) where
  toFun z := ⟨(z.1 : ℂ) • z.2.val, by
    rw [mem_sphere, dist_zero_right, norm_smul]
    have h₁ : ‖(z.1 : ℂ)‖ = 1 := by simpa using z.1.property
    have h₂ : ‖z.2.val‖ = 1 := by simpa using z.2.property
    rw [h₁, h₂, one_mul]⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- Unit scalar multiplication preserves the actual Hopf projection.
Source: Mathlib, Projectivization.mk_eq_mk_iff'. -/
theorem s2e_c11_hopfScalarAction_projection (k : ℕ)
    (a : sphere (0 : ℂ) 1)
    (v : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1) :
    AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization
      (s2e_c11_hopfScalarAction k (a, v)) =
    AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨a.val, rfl⟩

/-- Two unit representatives of one projective point differ by a unit complex scalar.
Source: Mathlib, Projectivization.mk_eq_mk_iff' and norm_smul. -/
theorem s2e_c11_hopf_fibre_scalar (k : ℕ)
    (v w : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (h : AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w =
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v) :
    ∃ a : sphere (0 : ℂ) 1, s2e_c11_hopfScalarAction k (a, v) = w := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hv : ‖v.val‖ = 1 := by simpa using v.property
  have hw : ‖w.val‖ = 1 := by simpa using w.property
  have hn : ‖a‖ = 1 := by
    have he := congrArg norm ha
    rw [norm_smul, hv, hw, mul_one] at he
    exact he
  refine ⟨⟨a, by simpa using hn⟩, ?_⟩
  exact Subtype.ext ha

/-- Hopf fibres have paths between every pair of their unit representatives.
Source: Mathlib, isPathConnected_sphere in real dimension two. -/
theorem s2e_c11_hopf_fibre_path (k : ℕ)
    (v w : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (h : AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w =
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v) :
    ∃ δ : Path v w, ∀ t,
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization (δ t) =
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v := by
  obtain ⟨a, ha⟩ := s2e_c11_hopf_fibre_scalar k v w h
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  letI : PathConnectedSpace (sphere (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hr _ zero_le_one)
  let e : sphere (0 : ℂ) 1 := ⟨1, by simp⟩
  let α : Path e a := PathConnectedSpace.somePath e a
  refine ⟨{ toFun := fun t => s2e_c11_hopfScalarAction k (α t, v)
            continuous_toFun := (s2e_c11_hopfScalarAction k).continuous.comp
              (α.continuous.prodMk continuous_const)
            source' := ?_
            target' := ?_ }, ?_⟩
  · rw [α.source]
    apply Subtype.ext
    exact one_smul ℂ v.val
  · rw [α.target]
    exact ha
  · intro t
    exact s2e_c11_hopfScalarAction_projection k (α t) v

/-- A continuous lift of a Hopf loop can be corrected to a based loop using its circle fibre.
Source: Hatcher, Algebraic Topology, Hopf bundle endpoint correction. -/
theorem s2e_c11_hopf_correct_endpoint (k : ℕ)
    (v : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (γ : Path (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v)
      (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v))
    (α : C(unitInterval,
      sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1))
    (h₀ : α 0 = v)
    (hα : ∀ t, AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization (α t) = γ t) :
    ∃ δ : Path v v, (δ.map
      AlgebraicGeometry.ComplexProjectiveSpace.continuous_sphereToProjectivization).Homotopic γ := by
  let p : Path v (α 1) := ⟨α, h₀, rfl⟩
  have h₁ : AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization (α 1) =
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v :=
    (hα 1).trans γ.target
  obtain ⟨q, hq⟩ := s2e_c11_hopf_fibre_path k (α 1) v h₁.symm
  refine ⟨p.trans q, ?_⟩
  have he : (p.trans q).map
      AlgebraicGeometry.ComplexProjectiveSpace.continuous_sphereToProjectivization =
      γ.trans (Path.refl _) := by
    ext t
    change AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization
      ((p.trans q) t) = (γ.trans (Path.refl _)) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hα _
    · exact (hq _).trans h₁
  rw [he]
  exact ⟨Path.Homotopy.transRefl γ⟩

/-- A nonzero coordinate reads the unique scalar between two unit representatives.
Source: Mathlib, Projectivization.mk_eq_mk_iff' and division in the complex field. -/
theorem s2e_c11_hopf_coordinate_reconstruction (k : ℕ) (i : Fin (k + 1))
    (v w : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (hi : v.val i ≠ 0)
    (h : AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w =
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v) :
    (w.val i / v.val i) • v.val = w.val := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have he : a * v.val i = w.val i := congrFun ha i
  have hd : w.val i / v.val i = a := (div_eq_iff hi).mpr he.symm
  rw [hd]
  exact ha

/-- The coordinate quotient between unit representatives has unit norm.
Source: Mathlib, norm_smul and the unit sphere norm equation. -/
theorem s2e_c11_hopf_coordinate_norm (k : ℕ) (i : Fin (k + 1))
    (v w : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (hi : v.val i ≠ 0)
    (h : AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w =
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v) :
    ‖w.val i / v.val i‖ = 1 := by
  have he := congrArg norm (s2e_c11_hopf_coordinate_reconstruction k i v w hi h)
  have hv : ‖v.val‖ = 1 := by simpa using v.property
  have hw : ‖w.val‖ = 1 := by simpa using w.property
  simpa only [norm_smul, hv, hw, mul_one] using he

/-- The selected representative has a nonzero distinguished chart coordinate.
Source: Mathlib, projective chart membership and the sphere section projection identity. -/
theorem s2e_c11_hopf_section_coordinate_ne_zero (k : ℕ) (i : Fin (k + 1))
    (p : {p : Projectivization ℂ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) //
      s2e_c11_normalizedCoordinates i p i ≠ 0}) :
    (s2e_c11_projectiveChartSphereSection k i p).val i ≠ 0 := by
  apply (s2e_c11_normalizedCoordinates_nonzero i _
    (s2e_c11_unitSphere_ne_zero (s2e_c11_projectiveChartSphereSection k i p))).mp
  change s2e_c11_normalizedCoordinates i
    (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization
      (s2e_c11_projectiveChartSphereSection k i p)) i ≠ 0
  rw [s2e_c11_projectiveChartSphereSection_projection]
  exact p.property

/-- The phase coordinate on a Hopf chart is a continuous unit complex scalar.
Source: Hatcher, Algebraic Topology, Hopf bundle local trivializations. -/
def s2e_c11_hopfChartCoordinate (k : ℕ) (i : Fin (k + 1)) :
    C({w : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1 //
      s2e_c11_normalizedCoordinates i
        (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w) i ≠ 0},
      sphere (0 : ℂ) 1) where
  toFun w := ⟨w.val.val i /
    (s2e_c11_projectiveChartSphereSection k i ⟨_, w.property⟩).val i, by
      rw [mem_sphere, dist_zero_right]
      apply s2e_c11_hopf_coordinate_norm
      · exact s2e_c11_hopf_section_coordinate_ne_zero k i _
      · exact (s2e_c11_projectiveChartSphereSection_projection k i
          ⟨AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w.val,
            w.property⟩).symm⟩
  continuous_toFun := by
    let P := {p : Projectivization ℂ
      (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) //
        s2e_c11_normalizedCoordinates i p i ≠ 0}
    have hb : Continuous (fun w : {w : sphere
        (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1 //
        s2e_c11_normalizedCoordinates i
          (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w) i ≠ 0} =>
        (⟨AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization w.val,
          w.property⟩ : P)) :=
      (AlgebraicGeometry.ComplexProjectiveSpace.continuous_sphereToProjectivization.comp
        continuous_subtype_val).subtype_mk _
    apply Continuous.subtype_mk
    exact ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val)).div
      ((continuous_apply i).comp (continuous_subtype_val.comp
        ((s2e_c11_projectiveChartSphereSection_continuous k i).comp hb)))
      (fun w => s2e_c11_hopf_section_coordinate_ne_zero k i _)

/-- Every sphere point over a projective chart extends to a section on that chart.
Source: Hatcher, Algebraic Topology, Hopf bundle local sections and unit scalar action. -/
theorem s2e_c11_hopf_chart_section_through (k : ℕ) (i : Fin (k + 1))
    (e : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (he : s2e_c11_normalizedCoordinates i
      (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization e) i ≠ 0) :
    ∃ s : Projectivization ℂ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) →
        sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1,
      ContinuousOn s {p | s2e_c11_normalizedCoordinates i p i ≠ 0} ∧
      Set.EqOn (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization ∘ s) id
        {p | s2e_c11_normalizedCoordinates i p i ≠ 0} ∧
      s (AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization e) = e := by
  classical
  let U := {p : Projectivization ℂ
    (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) |
    s2e_c11_normalizedCoordinates i p i ≠ 0}
  let a := s2e_c11_hopfChartCoordinate k i ⟨e, he⟩
  let σ : C(U, sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1) :=
    ⟨fun p => s2e_c11_hopfScalarAction k (a, s2e_c11_projectiveChartSphereSection k i p),
      (s2e_c11_hopfScalarAction k).continuous.comp
        (continuous_const.prodMk (s2e_c11_projectiveChartSphereSection_continuous k i))⟩
  let s := fun p => if hp : p ∈ U then σ ⟨p, hp⟩ else e
  refine ⟨s, ?_, ?_, ?_⟩
  · apply continuousOn_iff_continuous_restrict.mpr
    convert σ.continuous using 1
    funext p
    exact dif_pos p.property
  · intro p hp
    change AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization (s p) = p
    dsimp only [s]
    rw [dif_pos hp]
    exact (s2e_c11_hopfScalarAction_projection k a _).trans
      (s2e_c11_projectiveChartSphereSection_projection k i ⟨p, hp⟩)
  · dsimp only [s]
    rw [dif_pos (show AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization e ∈ U from he)]
    apply Subtype.ext
    exact s2e_c11_hopf_coordinate_reconstruction k i
      (s2e_c11_projectiveChartSphereSection k i ⟨_, he⟩) e
      (s2e_c11_hopf_section_coordinate_ne_zero k i _)
      (s2e_c11_projectiveChartSphereSection_projection k i
        ⟨AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization e, he⟩).symm

/-- The normalized coordinate charts cover the actual projectivization.
Source: Hartshorne, Algebraic Geometry, I.2, standard projective affine charts. -/
theorem s2e_c11_hopf_chart_cover (k : ℕ)
    (p : Projectivization ℂ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k)) :
    ∃ i : Fin (k + 1), s2e_c11_normalizedCoordinates i p i ≠ 0 := by
  have hex : ∃ i, p.rep i ≠ 0 := by
    by_contra! h
    exact p.rep_nonzero (funext h)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  rw [← p.mk_rep]
  exact (s2e_c11_normalizedCoordinates_nonzero i p.rep p.rep_nonzero).mpr hi

/-- The actual Hopf projection lifts every continuous interval map from a prescribed initial point.
Source: Hatcher, Algebraic Topology, Hopf bundle path lifting by local sections. -/
theorem s2e_c11_hopf_path_lift (k : ℕ)
    (γ : C(unitInterval, Projectivization ℂ
      (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k)))
    (v : sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1)
    (h₀ : γ 0 = AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization v) :
    ∃ α : C(unitInterval,
      sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1),
      AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization ∘ α = γ ∧ α 0 = v := by
  apply s2e_c11_interval_lift_of_local_sections _ ?_ γ v h₀
  intro p
  obtain ⟨i, hi⟩ := s2e_c11_hopf_chart_cover k p
  exact ⟨{p | s2e_c11_normalizedCoordinates i p i ≠ 0}, hi,
    s2e_c11_normalizedChart_isOpen i, s2e_c11_hopf_chart_section_through k i⟩

end HodgeLean.Foundations.Program
