import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import HodgeLean.Foundations.Program.SchoenCycleC11HomotopyHelpers
import Mathlib.Analysis.Normed.Module.Connected

/-! # Normalized projective coordinates
Explicit coordinate constructions for the projective topology argument.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Scale a representative by the inverse of its specified coordinate. -/
def s2e_c11_normalized_vector {k : ℕ} (i : Fin (k + 1))
    (p : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :
    ComplexProjectiveSpace.CoordinateSpace k :=
  Projectivization.lift (K := ℂ) (V := ComplexProjectiveSpace.CoordinateSpace k) (fun v ↦ (v.1 i)⁻¹ • v.1) (by
    intro a b t hab
    have ht : t ≠ 0 := by
      intro h
      apply a.2
      simpa only [h, zero_smul] using hab
    ext j
    have hi := congrArg (fun v ↦ v i) hab
    have hj := congrArg (fun v ↦ v j) hab
    change a.1 i = t * b.1 i at hi
    change a.1 j = t * b.1 j at hj
    change (a.1 i)⁻¹ * a.1 j = (b.1 i)⁻¹ * b.1 j
    rw [hi, hj, mul_inv_rev]
    calc
      ((b.1 i)⁻¹ * t⁻¹) * (t * b.1 j) = (b.1 i)⁻¹ * (t⁻¹ * t) * b.1 j := by ring
      _ = (b.1 i)⁻¹ * b.1 j := by rw [inv_mul_cancel₀ ht, mul_one]) p

/-- Normalization uses the actual coordinates of every representative.
Source: Mathlib, Projectivization.lift_mk. -/
theorem s2e_c11_normalized_vector_mk {k : ℕ} (i : Fin (k + 1))
    (v : ComplexProjectiveSpace.CoordinateSpace k) (hv : v ≠ 0) :
    s2e_c11_normalized_vector i (Projectivization.mk ℂ v hv) = (v i)⁻¹ • v := rfl

/-- The coordinate chart on which normalization has specified coordinate one. -/
def s2e_c11_coordinate_chart {k : ℕ} (i : Fin (k + 1)) :
    Set (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :=
  {p | s2e_c11_normalized_vector i p i = 1}

/-- Chart membership is exactly nonvanishing of the specified homogeneous coordinate.
Source: Hartshorne, Algebraic Geometry, I.2, standard projective charts. -/
theorem s2e_c11_mk_mem_coordinate_chart {k : ℕ} (i : Fin (k + 1))
    (v : ComplexProjectiveSpace.CoordinateSpace k) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ s2e_c11_coordinate_chart i ↔ v i ≠ 0 := by
  change (v i)⁻¹ * v i = 1 ↔ v i ≠ 0
  constructor
  · intro h hz
    rw [hz, inv_zero, zero_mul] at h
    exact zero_ne_one h
  · exact inv_mul_cancel₀

/-- Every normalized coordinate chart is open for the actual quotient topology.
Source: Mathlib, quotient topology and continuity of coordinate evaluation. -/
theorem s2e_c11_isOpen_coordinate_chart {k : ℕ} (i : Fin (k + 1)) :
    IsOpen (s2e_c11_coordinate_chart i) := by
  apply isOpen_coinduced.mpr
  change IsOpen ((Quotient.mk (projectivizationSetoid ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :
    {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} →
      Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) ⁻¹'
      s2e_c11_coordinate_chart i)
  have heq : (Quotient.mk (projectivizationSetoid ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :
    {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} →
      Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) ⁻¹'
      s2e_c11_coordinate_chart i = {v | v.1 i ≠ 0} := by
    ext v
    exact s2e_c11_mk_mem_coordinate_chart i v.1 v.2
  rw [heq]
  exact isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const

/-- Normalized coordinates vary continuously throughout their chart.
Source: Mathlib, IsQuotientMap.restrictPreimage_isOpen and continuity of inversion away from zero. -/
theorem s2e_c11_continuous_normalized_vector_chart {k : ℕ} (i : Fin (k + 1)) :
    Continuous (fun p : s2e_c11_coordinate_chart i ↦ s2e_c11_normalized_vector i p.1) := by
  let q : {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} →
      Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) :=
    Quotient.mk (projectivizationSetoid ℂ (ComplexProjectiveSpace.CoordinateSpace k))
  have hq : Topology.IsQuotientMap ((s2e_c11_coordinate_chart i).restrictPreimage q) :=
    (isQuotientMap_quotient_mk' (s := projectivizationSetoid ℂ
      (ComplexProjectiveSpace.CoordinateSpace k))).restrictPreimage_isOpen
        (s2e_c11_isOpen_coordinate_chart i)
  apply hq.continuous_iff.mpr
  change Continuous (fun v : q ⁻¹' s2e_c11_coordinate_chart i ↦ (v.1.1 i)⁻¹ • v.1.1)
  have hv : Continuous (fun v : q ⁻¹' s2e_c11_coordinate_chart i ↦ v.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hi : Continuous (fun v : q ⁻¹' s2e_c11_coordinate_chart i ↦ v.1.1 i) :=
    (continuous_apply i).comp hv
  exact (hi.inv₀ (fun v ↦ (s2e_c11_mk_mem_coordinate_chart i v.1.1 v.1.2).mp v.2)).smul hv

/-- A normalized representative in its chart has a coordinate equal to one and is nonzero.
Source: Hartshorne, Algebraic Geometry, I.2, standard projective coordinates. -/
theorem s2e_c11_normalized_vector_ne_zero {k : ℕ} (i : Fin (k + 1))
    (p : s2e_c11_coordinate_chart i) : s2e_c11_normalized_vector i p.1 ≠ 0 := by
  intro h
  have hi := p.2
  change s2e_c11_normalized_vector i p.1 i = 1 at hi
  rw [h] at hi
  exact zero_ne_one hi

/-- Normalizing a nonzero representative preserves its projective point.
Source: Mathlib, Projectivization.mk_eq_mk_iff'. -/
theorem s2e_c11_normalized_vector_projective {k : ℕ} (i : Fin (k + 1))
    (p : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k))
    (hn : s2e_c11_normalized_vector i p ≠ 0) :
    Projectivization.mk ℂ (s2e_c11_normalized_vector i p) hn = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    exact (Projectivization.mk_eq_mk_iff' ℂ _ v hn hv).mpr ⟨(v i)⁻¹, rfl⟩

/-- The normalized coordinate chart is the affine hyperplane with specified coordinate one.
Source: Hartshorne, Algebraic Geometry, I.2, standard projective charts. -/
def s2e_c11_coordinate_chart_homeomorph {k : ℕ} (i : Fin (k + 1)) :
    s2e_c11_coordinate_chart i ≃ₜ
      {v : ComplexProjectiveSpace.CoordinateSpace k // v i = 1} := by
  have hn (v : {v : ComplexProjectiveSpace.CoordinateSpace k // v i = 1}) : v.1 ≠ 0 := by
    intro h
    have hi := v.2
    rw [h] at hi
    exact zero_ne_one hi
  refine
    { toFun := fun p ↦ ⟨s2e_c11_normalized_vector i p.1, p.2⟩
      invFun := fun v ↦ ⟨Projectivization.mk ℂ v.1 (hn v),
        (s2e_c11_mk_mem_coordinate_chart i v.1 (hn v)).mpr (by rw [v.2]; exact one_ne_zero)⟩
      left_inv := fun p ↦ Subtype.ext (s2e_c11_normalized_vector_projective i p.1
        (s2e_c11_normalized_vector_ne_zero i p))
      right_inv := fun v ↦ Subtype.ext (by
        change (v.1 i)⁻¹ • v.1 = v.1
        rw [v.2, inv_one, one_smul])
      continuous_toFun := (s2e_c11_continuous_normalized_vector_chart i).subtype_mk _
      continuous_invFun := ?_ }
  have hq : Continuous (fun v : {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} ↦
      Projectivization.mk ℂ v.1 v.2) := continuous_quot_mk
  exact (hq.comp (continuous_subtype_val.subtype_mk hn)).subtype_mk _

/-- Every standard projective chart is simply connected, including dimension zero.
Source: Hartshorne, Algebraic Geometry, I.2; Mathlib, convex contractibility. -/
theorem s2e_c11_coordinate_chart_simply_connected {k : ℕ} (i : Fin (k + 1)) :
    IsSimplyConnected (s2e_c11_coordinate_chart i) := by
  have hc : Convex ℝ {v : ComplexProjectiveSpace.CoordinateSpace k | v i = 1} := by
    intro x hx y hy a b _ _ hab
    change a • x i + b • y i = 1
    rw [hx, hy, ← add_smul, hab, one_smul]
  have : ContractibleSpace {v : ComplexProjectiveSpace.CoordinateSpace k // v i = 1} :=
    hc.contractibleSpace ⟨fun _ ↦ 1, rfl⟩
  exact (s2e_c11_coordinate_chart_homeomorph i).toHomotopyEquiv.simplyConnectedSpace

/-- Fixing one coordinate to one and keeping another nonzero gives a path connected affine locus.
Source: Mathlib, isPathConnected_compl_singleton_of_one_lt_rank for the complex plane. -/
theorem s2e_c11_affine_pair_coordinate_path_connected
    {ι : Type*} (i j : ι) : IsPathConnected {v : ι → ℂ | v i = 1 ∧ v j ≠ 0} := by
  classical
  have hnz : IsPathConnected {z : ℂ | z ≠ 0} :=
    isPathConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  refine ⟨fun _ ↦ 1, ⟨rfl, one_ne_zero⟩, ?_⟩
  intro v hv
  let p : Path (1 : ℂ) (v j) := (hnz.joinedIn 1 one_ne_zero (v j) hv.2).somePath
  have hp (t : unitInterval) : p t ≠ 0 :=
    (hnz.joinedIn 1 one_ne_zero (v j) hv.2).somePath_mem t
  let q : Path (fun _ : ι ↦ (1 : ℂ)) v :=
    { toFun := fun t l ↦ if l = i then 1 else if l = j then p t else Path.segment 1 (v l) t
      continuous_toFun := by
        apply continuous_pi
        intro l
        by_cases hi : l = i
        · simp only [hi, if_pos rfl]
          exact continuous_const
        · by_cases hj : l = j
          · simp only [if_neg hi, if_pos hj]
            exact p.continuous
          · simp only [if_neg hi, if_neg hj]
            exact (Path.segment 1 (v l)).continuous
      source' := by
        funext l
        change (if l = i then 1 else if l = j then p 0 else Path.segment 1 (v l) 0) = 1
        split_ifs <;> first | rfl | exact p.source | exact (Path.segment 1 (v l)).source
      target' := by
        funext l
        change (if l = i then 1 else if l = j then p 1 else Path.segment 1 (v l) 1) = v l
        split_ifs with hi hj
        · simpa only [hi] using hv.1.symm
        · simpa only [hj] using p.target
        · exact (Path.segment 1 (v l)).target }
  refine ⟨q, ?_⟩
  intro t
  constructor
  · change (if i = i then 1 else if i = j then p t else Path.segment 1 (v i) t) = 1
    rw [if_pos rfl]
  · change (if j = i then 1 else if j = j then p t else Path.segment 1 (v j) t) ≠ 0
    by_cases hji : j = i
    · rw [if_pos hji]
      exact one_ne_zero
    · rw [if_neg hji, if_pos rfl]
      exact hp t

/-- Pairwise coordinate chart intersections are path connected.
Source: Hartshorne, Algebraic Geometry, I.2, normalized coordinate charts;
Mathlib, continuous images of path connected spaces. -/
theorem s2e_c11_coordinate_chart_intersection_path_connected
    {k : ℕ} (i j : Fin (k + 1)) :
    IsPathConnected (s2e_c11_coordinate_chart i ∩ s2e_c11_coordinate_chart j) := by
  let S : Set (ComplexProjectiveSpace.CoordinateSpace k) := {v | v i = 1 ∧ v j ≠ 0}
  have hn (v : S) : v.1 ≠ 0 := by
    intro h
    have hi := v.2.1
    rw [h] at hi
    exact zero_ne_one hi
  let q : S → Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) :=
    fun v ↦ Projectivization.mk ℂ v.1 (hn v)
  have hq : Continuous q := continuous_quot_mk.comp (continuous_subtype_val.subtype_mk hn)
  have : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp
    (s2e_c11_affine_pair_coordinate_path_connected i j)
  have hr : Set.range q = s2e_c11_coordinate_chart i ∩ s2e_c11_coordinate_chart j := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(s2e_c11_mk_mem_coordinate_chart i v.1 (hn v)).mpr
        (by rw [v.2.1]; exact one_ne_zero),
        (s2e_c11_mk_mem_coordinate_chart j v.1 (hn v)).mpr v.2.2⟩
    · intro hp
      let v := s2e_c11_normalized_vector i p
      have hnv : v ≠ 0 := s2e_c11_normalized_vector_ne_zero i ⟨p, hp.1⟩
      have heq : Projectivization.mk ℂ v hnv = p := s2e_c11_normalized_vector_projective i p hnv
      have hj : v j ≠ 0 := (s2e_c11_mk_mem_coordinate_chart j v hnv).mp (heq ▸ hp.2)
      exact ⟨⟨v, hp.1, hj⟩, heq⟩
  exact hr ▸ isPathConnected_range hq

/-- Some homogeneous coordinate is nonzero at every projective point.
Source: Hartshorne, Algebraic Geometry, I.2, standard chart cover. -/
theorem s2e_c11_coordinate_chart_cover {k : ℕ}
    (p : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :
    ∃ i, p ∈ s2e_c11_coordinate_chart i := by
  obtain ⟨i, hi⟩ := ComplexProjectiveSpace.exists_coordinate_ne_zero p.rep p.rep_nonzero
  refine ⟨i, ?_⟩
  rw [← p.mk_rep]
  exact (s2e_c11_mk_mem_coordinate_chart i p.rep p.rep_nonzero).mpr hi

/-- Complex projective space is simply connected by its actual coordinate chart cover.
Source: Hartshorne, Algebraic Geometry, I.2, projective charts;
Hatcher, Algebraic Topology, section 1.2, path-class gluing. -/
theorem s2e_c11_classical_projective_simply_connected_direct (k : ℕ) :
    SimplyConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) := by
  have hn : (fun _ : Fin (k + 1) ↦ (1 : ℂ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  apply s2e_c11_simply_connected_common_point_cover
    (fun i : Fin (k + 1) ↦ s2e_c11_coordinate_chart i)
    s2e_c11_isOpen_coordinate_chart s2e_c11_coordinate_chart_cover
    s2e_c11_coordinate_chart_simply_connected
    (Projectivization.mk ℂ (fun _ ↦ 1) hn)
  · intro i
    exact (s2e_c11_mk_mem_coordinate_chart i (fun _ ↦ 1) hn).mpr one_ne_zero
  · exact s2e_c11_coordinate_chart_intersection_path_connected

end HodgeLean.Foundations.Program
