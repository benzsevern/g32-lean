import HodgeLean.Foundations.Program.SchoenTowerT11bCylindricalRegularProjection

/-! Actual Euclidean subset coordinates for one-coordinate cylindrical projections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The first coordinate and remaining coordinates reconstruct an actual Euclidean point.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical coordinate reconstruction step. -/
theorem s2v_t11b_euclidean_cons_eta {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) :
    WithLp.toLp 2 (Fin.cons (y 0) (fun i => y i.succ)) = y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl


/-- Separate the first coordinate over any Euclidean subset and specified remaining-coordinate base.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical subset coordinate step. -/
def s2v_t11b_euclideanSetBaseChart {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) (K : Set (EuclideanSpace ℝ (Fin n))) :
    {y : EuclideanSpace ℝ (Fin (n + 1)) | y ∈ S ∧ WithLp.toLp 2 (fun i => y i.succ) ∈ K} ≃ₜ
      {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun i => z.1.val i)) ∈ S} where
  toFun y := ⟨(⟨WithLp.toLp 2 (fun i => y.val i.succ), y.property.2⟩, y.val 0), by
    change WithLp.toLp 2 (Fin.cons (y.val 0) (fun i => y.val i.succ)) ∈ S
    rw [s2v_t11b_euclidean_cons_eta]
    exact y.property.1⟩
  invFun z := ⟨WithLp.toLp 2 (Fin.cons z.val.2 (fun i => z.val.1.val i)),
    z.property, z.val.1.property⟩
  left_inv y := Subtype.ext (s2v_t11b_euclidean_cons_eta y.val)
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      apply continuous_pi
      intro i
      exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i.succ).comp continuous_subtype_val
    · exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd.comp continuous_subtype_val
    · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))


/-- The actual Euclidean projection fiber is its specified first-coordinate slice.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, actual cylindrical fiber step. -/
def s2v_t11b_euclideanSetFiberChart {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) (b : EuclideanSpace ℝ (Fin n)) :
    {y : EuclideanSpace ℝ (Fin (n + 1)) | y ∈ S ∧ WithLp.toLp 2 (fun i => y i.succ) = b} ≃ₜ
      {x : ℝ | WithLp.toLp 2 (Fin.cons x (fun i => b i)) ∈ S} where
  toFun y := ⟨y.val 0, by
    have h : WithLp.toLp 2 (Fin.cons (y.val 0) (fun i => b i)) = y.val := by
      ext i
      refine Fin.cases (by rfl) (fun j => ?_) i
      exact (congrArg (fun t : EuclideanSpace ℝ (Fin n) => t j) y.property.2).symm
    change WithLp.toLp 2 (Fin.cons (y.val 0) (fun i => b i)) ∈ S
    rw [h]
    exact y.property.1⟩
  invFun x := ⟨WithLp.toLp 2 (Fin.cons x.val (fun i => b i)), x.property, rfl⟩
  left_inv y := by
    apply Subtype.ext
    ext i
    refine Fin.cases (by rfl) (fun j => ?_) i
    exact (congrArg (fun t : EuclideanSpace ℝ (Fin n) => t j) y.property.2).symm
  right_inv _ := rfl
  continuous_toFun := ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_subtype_val
    · exact continuous_const

end HodgeLean.Foundations.Program
