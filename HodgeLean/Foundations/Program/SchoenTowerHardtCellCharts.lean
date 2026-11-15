import HodgeLean.Foundations.Program.SchoenTowerT11bBands

/-! Open-box charts for graph and band lifts of a supplied base chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Append one normalized interval coordinate to an open unit box.
Source: Coste, Real Algebraic Sets (2005), §1.2, printed p. 7, chart induction;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, cylindrical cells. -/
def s2v_hardt_extend_box (d : ℕ) :
    ({t : EuclideanSpace ℝ (Fin d) | ∀ a, -1 < t a ∧ t a < 1} × Set.Ioo (0 : ℝ) 1) ≃ₜ
      {t : EuclideanSpace ℝ (Fin (d + 1)) | ∀ a, -1 < t a ∧ t a < 1} where
  toFun z := ⟨WithLp.toLp 2 (Fin.cons (2 * z.2.val - 1) (fun i => z.1.val i)), by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change -1 < 2 * z.2.val - 1 ∧ 2 * z.2.val - 1 < 1
      constructor <;> linarith [z.2.property.1, z.2.property.2]
    · exact z.1.property j⟩
  invFun z := (⟨WithLp.toLp 2 (fun i => z.val i.succ), fun i => z.property i.succ⟩,
    ⟨(z.val 0 + 1) / 2, by
      constructor <;> linarith [(z.property 0).1, (z.property 0).2]⟩)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      ext i
      rfl
    · apply Subtype.ext
      change (2 * z.2.val - 1 + 1) / 2 = z.2.val
      ring
  right_inv z := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 2 * ((z.val 0 + 1) / 2) - 1 = z.val 0
      ring
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun z : ({t : EuclideanSpace ℝ (Fin d) | ∀ a, -1 < t a ∧ t a < 1} × Set.Ioo (0 : ℝ) 1) => 2 * z.2.val - 1)
      fun_prop
    · change Continuous (fun z : ({t : EuclideanSpace ℝ (Fin d) | ∀ a, -1 < t a ∧ t a < 1} × Set.Ioo (0 : ℝ) 1) => z.1.val j)
      fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
      apply continuous_pi
      intro i
      change Continuous (fun z : {t : EuclideanSpace ℝ (Fin (d + 1)) | ∀ a, -1 < t a ∧ t a < 1} => z.val i.succ)
      fun_prop
    · apply Continuous.subtype_mk
      change Continuous (fun z : {t : EuclideanSpace ℝ (Fin (d + 1)) | ∀ a, -1 < t a ∧ t a < 1} => (z.val 0 + 1) / 2)
      fun_prop

/-- A continuous section graph inherits the supplied base cell chart.
Source: Coste, Real Algebraic Sets (2005), §1.2, printed p. 7, graph cells;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, cylindrical cells. -/
def s2v_hardt_graph_chart {X : Type*} [TopologicalSpace X] {d : ℕ}
    (e : X ≃ₜ {t : EuclideanSpace ℝ (Fin d) | ∀ a, -1 < t a ∧ t a < 1})
    (s : X → ℝ) (hs : Continuous s) :
    {z : X × ℝ | z.2 = s z.1} ≃ₜ
      {t : EuclideanSpace ℝ (Fin d) | ∀ a, -1 < t a ∧ t a < 1} :=
  ({ toFun := fun z => z.val.1
     invFun := fun x => ⟨(x, s x), rfl⟩
     left_inv := by
       intro z
       apply Subtype.ext
       exact Prod.ext rfl z.property.symm
     right_inv := fun _ => rfl
     continuous_toFun := continuous_fst.comp continuous_subtype_val
     continuous_invFun := (continuous_id.prodMk hs).subtype_mk _ } :
      {z : X × ℝ | z.2 = s z.1} ≃ₜ X).trans e

/-- Two ordered continuous sections give a cell chart of one higher dimension.
Source: Coste, Real Algebraic Sets (2005), §1.2, printed p. 7, band cells;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, cylindrical cells. -/
def s2v_hardt_band_chart {X : Type*} [TopologicalSpace X] {d : ℕ}
    (e : X ≃ₜ {t : EuclideanSpace ℝ (Fin d) | ∀ a, -1 < t a ∧ t a < 1})
    (l u : X → ℝ) (hl : Continuous l) (hu : Continuous u) (hlu : ∀ x, l x < u x) :
    {z : X × ℝ | l z.1 < z.2 ∧ z.2 < u z.1} ≃ₜ
      {t : EuclideanSpace ℝ (Fin (d + 1)) | ∀ a, -1 < t a ∧ t a < 1} :=
  ((s2v_t11b_bandHomeomorph l u hl hu hlu).trans
    (e.prodCongr (Homeomorph.refl _))).trans (s2v_hardt_extend_box d)

end HodgeLean.Foundations.Program
