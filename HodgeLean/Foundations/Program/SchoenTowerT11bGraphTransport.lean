import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Transport between maps and their actual polynomial graphs.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Graph coordinates restricted over any base subset retain the original map value.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, graph projection formulation. -/
def s2v_t11b_graphRestrictionHomeomorph {n : ℕ} (f : s2v_t11b_Formula n)
    (p : EuclideanSpace ℝ (Fin n) → ℝ) (hp : Continuous p)
    (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), z ∈ g.realize ↔
      WithLp.toLp 2 (fun i : Fin n => z i.castSucc) ∈ f.realize ∧
        z (Fin.last n) = p (WithLp.toLp 2 (fun i : Fin n => z i.castSucc)))
    (U : Set ℝ) :
    {y : EuclideanSpace ℝ (Fin n) | y ∈ f.realize ∧ p y ∈ U} ≃ₜ
      {z : EuclideanSpace ℝ (Fin (n + 1)) | z ∈ g.realize ∧ z (Fin.last n) ∈ U} where
  toFun y := ⟨WithLp.toLp 2 (Fin.snoc (fun i => y.val i) (p y.val)), by
    constructor
    · apply (hg _).mpr
      simpa only [WithLp.ofLp_toLp, Fin.snoc_castSucc, WithLp.toLp_ofLp, Fin.snoc_last]
        using And.intro y.property.1 (rfl : p y.val = p y.val)
    · simpa only [Fin.snoc_last] using y.property.2⟩
  invFun z := ⟨WithLp.toLp 2 (fun i : Fin n => z.val i.castSucc), by
    obtain ⟨hy, heq⟩ := (hg z.val).mp z.property.1
    exact ⟨hy, heq ▸ z.property.2⟩⟩
  left_inv y := by
    apply Subtype.ext
    ext i
    simp only [Fin.snoc_castSucc]
  right_inv z := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    change Fin.snoc (fun i : Fin n => z.val i.castSucc)
      (p (WithLp.toLp 2 (fun i : Fin n => z.val i.castSucc))) = WithLp.ofLp z.val
    rw [← ((hg z.val).mp z.property.1).2]
    exact Fin.snoc_init_self _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
    exact (((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp
      continuous_subtype_val).finSnoc (hp.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i.castSucc).comp
      continuous_subtype_val

/-- The last graph coordinate is exactly the original map value after restriction.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, graph projection formulation. -/
theorem s2v_t11b_graphRestrictionHomeomorph_projection {n : ℕ}
    (f : s2v_t11b_Formula n) (p : EuclideanSpace ℝ (Fin n) → ℝ) (hp : Continuous p)
    (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), z ∈ g.realize ↔
      WithLp.toLp 2 (fun i : Fin n => z i.castSucc) ∈ f.realize ∧
        z (Fin.last n) = p (WithLp.toLp 2 (fun i : Fin n => z i.castSucc)))
    (U : Set ℝ) (y : {y : EuclideanSpace ℝ (Fin n) | y ∈ f.realize ∧ p y ∈ U}) :
    (s2v_t11b_graphRestrictionHomeomorph f p hp g hg U y).val (Fin.last n) = p y.val := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) (fun i => y.val i) (p y.val) (Fin.last n) = p y.val
  exact Fin.snoc_last _ _

end HodgeLean.Foundations.Program
