import HodgeLean.Foundations.Program.RelativeFrameFamilyDefs

noncomputable section
open Set Metric Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf7_pieceCover_of_compact_closure {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (O : Set C) (hO : IsOpen O) (hK : IsCompact (closure O))
    (A : closure O → OpenPartialHomeomorph C ℂ)
    (hA : ∀ p, p.val ∈ (A p).source ∧ A p ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C) :
    ∃ P : rf2_PieceCover C O, ∀ i, ∃ p : closure O, P.chart i = A p := by
  classical
  have hex (p : closure O) : ∃ r > 0, closedBall (A p p.val) r ⊆ (A p).target := by
    obtain ⟨R, hR, hRT⟩ := Metric.isOpen_iff.mp (A p).open_target _ ((A p).map_source (hA p).1)
    exact ⟨R / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hRT⟩
  choose r hr hrt using hex
  let V : closure O → Set C := fun p ↦ (A p).source ∩ A p ⁻¹' ball (A p p.val) (r p)
  have hVo (p : closure O) : IsOpen (V p) := (A p).isOpen_inter_preimage Metric.isOpen_ball
  have hpV (p : closure O) : p.val ∈ V p := ⟨(hA p).1, Metric.mem_ball_self (hr p)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hVo (fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hpV ⟨y, hy⟩⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let chart : Fin (Fintype.card s) → OpenPartialHomeomorph C ℂ := fun i ↦ A (e i).val
  let piece : Fin (Fintype.card s) → Set ℂ := fun i ↦
    (chart i).target ∩ (chart i).symm ⁻¹' O ∩ ball (A (e i).val (e i).val.val) (r (e i).val)
  have hpo (i) : IsOpen (piece i) :=
    ((chart i).symm.isOpen_inter_preimage hO).inter Metric.isOpen_ball
  have hpB (i) : closure (piece i) ⊆ closedBall (A (e i).val (e i).val.val) (r (e i).val) :=
    closure_minimal (fun _ hz ↦ Metric.ball_subset_closedBall hz.2) Metric.isClosed_closedBall
  have hpc (i) : IsCompact (closure (piece i)) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (hpB i)
  have hpt (i) : closure (piece i) ⊆ (chart i).target := (hpB i).trans (hrt (e i).val)
  have hcover : O = ⋃ i, (chart i).symm '' piece i := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs (subset_closure hy))
      obtain ⟨hps, hyp⟩ := Set.mem_iUnion.mp hp
      let i := e.symm ⟨p, hps⟩
      have he : (e i).val = p := congrArg Subtype.val (e.apply_symm_apply ⟨p, hps⟩)
      apply Set.mem_iUnion.mpr
      refine ⟨i, chart i y, ?_, ?_⟩
      · change (A (e i).val y ∈ (A (e i).val).target ∧
          (A (e i).val).symm (A (e i).val y) ∈ O) ∧
          A (e i).val y ∈ ball (A (e i).val (e i).val.val) (r (e i).val)
        rw [he]
        exact ⟨⟨(A p).map_source hyp.1, by rw [(A p).left_inv hyp.1]; exact hy⟩, hyp.2⟩
      · change (A (e i).val).symm (A (e i).val y) = y
        rw [he]
        exact (A p).left_inv hyp.1
    · intro hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      exact hz.1.2
  exact ⟨⟨Fintype.card s, chart, fun i ↦ (hA (e i).val).2, piece, hpo, hpc, hpt, hcover⟩,
    fun i ↦ ⟨(e i).val, rfl⟩⟩

/-- Adding specified coordinate pieces preserves a finite cover when their images lie in it.
Source: `rf2_PieceCover.covers`. -/
def rf7_appendPieceCover {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O)
    (m : ℕ) (A : Fin m → OpenPartialHomeomorph C ℂ) (V : Fin m → Set ℂ)
    (hA : ∀ k, A k ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C)
    (hVo : ∀ k, IsOpen (V k)) (hVc : ∀ k, IsCompact (closure (V k)))
    (hVt : ∀ k, closure (V k) ⊆ (A k).target)
    (hsub : ∀ k, (A k).symm '' V k ⊆ O) : rf2_PieceCover C O where
  n := P.n + m
  chart := Fin.append P.chart A
  analytic := by
    intro i
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa using P.analytic k
    · simpa using hA k
  piece := Fin.append P.piece V
  isOpen := by
    intro i
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa using P.isOpen k
    · simpa using hVo k
  compact := by
    intro i
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa using P.compact k
    · simpa using hVc k
  contained := by
    intro i
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa using P.contained k
    · simpa using hVt k
  covers := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, z, hz, hyz⟩ := mem_iUnion.mp (P.covers ▸ hy)
      apply mem_iUnion.mpr
      refine ⟨Fin.castAdd m i, z, ?_, ?_⟩
      · simpa using hz
      · simpa using hyz
    · intro hy
      obtain ⟨i, z, hz, hyz⟩ := mem_iUnion.mp hy
      revert hz hyz
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
      · intro hz hyz
        rw [P.covers]
        apply mem_iUnion.mpr
        refine ⟨k, z, ?_, ?_⟩
        · simpa using hz
        · simpa using hyz
      · intro hz hyz
        apply hsub k
        exact ⟨z, by simpa using hz, by simpa using hyz⟩

end HodgeLean.Foundations.Program
