import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GraphImages

/-! Graph lifts adjoining actual coordinate projections without increasing dimension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_coordinate_graph_lift {n d : ℕ}
    (S : s2v_t11b_Formula n) (P : s2v_hardt_cad5_Partition S.realize)
    (r : Fin d → Fin n) :
    ∃ R : s2v_t11b_Formula (n + d), ∃ PR : s2v_hardt_cad5_Partition R.realize,
      (∀ (x : EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin d)),
        WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => a i)) ∈ R.realize ↔
          x ∈ S.realize ∧ a = WithLp.toLp 2 (fun i => x (r i))) ∧
      PR.dimension ≤ P.dimension ∧
      (∀ x ∈ closure S.realize, WithLp.toLp 2
        (Fin.append (fun i => x i) (fun i => x (r i))) ∈ closure R.realize) := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_coordinate_map_graph r
  let R : s2v_t11b_Formula (n + d) :=
    .inter (s2v_hardt1_rename (Fin.castAdd d) S) D
  have hR (x : EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin d)) :
      WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => a i)) ∈ R.realize ↔
        x ∈ S.realize ∧ a = WithLp.toLp 2 (fun i => x (r i)) := by
    change (_ ∧ _) ↔ _
    rw [s2v_hardt1_realize_rename, hD]
    have hx : WithLp.toLp 2 (fun i => Fin.append (fun j => x j)
        (fun j => a j) (Fin.castAdd d i)) = x := by ext i; simp only [Fin.append_left]
    rw [hx]
  obtain ⟨PR⟩ := s2v_hardt_cad5_partition_exists R
  let rFull : Fin (n + d) → Fin n := Fin.addCases id r
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + d)) :=
    fun x => WithLp.toLp 2 (fun i => x (rFull i))
  have hF (x : EuclideanSpace ℝ (Fin n)) : F x = WithLp.toLp 2
      (Fin.append (fun i => x i) (fun i => x (r i))) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [F, rFull]
  let f : S.realize → R.realize := fun x =>
    ⟨F x.val, by rw [hF]; exact (hR _ _).mpr ⟨x.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro y
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => y.val (i.castAdd d))
    let a : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => y.val (i.natAdd n))
    have hy : WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => a i)) = y.val := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [x, a]
    obtain ⟨hx, ha⟩ := (hR x a).mp (by rw [hy]; exact y.property)
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change F x = y.val
    rw [hF]
    exact (congrArg (fun b : EuclideanSpace ℝ (Fin d) => WithLp.toLp 2
      (Fin.append (fun i => x i) (fun i => b i))) ha.symm).trans hy
  obtain ⟨G, hG⟩ := s2v_hardt_cad5_coordinate_map_graph rFull
  have hGraph : ∀ (x : S.realize) (y : EuclideanSpace ℝ (Fin (n + d))),
      WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => y i)) ∈ G.realize ↔
        y = (f x).val := fun x y => hG x.val y
  have hdim := s2v_hardt_cad5_dimension_le_of_graph_surjective P PR f hf G hGraph
  refine ⟨R, PR, hR, hdim, ?_⟩
  have hcF : Continuous F := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (continuous_apply (rFull i)).comp (PiLp.continuous_ofLp 2 _)))
  have himage : F '' S.realize ⊆ R.realize := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hF]
    exact (hR _ _).mpr ⟨hx, rfl⟩
  intro x hx
  have hcl := closure_mono himage (mem_closure_image hcF.continuousAt hx)
  simpa only [hF] using hcl

end HodgeLean.Foundations.Program
