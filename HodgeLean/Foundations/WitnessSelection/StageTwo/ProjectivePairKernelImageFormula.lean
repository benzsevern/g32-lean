import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelGraphFormula

/-! Boolean images under normalized Hermitian coordinates.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- The normalized Hermitian image of a Boolean family of complex vectors is Boolean.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_kernel_image_formula {ι : Type*} [Fintype ι] {k : ℕ}
    (r s : ι → MvPolynomial (Fin k) ℝ) (b : s2v_t11b_Formula k) :
    let N := Fintype.card ((ι × ι) ⊕ (ι × ι))
    let v := fun x : EuclideanSpace ℝ (Fin k) => fun i =>
      (MvPolynomial.eval (fun j => x j) (r i) : ℂ) +
        (MvPolynomial.eval (fun j => x j) (s i) : ℂ) * Complex.I
    ∃ f : s2v_t11b_Formula N, ∀ z, z ∈ f.realize ↔
      ∃ x : EuclideanSpace ℝ (Fin k), x ∈ b.realize ∧ v x ≠ 0 ∧
        z = s2e_pair_complexRealCoordinates
          (fun a : ι × ι => s2e_pair_projectiveKernel (v x) a.1 a.2) := by
  classical
  dsimp only
  let N := Fintype.card ((ι × ι) ⊕ (ι × ι))
  let β := s2v_hardt2_boundIndex N k
  let φ := s2v_hardt2_freeIndex N k
  obtain ⟨G, hG⟩ := s2e_pair_kernel_graph_formula
    (fun i => MvPolynomial.rename β (r i))
    (fun i => MvPolynomial.rename β (s i)) φ
  obtain ⟨f, hf⟩ := s2v_hardt2_repeated_projection
    (.inter (s2v_hardt1_rename β b) G)
  refine ⟨f, ?_⟩
  intro z
  rw [hf]
  constructor
  · rintro ⟨y, hy, hg⟩
    rw [s2v_hardt1_realize_rename] at hy
    rw [hG] at hg
    simp only [MvPolynomial.eval_rename, s2v_hardt2_insert_bound,
      s2v_hardt2_insert_free, β, φ, Function.comp_def] at hy hg
    exact ⟨WithLp.toLp 2 y, hy, hg.1, by ext j; exact hg.2 j⟩
  · rintro ⟨x, hx, hv, rfl⟩
    refine ⟨fun j => x j, ?_, ?_⟩
    · rw [s2v_hardt1_realize_rename]
      simpa only [β, s2v_hardt2_insert_bound] using hx
    · rw [hG]
      simp only [MvPolynomial.eval_rename, β, φ, Function.comp_def,
        s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
      exact ⟨hv, fun _ => trivial⟩

end HodgeLean.WitnessSelection.StageTwo
