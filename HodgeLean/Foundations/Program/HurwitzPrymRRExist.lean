import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rr`: small lemmas for the Riemann existence assembly

A finite subset of a nonempty Riemann surface misses a point, and reversing a tuple turns its
product into the product of the opposites.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

/-- **A finite set misses a point** of a nonempty manifold modelled on a complex line: a chart
image of a countable set has dense complement. -/
theorem HurwitzPrymRR_exists_not_mem {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [Nonempty Y]
    (hE' : Module.finrank ℂ E' = 1) {B : Set Y} (hB : B.Finite) : ∃ y, y ∉ B := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have : Nontrivial E' := Module.nontrivial_of_finrank_eq_succ hE'
  let φ := chartAt E' y
  have hd : Dense (φ '' (B ∩ φ.source))ᶜ :=
    ((hB.subset Set.inter_subset_left).image φ).countable.dense_compl ℂ
  obtain ⟨z, hz, hzB⟩ := hd.inter_open_nonempty _ φ.open_target
    ⟨φ y, φ.map_source (mem_chart_source E' y)⟩
  exact ⟨φ.symm z, fun hmem ↦ hzB ⟨φ.symm z, ⟨hmem, φ.map_target hz⟩, φ.right_inv hz⟩⟩

/-- **Reversing a tuple in `Gᵐᵒᵖ`**: `∏ op (g (rev j)) = op (∏ g j)`. -/
theorem HurwitzPrymRR_prod_op_rev {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (List.ofFn fun j : Fin r ↦ MulOpposite.op (g j.rev)).prod =
      MulOpposite.op (List.ofFn g).prod := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ', List.prod_cons, List.prod_concat, MulOpposite.op_mul]
    congr 1
    rw [← ih (fun i ↦ g i.castSucc)]
    simp [Fin.rev_succ]

end HodgeLean.Foundations.Program
