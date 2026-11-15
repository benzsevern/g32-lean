import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import HodgeLean.Foundations.Program.MarkedRootCoverLoops

noncomputable section
open Set Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_finite_mem (z : ℂ) :
    (z : OnePoint ℂ) ∈ b6t_punctured mr_base ↔ z ∉ b65r_marks := by
  rw [b6t_punctured, mem_compl_iff, mr_mem_branch]
  simp only [OnePoint.coe_ne_infty, false_or, OnePoint.coe_eq_coe, mr_fin]
  simp [b65r_marks, mr_marks, eq_comm]

def b65r_chartMap (z : {z : ℂ // z ∉ b65r_marks}) : b6t_punctured mr_base :=
  ⟨(z.val : OnePoint ℂ), (b65r_finite_mem z.val).mpr z.property⟩

theorem b65r_chartMap_bijective : Function.Bijective b65r_chartMap := by
  constructor
  · intro z w h
    exact Subtype.ext (OnePoint.coe_injective (congrArg Subtype.val h))
  · intro y
    have hy : y.val ≠ OnePoint.infty := by
      intro h
      exact y.property ⟨12, h.symm⟩
    obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hy
    have hm : z ∉ b65r_marks := (b65r_finite_mem z).mp (hz ▸ y.property)
    exact ⟨⟨z, hm⟩, Subtype.ext hz⟩

def b65r_chart : {z : ℂ // z ∉ b65r_marks} ≃ₜ b6t_punctured mr_base :=
  (Equiv.ofBijective b65r_chartMap b65r_chartMap_bijective).toHomeomorphOfIsInducing
    ((OnePoint.isOpenEmbedding_coe.isInducing.comp
      Topology.IsInducing.subtypeVal).codRestrict _)

theorem b65r_mapOfEq_fromPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (p : Path x x) :
    FundamentalGroup.mapOfEq f h (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((p.map f.continuous).cast h.symm h.symm)) := by
  exact FundamentalGroup.mapOfEq_apply f h _

theorem b65r_mapOfEq_leftInverse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {x : X} {y : Y} (h : e x = y) (c : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
      (by rw [← h]; exact e.symm_apply_apply x)
      (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h c) = c := by
  change FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ _
    (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
      (FundamentalGroup.fromPath c.toPath)) = FundamentalGroup.fromPath c.toPath
  induction c.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [b65r_mapOfEq_fromPath, b65r_mapOfEq_fromPath]
      congr 1
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact e.symm_apply_apply (p t)

theorem b65r_transport_congr (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (γ δ : ℝ → ℂ)
    (h : EqOn γ δ (Icc (0 : ℝ) 1)) : b65f_transport E A γ = b65f_transport E A δ := by
  unfold b65f_transport
  congr 1
  funext N
  unfold b65f_polygon
  congr 3
  funext i
  have hp : (0 : ℝ) < 2^N := by positivity
  have hi : (i.val : ℝ) + 1 ≤ (2 : ℝ)^N := by
    exact_mod_cast i.isLt
  rw [h ⟨by positivity, (div_le_one hp).mpr (by linarith)⟩,
    h ⟨by positivity, (div_le_one hp).mpr hi⟩]

end HodgeLean.Foundations.Program
