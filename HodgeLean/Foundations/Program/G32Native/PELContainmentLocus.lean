import HodgeLean.Foundations.Program.G32Native.PELMarkedCircleMatrix
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations HodgeLean.Adapters MvPolynomial
open scoped TensorProduct

/-- Testing the full marked circle tests containment of the generated Hodge group. -/
theorem pel_hodgeGroup_subset_iff_equations {R : PELSplitReference}
    (F : PELSplitFamily R) (z : PELSplitComponent R)
    (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (S : Set (MvPolynomial (Fin 12 × Fin 12) ℚ))
    (hG : g2_IsRatAlgSubgroup G) (hS : G = g2_ratZeroSet S) :
    F.hodgeGroup z ⊆ G ↔ ∀ c : Circle, ∀ p ∈ S,
      aeval (fun ij : Fin 12 × Fin 12 =>
        (((c : ℂ).re : ℂ) • (1 : Matrix (Fin 12) (Fin 12) ℂ) -
          ((c : ℂ).im : ℂ) • z.val.J.map (algebraMap ℝ ℂ)) ij.1 ij.2) p = 0 := by
  constructor
  · intro h c p hp
    let g := g2h_circleMat (latticeHodgePieces (F.fibre z).X)
      (spec_latticeHodgePieces_isInternal (F.fibre z).X) (F.basis z) c
    have hg : g ∈ F.hodgeGroup z :=
      g2_circleImage_subset_hodgeGroup _ _ _ ⟨c, rfl⟩
    have hh := h hg
    rw [hS] at hh
    have he : (g : Matrix (Fin 12) (Fin 12) ℂ) = _ :=
      pel_marked_circle_matrix R F z c
    have hhp := hh p hp
    change aeval (fun ij : Fin 12 × Fin 12 =>
      (g : Matrix (Fin 12) (Fin 12) ℂ) ij.1 ij.2) p = 0 at hhp
    rw [he] at hhp
    exact hhp
  · intro h
    apply Set.sInter_subset_of_mem
    refine ⟨hG, ?_⟩
    rintro g ⟨c, hc⟩
    rw [hS]
    intro p hp
    change aeval (fun ij : Fin 12 × Fin 12 =>
      (g : Matrix (Fin 12) (Fin 12) ℂ) ij.1 ij.2) p = 0
    rw [hc, pel_marked_circle_matrix R F z c]
    exact h c p hp

/-- The containment locus is closed in the ordinary retained matrix topology. -/
theorem pel_hodgeGroup_containment_isClosed {R : PELSplitReference}
    (F : PELSplitFamily R) (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hG : g2_IsRatAlgSubgroup G) :
    IsClosed {z : PELSplitComponent R | F.hodgeGroup z ⊆ G} := by
  obtain ⟨S, hS⟩ := hG.1
  have he : {z : PELSplitComponent R | F.hodgeGroup z ⊆ G} =
      ⋂ c : Circle, ⋂ p : S, {z | aeval (fun ij : Fin 12 × Fin 12 =>
        (((c : ℂ).re : ℂ) • (1 : Matrix (Fin 12) (Fin 12) ℂ) -
          ((c : ℂ).im : ℂ) • z.val.J.map (algebraMap ℝ ℂ)) ij.1 ij.2) p.val = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [pel_hodgeGroup_subset_iff_equations F z G S hG hS]
    constructor
    · intro h c p
      exact h c p.val p.property
    · intro h c p hp
      exact h c ⟨p, hp⟩
  rw [he]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro p
  apply isClosed_eq _ continuous_const
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro ij
  have hJ : Continuous (fun z : PELSplitComponent R => z.val.J ij.1 ij.2) :=
    (continuous_apply ij.2).comp ((continuous_apply ij.1).comp
      (continuous_induced_dom.comp continuous_subtype_val))
  change Continuous (fun z : PELSplitComponent R =>
    ((c : ℂ).re : ℂ) * (1 : Matrix (Fin 12) (Fin 12) ℂ) ij.1 ij.2 -
      ((c : ℂ).im : ℂ) * (z.val.J ij.1 ij.2 : ℂ))
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp hJ))

#print axioms pel_hodgeGroup_subset_iff_equations
#print axioms pel_hodgeGroup_containment_isClosed
end HodgeLean.Foundations.Program.GeneralTypeIII
