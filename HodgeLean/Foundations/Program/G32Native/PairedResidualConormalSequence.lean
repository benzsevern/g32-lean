import HodgeLean.Foundations.Program.G32Native.PairedResidualPresentationDefs
import HodgeLean.Foundations.Program.G32Native.UnionConormalSequence

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The retained endpoint identifications transport the union conormal sequence.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_residual_conormal_sequence
    {P V : Over (Spec ↧ℂ)} [IsIntegral P.left] [Smooth P.hom] [Smooth V.hom]
    (i : P ⟶ V) [IsClosedImmersion i.left] (k : ℕ) (L : P.left.Modules)
    (R : PairedResidualPresentation P V i k L) :
    ∃ (f : (SheafOfModules.free (R := P.left.ringCatSheaf) (Fin k) :
        P.left.Modules) ⟶ s2c_conormal i.left)
      (g : s2c_conormal i.left ⟶ L)
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact := by
  letI := R.closed_t
  letI := R.closed_t₂
  letI := R.closed_a
  letI := R.closed_s₁
  letI := R.closed_s₂
  letI := R.smooth_T₂
  obtain ⟨f, g, hfg, hseq⟩ := union_conormal_sequence_aux
    V R.T P R.T₂ R.S R.t i R.t₂
    R.a R.s₁ R.s₂ R.ha R.hs R.union_ideal R.intersection_ideal
    R.noncontainment k R.local_frames
  let f' := R.sourceIso.inv ≫ f
  let g' := g ≫ R.lastIso.hom
  have hz : f' ≫ g' = 0 := by
    simp only [f', g', Category.assoc, ← Category.assoc f g, hfg,
      zero_comp, comp_zero]
  refine ⟨f', g', hz, ?_⟩
  let e : ShortComplex.mk f g hfg ≅ ShortComplex.mk f' g' hz :=
    ShortComplex.isoMk R.sourceIso (Iso.refl _) R.lastIso (by
      simp only [f', Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]) (by
      simp only [g', Iso.refl_hom, Category.id_comp])
  exact ShortComplex.shortExact_of_iso e hseq


#print axioms paired_residual_conormal_sequence
end HodgeLean.Foundations.Program.G32Native
