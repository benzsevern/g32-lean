import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationComparisonHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1GenericOpenHelpers
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Actual normalization etaleness over isomorphic base opens -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatible nonempty open bases transport etaleness of the normalization
of the specified dominant field source. -/
theorem s2e_c1_normalization_etale_of_open_base_iso
    {K : Type} [Field K] {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Spec (CommRingCat.of K) ⟶ X) (g : Spec (CommRingCat.of K) ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    [QuasiCompact g] [QuasiSeparated g] [IsDominant g]
    (b : X ⟶ Y) (hfg : f ≫ b = g)
    (U : X.Opens) (V : Y.Opens)
    (hU : (U : Set X).Nonempty) (hV : (V : Set Y).Nonempty)
    (e : U.toScheme ≅ V.toScheme) (he : e.hom ≫ V.ι = U.ι ≫ b)
    [Etale (g.fromNormalization ∣_ V)] : Etale (f.fromNormalization ∣_ U) := by
  obtain ⟨fU, hfqc, hfqs, hf⟩ := s2e_c1_generic_source_lift_to_open X f U hU
  obtain ⟨gV, hgqc, hgqs, hg⟩ := s2e_c1_generic_source_lift_to_open Y g V hV
  letI := hfqc
  letI := hfqs
  letI := hgqc
  letI := hgqs
  have hcompat : fU ≫ e.hom = gV := by
    rw [← cancel_mono V.ι, Category.assoc, he, ← Category.assoc, hf, hg, hfg]
  obtain ⟨E, _, _, _, hbase, _, _, _⟩ :=
    s2e_c1_normalization_open_base_iso f g U V e fU gV hf hg hcompat
  have heq : (f.fromNormalization ∣_ U) =
      E.hom ≫ (g.fromNormalization ∣_ V) ≫ e.inv := by
    rw [← Category.assoc, hbase, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

end HodgeLean.Foundations.Program
