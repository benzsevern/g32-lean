import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationOverComparisonHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1PartialIsoTowerHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1GenericOpenHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1GoodFibreHelpers

/-! # A degree-sized fibre after a retained-field base modification -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Compatible partial base isomorphisms and the retained field identify
a measured initial fibre with a fibre in any nonempty final neighbourhood. -/
theorem s2e_c1_normalization_has_measured_fibre
    {K : Type} [Field K] (m : ℕ) (B B₀ : Over (Spec ↧ℂ))
    [IsIntegral B.left] [LocallyOfFiniteType B.hom] [IsIntegral B₀.left]
    (f : Spec (CommRingCat.of K) ⟶ B.left) (g : Spec (CommRingCat.of K) ⟶ B₀.left)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    [QuasiCompact g] [QuasiSeparated g] [IsDominant g]
    (b : B ⟶ B₀) (hη : f ≫ b.left = g)
    (P : B.left.PartialIso B₀.left)
    (hP : P.iso.hom ≫ P.target.ι = P.source.ι ≫ b.left)
    (U : B.left.Opens) (hU : (U : Set B.left).Nonempty)
    (V₀ : B₀.left.Opens) (hV₀ : Dense (V₀ : Set B₀.left))
    (hcard : ∀ y : ComplexPoint B₀, y.underlying ∈ V₀ →
      Nat.card ((Point.map (s2b_normalizationMap B₀ g)) ⁻¹' {y}) = m) :
    ∃ y : ComplexPoint B, y.underlying ∈ U ∧
      Nat.card ((Point.map (s2b_normalizationMap B f)) ⁻¹' {y}) = m := by
  have hPover : P.IsOver b.left (𝟙 B₀.left) := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hP
  obtain ⟨Q, hQU, hQV, hQover⟩ := s2e_c1_partial_iso_within_dense_opens P b.left (𝟙 B₀.left)
    hPover U (U.isOpen.dense hU) V₀ hV₀
  have hQ : Q.iso.hom ≫ Q.target.ι = Q.source.ι ≫ b.left := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hQover
  haveI : Nonempty Q.source := Q.dense_source.nonempty.to_subtype
  obtain ⟨fU, hfqc, hfqs, hf⟩ := s2e_c1_generic_source_lift_to_open B.left f Q.source Q.dense_source.nonempty
  obtain ⟨gV, hgqc, hgqs, hg⟩ := s2e_c1_generic_source_lift_to_open B₀.left g Q.target Q.dense_target.nonempty
  haveI := hfqc
  haveI := hfqs
  haveI := hgqc
  haveI := hgqs
  let e : openScheme B Q.source ≅ openScheme B₀ Q.target := Over.isoMk Q.iso (by
    change Q.iso.hom ≫ (Q.target.ι ≫ B₀.hom) = Q.source.ι ≫ B.hom
    rw [← Category.assoc, hQ, Category.assoc, Over.w b])
  have he : fU ≫ e.hom.left = gV := by
    change fU ≫ Q.iso.hom = gV
    rw [← cancel_mono Q.target.ι, Category.assoc, hQ, ← Category.assoc, hf, hη, hg]
  obtain ⟨E, hE⟩ := s2e_c1_normalization_open_over_iso B B₀ f g Q.source Q.target e fU gV hf hg he
  exact s2e_c1_good_fibre_of_open_cover_iso m (s2b_normalizationOver B f) B
    (s2b_normalizationOver B₀ g) B₀ (s2b_normalizationMap B f) (s2b_normalizationMap B₀ g)
    U Q.source V₀ Q.target hQU hQV e E hE hcard

end HodgeLean.Foundations.Program
