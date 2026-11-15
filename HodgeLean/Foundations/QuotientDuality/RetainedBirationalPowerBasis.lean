import HodgeLean.Foundations.Program.SchoenCycleC1RetainedWeightedNormalization

/-! Transport of the original Kummer power basis through the actual retained birational map. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_birational_kummer_power_basis
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (P : X.PartialIso Y)
    (hP : P.iso.hom ≫ P.target.ι = P.source.ι ≫ f)
    (L : Type) [Field L] (ηX : Spec (CommRingCat.of L) ⟶ X) [IsDominant ηX]
    (ηY : Spec (CommRingCat.of L) ⟶ Y) (hη : ηX ≫ f = ηY)
    (φY : Y.functionField →+* L)
    (hY : Spec.map (CommRingCat.ofHom φY) ≫ Y.fromSpecStalk (genericPoint Y) = ηY) :
    letI := φY.toAlgebra
    ∀ (B : PowerBasis Y.functionField L) (c : Y.functionField) (m : ℕ),
      B.gen ^ m = φY c →
      ∃ φX : X.functionField →+* L,
        Spec.map (CommRingCat.ofHom φX) ≫ X.fromSpecStalk (genericPoint X) = ηX ∧
        (letI := φX.toAlgebra
         let hg := s2e_c1_dominant_generic_point f
         let ψ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
           f.stalkMap (genericPoint X)).hom
         ∃ C : PowerBasis X.functionField L,
           C.gen = B.gen ∧ C.dim = B.dim ∧ C.gen ^ m = φX (ψ c)) := by
  letI := φY.toAlgebra
  intro B c m hroot
  obtain ⟨φX, _, hX⟩ := s2e_c1_field_source_generic_embedding L X ηX
  obtain ⟨F, hF, _⟩ := s2e_c1_partial_iso_rational_equivalence f P hP
  have hcomp := s2e_c1_generic_covering_field_square f L ηX ηY hη φX φY hX hY
  have hcompat : φX.comp F.toRingHom = φY := by rw [hF]; exact hcomp
  letI := φX.toAlgebra
  obtain ⟨C, hgen, hdimC, _⟩ := s2e_c1_power_basis_base_field_transport F
    (fun r => RingHom.congr_fun hcompat r) B
  refine ⟨φX, hX, C, hgen, hdimC, ?_⟩
  rw [hgen, hroot]
  exact (RingHom.congr_fun hcomp c).symm

#print axioms retained_birational_kummer_power_basis
end HodgeLean.Foundations.QuotientDuality
