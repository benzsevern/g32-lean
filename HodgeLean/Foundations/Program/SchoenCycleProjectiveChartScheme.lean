import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual scheme products for standard projective charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The spectrum of the integral tensor product is the actual scheme product over the chosen terminal scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.3 and II.7. -/
def s2e_specTensorProductTerminalIso (R S : Type) [CommRing R] [CommRing S] :
    Spec (CommRingCat.of (R ⊗[ℤ] S)) ≅
      pullback (terminal.from (Spec (CommRingCat.of R)))
        (terminal.from (Spec (CommRingCat.of S))) := by
  let eZ : Spec (CommRingCat.of ℤ) ≅ ⊤_ Scheme :=
    specZIsTerminal.uniqueUpToIso terminalIsTerminal
  have h : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[ℤ] S))))
      (Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight : S →ₐ[ℤ] R ⊗[ℤ] S))))
      (terminal.from (Spec (CommRingCat.of R)))
      (terminal.from (Spec (CommRingCat.of S))) := by
    refine (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ S)))).of_iso
      (pullbackSpecIso ℤ R S) (Iso.refl _) (Iso.refl _) eZ ?_ ?_ ?_ ?_
    · simpa only [Iso.refl_hom, Category.comp_id] using (pullbackSpecIso_hom_fst' ℤ R S).symm
    · simpa only [Iso.refl_hom, Category.comp_id] using (pullbackSpecIso_hom_snd ℤ R S).symm
    · apply terminalIsTerminal.hom_ext
    · apply terminalIsTerminal.hom_ext
  exact h.isoPullback

/-- The first projection of the actual tensor-spectrum product is the structural map of the left tensor factor.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_specTensorProductTerminalIso_hom_fst
    (R S : Type) [CommRing R] [CommRing S] :
    (s2e_specTensorProductTerminalIso R S).hom ≫
      pullback.fst (terminal.from (Spec (CommRingCat.of R)))
        (terminal.from (Spec (CommRingCat.of S))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[ℤ] S))) := by
  dsimp only [s2e_specTensorProductTerminalIso]
  exact IsPullback.isoPullback_hom_fst _

/-- The second projection of the tensor-spectrum product is induced by the right tensor factor.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_specTensorProductTerminalIso_hom_snd
    (R S : Type) [CommRing R] [CommRing S] :
    (s2e_specTensorProductTerminalIso R S).hom ≫
      pullback.snd (terminal.from (Spec (CommRingCat.of R)))
        (terminal.from (Spec (CommRingCat.of S))) =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : S →ₐ[ℤ] R ⊗[ℤ] S))) := by
  dsimp only [s2e_specTensorProductTerminalIso]
  exact IsPullback.isoPullback_hom_snd _

end HodgeLean.Foundations.Program
