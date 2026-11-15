import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Partial isomorphisms along the specified base tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Specified open-base isomorphisms compose through a finite tower while
retaining the actual total base morphism. -/
theorem s2e_c1_partial_iso_tower
    (r : ℕ) (X : Fin (r + 1) → Scheme) (Y : Scheme)
    (f₀ : X 0 ⟶ Y) (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (P₀ : (X 0).PartialIso Y) (hP₀ : P₀.IsOver f₀ (𝟙 Y))
    (P : ∀ i : Fin r, (X i.succ).PartialIso (X i.castSucc))
    (hP : ∀ i : Fin r, (P i).iso.hom ≫ (P i).target.ι = (P i).source.ι ≫ b i) :
    ∀ i, ∃ Q : (X i).PartialIso Y,
      Q.IsOver (s2e_towerTotalMap X f₀ b i) (𝟙 Y) := by
  intro i
  induction i using Fin.induction with
  | zero => exact ⟨P₀, hP₀⟩
  | succ j ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨(P j).trans Q, ?_⟩
    apply Scheme.PartialIso.IsOver.trans ?_ hQ
    simpa only [Scheme.PartialIso.IsOver, s2e_towerTotalMap_succ, Category.assoc] using
      congrArg (fun f => f ≫ s2e_towerTotalMap X f₀ b j.castSucc) (hP j)

/-- A compatible partial isomorphism can be confined to prescribed dense
opens on both sides while retaining its base square. -/
theorem s2e_c1_partial_iso_within_dense_opens
    {X Y S : Scheme} (P : X.PartialIso Y) (sX : X ⟶ S) (sY : Y ⟶ S)
    (hP : P.IsOver sX sY) (U : X.Opens) (hU : Dense (U : Set X))
    (V : Y.Opens) (hV : Dense (V : Set Y)) :
    ∃ Q : X.PartialIso Y, Q.source ≤ U ∧ Q.target ≤ V ∧ Q.IsOver sX sY := by
  have hSU : Dense ((P.source ⊓ U : X.Opens) : Set X) :=
    P.dense_source.inter_of_isOpen_right hU U.isOpen
  let P₁ := P.restrictSource (P.source ⊓ U) hSU inf_le_left
  have hP₁ : P₁.IsOver sX sY := hP.restrictSource _ hSU inf_le_left
  have hTV : Dense ((P₁.target ⊓ V : Y.Opens) : Set Y) :=
    P₁.dense_target.inter_of_isOpen_right hV V.isOpen
  let Q := P₁.restrictTarget (P₁.target ⊓ V) hTV inf_le_left
  have hQS : Q.source ≤ P₁.source := by
    change P₁.source.ι ''ᵁ _ ≤ P₁.source
    apply le_trans (Scheme.Hom.image_le_opensRange _ _)
    exact le_of_eq (Scheme.Opens.opensRange_ι _)
  exact ⟨Q, hQS.trans inf_le_right, inf_le_right, hP₁.restrictTarget _ hTV inf_le_left⟩

end HodgeLean.Foundations.Program
