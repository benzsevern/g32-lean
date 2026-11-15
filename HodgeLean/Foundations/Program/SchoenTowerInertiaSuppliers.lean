import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Analysis.Complex.Basic

/-! Retained tower composites and deck compatibility.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The composite of the retained transition maps from a tower stage to stage zero.
Source: Schoen (1988), §2, pp. 14–15, the successive base blowups. -/
def s2v_towerToInitial {r : ℕ} (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc) :
    ∀ i : Fin (r + 1), B i ⟶ B 0 :=
  Fin.induction (𝟙 (B 0)) (fun i u => b i ≫ u)

/-- Commutative retained transition squares give the square to the initial stage.
Source: Schoen (1988), §2, p. 15, the normalized tower over the base tower. -/
theorem s2v_towerToInitial_naturality {r : ℕ}
    (W B : Fin (r + 1) → Over (Spec ↧ℂ))
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (β : ∀ i, W i ⟶ B i)
    (hβ : ∀ i : Fin r, w i ≫ β i.castSucc = β i.succ ≫ b i)
    (i : Fin (r + 1)) :
    s2v_towerToInitial W w i ≫ β 0 = β i ≫ s2v_towerToInitial B b i := by
  induction i using Fin.induction with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ i ih =>
    change (w i ≫ s2v_towerToInitial W w i.castSucc) ≫ β 0 =
      β i.succ ≫ b i ≫ s2v_towerToInitial B b i.castSucc
    rw [Category.assoc, ih, ← Category.assoc, hβ i, Category.assoc]

/-- The retained tower-to-original projection intertwines the specified deck generators.
Source: Schoen (1988), §2, p. 15, compatibility of the lifted residual actions. -/
theorem s2v_towerToOriginal_deck {r : ℕ}
    (W : Fin (r + 1) → Over (Spec ↧ℂ))
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (d : ∀ i, W i ⟶ W i)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (W₀ : Over (Spec ↧ℂ)) (eW : W 0 ≅ W₀) (d₀ : W₀ ⟶ W₀)
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀) (i : Fin (r + 1)) :
    d i ≫ (s2v_towerToInitial W w i ≫ eW.hom) =
      (s2v_towerToInitial W w i ≫ eW.hom) ≫ d₀ := by
  have hs := s2v_towerToInitial_naturality W W w w d (fun j => (hdw j).symm) i
  rw [← Category.assoc, ← hs, Category.assoc, hdinit, ← Category.assoc]

end HodgeLean.Foundations.Program
