import HodgeLean.Foundations.Program.G32Native.PairedC3SmoothRegularCharts

/-! # Regular equations after an ambient open immersion -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Pulling a smooth subscheme back along an ambient open immersion retains
regular affine equations for the actual ideal.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem paired_c3_open_regular_chart
    {K : Type} [Field K] [PerfectField K] {X Y : Scheme.{0}}
    (p : Y ⟶ Spec (.of K)) (g : X ⟶ Y) [IsOpenImmersion g]
    (I : Y.IdealSheafData) (n k : ℕ)
    [SmoothOfRelativeDimension (n + k) p]
    [SmoothOfRelativeDimension n (I.subschemeι ≫ p)]
    (x : X) (hx : g x ∈ I.support) :
    ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X) (_ : IsOpenImmersion j),
      x ∈ j.opensRange ∧ ∃ f : Fin k → A,
        RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          (((I.comap g).comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f) := by
  let L := I.comap g
  let e := I.comapIso g
  let h : L.subscheme ⟶ I.subscheme := e.hom ≫ pullback.snd g I.subschemeι
  have hh : h ≫ I.subschemeι = L.subschemeι ≫ g := by
    dsimp only [h]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  letI : IsOpenImmersion h := by dsimp only [h]; infer_instance
  letI : SmoothOfRelativeDimension (n + k) (g ≫ p) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + (n + k)) (g ≫ p))
  letI : SmoothOfRelativeDimension ((n + k) - k) (L.subschemeι ≫ (g ≫ p)) := by
    rw [← Category.assoc, ← hh, Category.assoc]
    simpa only [zero_add, Nat.add_sub_cancel] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (h ≫ (I.subschemeι ≫ p)))
  apply paired_c3_smooth_regular_chart (g ≫ p) (n + k) k (by omega) L x
  rw [show L = I.comap g from rfl, Scheme.IdealSheafData.support_comap]
  exact hx

#print axioms paired_c3_open_regular_chart
end HodgeLean.Foundations.Program.G32Native
