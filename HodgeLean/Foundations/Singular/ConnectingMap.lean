import HodgeLean.Foundations.Singular.MayerVietoris

/-!
# Connecting maps and degreewise operations

Connecting-map compatibility is proved directly from cocycle lifts, allowing
operations that shift degree. HC no distance; AV milestone no distance.
This is infrastructure for stage S4 and retires no stated hypothesis.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.Singular

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
/-- A degreewise operation commutes with connecting maps when it preserves the
two lifting equations. No morphism of whole cochain complexes is required.
Source: constructed here from Mathlib `ShortComplex.ShortExact.δ_eq`, the explicit
cocycle-lift construction of Hatcher, *Algebraic Topology*, §3.1.
-/
theorem connectingMap_degreewise
    (S T : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ))
    (hS : S.ShortExact) (hT : T.ShortExact) (n m : ℕ)
    (a : S.X₃.sc n ⟶ T.X₃.sc m)
    (b : S.X₂.X n ⟶ T.X₂.X m)
    (b' : S.X₂.X (n + 1) ⟶ T.X₂.X (m + 1))
    (c : S.X₁.sc (n + 1) ⟶ T.X₁.sc (m + 1))
    (hg : b ≫ T.g.f m = S.g.f n ≫ a.τ₂)
    (hf : c.τ₂ ≫ T.f.f (m + 1) = S.f.f (n + 1) ≫ b')
    (hd : b ≫ T.X₂.d m (m + 1) = S.X₂.d n (n + 1) ≫ b') :
    ShortComplex.homologyMap a ≫ hT.δ m (m + 1) (by simp) =
      hS.δ n (n + 1) (by simp) ≫ ShortComplex.homologyMap c := by
  dsimp only [sc, shortComplexFunctor, shortComplexFunctor'] at a c
  letI := hS.epi_g
  letI := hS.mono_f
  let x₃ := S.X₃.iCycles n
  let x₂ := Projective.factorThru x₃ (S.g.f n)
  have hx₂ : x₂ ≫ S.g.f n = x₃ := Projective.factorThru_comp _ _
  have hx₃ : x₃ ≫ S.X₃.d n (n + 1) = 0 := S.X₃.iCycles_d _ _
  have he : (S.map (eval (ModuleCat ℚ) (ComplexShape.up ℕ) (n + 1))).Exact :=
    ((shortExact_iff_degreewise_shortExact S).mp hS (n + 1)).exact
  letI : Mono (S.map (eval (ModuleCat ℚ) (ComplexShape.up ℕ) (n + 1))).f :=
    ((shortExact_iff_degreewise_shortExact S).mp hS (n + 1)).mono_f
  have hk : (x₂ ≫ S.X₂.d n (n + 1)) ≫ S.g.f (n + 1) = 0 := by
    rw [Category.assoc, ← S.g.comm, ← Category.assoc, hx₂, hx₃]
  let x₁ := he.lift (x₂ ≫ S.X₂.d n (n + 1)) hk
  have hx₁ : x₁ ≫ S.f.f (n + 1) = x₂ ≫ S.X₂.d n (n + 1) := he.lift_f _ _
  have hc₁ : x₁ ≫ S.X₁.d (n + 1) (n + 2) = 0 := by
    rw [← cancel_mono (S.f.f (n + 2)), Category.assoc, ← S.f.comm,
      ← Category.assoc, hx₁, Category.assoc, d_comp_d, comp_zero, zero_comp]
  have ha : (x₃ ≫ a.τ₂) ≫ T.X₃.d m (m + 1) = 0 := by
    change ((S.X₃.sc n).iCycles ≫ a.τ₂) ≫ T.X₃.d m (m + 1) = 0
    rw [← ShortComplex.cyclesMap_i, Category.assoc]
    change ShortComplex.cyclesMap a ≫ (T.X₃.iCycles m ≫ T.X₃.d m (m + 1)) = 0
    rw [iCycles_d, comp_zero]
  have hb : (x₂ ≫ b) ≫ T.g.f m = x₃ ≫ a.τ₂ := by
    rw [Category.assoc, hg, ← Category.assoc, hx₂]
  have hc : (x₁ ≫ c.τ₂) ≫ T.f.f (m + 1) =
      (x₂ ≫ b) ≫ T.X₂.d m (m + 1) := by
    rw [Category.assoc, hf, ← Category.assoc, hx₁, Category.assoc,
      Category.assoc, hd]
  have hs := hS.δ_eq n (n + 1) (by simp) x₃ hx₃ x₂ hx₂ x₁ hx₁ (n + 2) (by simp)
  have ht := hT.δ_eq m (m + 1) (by simp) (x₃ ≫ a.τ₂) ha
    (x₂ ≫ b) hb (x₁ ≫ c.τ₂) hc (m + 2) (by simp)
  have hl : S.X₃.liftCycles x₃ (n + 1) (by simp) hx₃ = 𝟙 _ := by
    apply (cancel_mono (S.X₃.iCycles n)).mp
    simp [x₃]
  rw [hl, Category.id_comp] at hs
  apply (cancel_epi (S.X₃.homologyπ n)).mp
  change (S.X₃.sc n).homologyπ ≫ ShortComplex.homologyMap a ≫ _ = _
  rw [← Category.assoc, ShortComplex.homologyπ_naturality]
  have hla : ShortComplex.cyclesMap a =
      T.X₃.liftCycles (x₃ ≫ a.τ₂) (m + 1) (by simp) ha := by
    apply (cancel_mono (T.X₃.iCycles m)).mp
    simp only [liftCycles_i]
    exact ShortComplex.cyclesMap_i a
  rw [hla, Category.assoc]
  change T.X₃.liftCycles (x₃ ≫ a.τ₂) (m + 1) _ ha ≫ T.X₃.homologyπ m ≫ _ = _
  rw [ht, ← Category.assoc, hs]
  change _ = S.X₁.liftCycles x₁ (n + 2) _ _ ≫
    (S.X₁.sc (n + 1)).homologyπ ≫ ShortComplex.homologyMap c
  rw [ShortComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  apply (cancel_mono (T.X₁.iCycles (m + 1))).mp
  simp only [Category.assoc, liftCycles_i]
  exact (congrArg (fun t => t ≫ c.τ₂)
    (S.X₁.liftCycles_i x₁ (n + 2) (by simp) hc₁)).symm.trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => S.X₁.liftCycles x₁ (n + 2) (by simp) hc₁ ≫ t)
          (ShortComplex.cyclesMap_i c).symm))

#print axioms connectingMap_degreewise
end HodgeLean.Foundations.Singular
