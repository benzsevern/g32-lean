import HodgeLean.Foundations.QuotientDuality.ProperCycleCapTailZero
import Mathlib.Algebra.Homology.ConcreteCategory

/-! # Connecting maps on the actual chain-tail cap models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Three-term homology maps carry the original cycle representative to its literal middle-component image.
Source: Mathlib, Algebra/Homology/ConcreteCategory.lean, cycle representatives.
HC no distance; AV milestone no distance. -/
lemma properCycle_sc_homology_on_cycles
    (K L : ChainComplex (ModuleCat ℚ) ℕ) (i j : ℕ)
    (F : K.sc i ⟶ L.sc j) (x : K.cycles i) :
    (ShortComplex.homologyMap F).hom ((K.homologyπ i).hom x) =
      (L.homologyπ j).hom
        (L.cyclesMk (F.τ₂.hom ((K.iCycles i).hom x))
          ((ComplexShape.down ℕ).next j) rfl (by
            change ((K.iCycles i ≫ F.τ₂) ≫ (L.sc j).g).hom x = 0
            rw [Category.assoc, F.comm₂₃, ← Category.assoc]
            change (((K.sc i).iCycles ≫ (K.sc i).g) ≫ F.τ₃).hom x = 0
            rw [ShortComplex.iCycles_g, zero_comp]
            rfl)) := by
  have hn := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality F) x
  change (ShortComplex.homologyMap F).hom ((K.homologyπ i).hom x) =
    (L.homologyπ j).hom ((ShortComplex.cyclesMap F).hom x) at hn
  refine hn.trans ?_
  apply congrArg (L.homologyπ j).hom
  apply (ModuleCat.mono_iff_injective (L.iCycles j)).mp inferInstance
  have hi := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i F) x
  exact hi.trans (L.i_cyclesMk _ _ _ _).symm

/-- A morphism from an actual degree tail to a short exact chain sequence intertwines the original connecting map with the target connecting map, including the tail endpoint.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of connecting homomorphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_connecting_zero
    (S T : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (hS : S.ShortExact) (hT : T.ShortExact) (p : ℕ)
    (F : S.map ((properCycle_cap_tail_embedding p).restrictionFunctor (ModuleCat ℚ)) ⟶ T) :
    (properCycle_cap_tail_homology_iso S.X₃ p 0).hom ≫
        HomologicalComplex.homologyMap F.τ₃ 1 ≫ hT.δ 1 0 (by simp) =
      hS.δ (p + 1) p (by simp) ≫
        properCycle_cap_tail_zero_homology_map S.X₁ p ≫
          HomologicalComplex.homologyMap F.τ₁ 0 := by
  letI := hS.mono_f
  letI := hS.epi_g
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (S.X₃.homologyπ (p + 1))).mp inferInstance z
  let x₃ := (S.X₃.iCycles (p + 1)).hom x
  have hx₃ : (S.X₃.d (p + 1) p).hom x₃ = 0 := by
    exact ConcreteCategory.congr_hom (S.X₃.iCycles_d (p + 1) p) x
  have hS' := hS.map (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) (p + 1))
  obtain ⟨x₂, hx₂⟩ := hS'.moduleCat_surjective_g x₃
  change (S.g.f (p + 1)).hom x₂ = x₃ at hx₂
  have hker : (S.g.f p).hom ((S.X₂.d (p + 1) p).hom x₂) = 0 := by
    have hh := ConcreteCategory.congr_hom (S.g.comm (p + 1) p).symm x₂
    change (S.g.f p).hom ((S.X₂.d (p + 1) p).hom x₂) =
      (S.X₃.d (p + 1) p).hom ((S.g.f (p + 1)).hom x₂) at hh
    exact hh.trans (by rw [hx₂]; exact hx₃)
  have he := (hS.map (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) p)).exact
  obtain ⟨x₁, hx₁⟩ := ((ShortComplex.moduleCat_exact_iff _).mp he) _ hker
  change (S.f.f p).hom x₁ = (S.X₂.d (p + 1) p).hom x₂ at hx₁
  let y₃ := (F.τ₃.f 1).hom x₃
  let y₂ := (F.τ₂.f 1).hom x₂
  let y₁ := (F.τ₁.f 0).hom x₁
  have hy₃ : (T.X₃.d 1 0).hom y₃ = 0 := by
    have hh := ConcreteCategory.congr_hom (F.τ₃.comm 1 0) x₃
    change (T.X₃.d 1 0).hom y₃ =
      (F.τ₃.f 0).hom ((S.X₃.d (p + 1) p).hom x₃) at hh
    exact hh.trans (by rw [hx₃, map_zero])
  have hy₂ : (T.g.f 1).hom y₂ = y₃ := by
    have hh := ConcreteCategory.congr_hom (congrArg (fun m => m.f 1) F.comm₂₃) x₂
    change (T.g.f 1).hom y₂ = (F.τ₃.f 1).hom ((S.g.f (p + 1)).hom x₂) at hh
    exact hh.trans (congrArg (F.τ₃.f 1).hom hx₂)
  have hy₁ : (T.f.f 0).hom y₁ = (T.X₂.d 1 0).hom y₂ := by
    have hh := ConcreteCategory.congr_hom (congrArg (fun m => m.f 0) F.comm₁₂) x₁
    change (T.f.f 0).hom y₁ = (F.τ₂.f 0).hom ((S.f.f p).hom x₁) at hh
    rw [hx₁] at hh
    exact hh.trans (ConcreteCategory.congr_hom (F.τ₂.comm 1 0).symm x₂)
  have hδS := hS.δ_apply (p + 1) p (by simp) x₃ hx₃ x₂ hx₂ x₁ hx₁
    ((ComplexShape.down ℕ).next p) rfl
  have hδT := hT.δ_apply 1 0 (by simp) y₃ hy₃ y₂ hy₂ y₁ hy₁ 0 (by simp)
  have hx : S.X₃.cyclesMk x₃ p (ChainComplex.next_nat_succ p) hx₃ = x := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles (p + 1))).mp inferInstance
    exact S.X₃.i_cyclesMk _ _ _ _
  rw [hx] at hδS
  change (hS.δ (p + 1) p (by simp)).hom ((S.X₃.homologyπ (p + 1)).hom x) =
    (S.X₁.homologyπ p).hom _ at hδS
  change (hT.δ 1 0 (by simp)).hom ((T.X₃.homologyπ 1).hom _) =
    (T.X₁.homologyπ 0).hom _ at hδT
  let U := (properCycle_cap_tail_sc_iso S.X₃ p 0).hom ≫
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 1).map F.τ₃
  let V := properCycle_cap_tail_zero_sc_map S.X₁ p ≫
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map F.τ₁
  have hU := properCycle_sc_homology_on_cycles S.X₃ T.X₃ (p + 1) 1 U x
  have hV := properCycle_sc_homology_on_cycles S.X₁ T.X₁ p 0 V
    (S.X₁.cyclesMk x₁ ((ComplexShape.down ℕ).next p) rfl
      (hS.d_eq_zero_of_f_eq_d_apply (p + 1) p x₂ x₁ hx₁ _))
  have hUmid : U.τ₂ = F.τ₃.f 1 := by
    apply ModuleCat.hom_ext
    ext c
    rfl
  have hVmid : V.τ₂ = F.τ₁.f 0 := by
    apply ModuleCat.hom_ext
    ext c
    rfl
  simp only [hUmid] at hU
  simp only [hVmid, S.X₁.i_cyclesMk] at hV
  have hUmap : ShortComplex.homologyMap U =
      (properCycle_cap_tail_homology_iso S.X₃ p 0).hom ≫
        HomologicalComplex.homologyMap F.τ₃ 1 := by
    dsimp only [U]
    rw [ShortComplex.homologyMap_comp]
    rfl
  have hVmap : ShortComplex.homologyMap V =
      properCycle_cap_tail_zero_homology_map S.X₁ p ≫
        HomologicalComplex.homologyMap F.τ₁ 0 := by
    dsimp only [V]
    rw [ShortComplex.homologyMap_comp]
    rfl
  rw [← Category.assoc, ← hUmap, ← hVmap]
  change (hT.δ 1 0 (by simp)).hom
      ((ShortComplex.homologyMap U).hom ((S.X₃.homologyπ (p + 1)).hom x)) =
    (ShortComplex.homologyMap V).hom
      ((hS.δ (p + 1) p (by simp)).hom ((S.X₃.homologyπ (p + 1)).hom x))
  rw [hU, hδS, hV]
  have hi₁ := S.X₁.i_cyclesMk x₁ ((ComplexShape.down ℕ).next p) rfl
    (hS.d_eq_zero_of_f_eq_d_apply (p + 1) p x₂ x₁ hx₁ _)
  change (S.X₁.iCycles p).hom _ = x₁ at hi₁
  simp only [hi₁]
  exact hδT

end HodgeLean.Foundations.QuotientDuality
