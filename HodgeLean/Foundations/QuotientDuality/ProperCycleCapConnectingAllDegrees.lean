import HodgeLean.Foundations.QuotientDuality.ProperCycleCapConnecting
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapTailNaturality

/-! # Original connecting maps through chain tails in every output degree -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original three-term models map to their actual degree-tail models at every output degree, retaining the canonical endpoint injection in degree zero.
Source: Mathlib, Algebra/Homology/ShortComplex/HomologicalComplex.lean, three-term chain models.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_sc_map
    (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (p : ℕ) (q : ℕ) :
    K.sc (p + q) ⟶ (K.restriction (properCycle_cap_tail_embedding p)).sc q :=
  match q with
  | 0 => properCycle_cap_tail_zero_sc_map K p
  | q + 1 => (properCycle_cap_tail_sc_iso K p q).hom

/-- The original homology comparison with a degree tail uses the actual endpoint map and the original positive-degree isomorphisms.
Source: Hatcher, Algebraic Topology, section 2.1, degree-tail cycles and boundaries.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_homology_map
    (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (p q : ℕ) :
    K.homology (p + q) ⟶ (K.restriction (properCycle_cap_tail_embedding p)).homology q :=
  ShortComplex.homologyMap (properCycle_cap_tail_sc_map K p q)

/-- Actual morphisms from chain tails intertwine the original connecting maps in every output degree, retaining the original endpoint comparison.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of connecting homomorphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_connecting
    (S T : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ))
    (hS : S.ShortExact) (hT : T.ShortExact) (p q : ℕ)
    (F : S.map ((properCycle_cap_tail_embedding p).restrictionFunctor (ModuleCat ℚ)) ⟶ T) :
    (properCycle_cap_tail_homology_iso S.X₃ p q).hom ≫
        HomologicalComplex.homologyMap F.τ₃ (q + 1) ≫ hT.δ (q + 1) q (by simp) =
      hS.δ (p + (q + 1)) (p + q) (by change (p + q) + 1 = p + (q + 1); omega) ≫
        properCycle_cap_tail_homology_map S.X₁ p q ≫
          HomologicalComplex.homologyMap F.τ₁ q := by
  let n := p + q
  letI := hS.mono_f
  letI := hS.epi_g
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (S.X₃.homologyπ (n + 1))).mp inferInstance z
  let x₃ := (S.X₃.iCycles (n + 1)).hom x
  have hx₃ : (S.X₃.d (n + 1) n).hom x₃ = 0 := by
    exact ConcreteCategory.congr_hom (S.X₃.iCycles_d (n + 1) n) x
  have hS' := hS.map (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) (n + 1))
  obtain ⟨x₂, hx₂⟩ := hS'.moduleCat_surjective_g x₃
  change (S.g.f (n + 1)).hom x₂ = x₃ at hx₂
  have hker : (S.g.f n).hom ((S.X₂.d (n + 1) n).hom x₂) = 0 := by
    have hh := ConcreteCategory.congr_hom (S.g.comm (n + 1) n).symm x₂
    change (S.g.f n).hom ((S.X₂.d (n + 1) n).hom x₂) =
      (S.X₃.d (n + 1) n).hom ((S.g.f (n + 1)).hom x₂) at hh
    exact hh.trans (by rw [hx₂]; exact hx₃)
  have he := (hS.map (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)).exact
  obtain ⟨x₁, hx₁⟩ := ((ShortComplex.moduleCat_exact_iff _).mp he) _ hker
  change (S.f.f n).hom x₁ = (S.X₂.d (n + 1) n).hom x₂ at hx₁
  let y₃ := (F.τ₃.f (q + 1)).hom x₃
  let y₂ := (F.τ₂.f (q + 1)).hom x₂
  let y₁ := (F.τ₁.f q).hom x₁
  have hy₃ : (T.X₃.d (q + 1) q).hom y₃ = 0 := by
    have hh := ConcreteCategory.congr_hom (F.τ₃.comm (q + 1) q) x₃
    change (T.X₃.d (q + 1) q).hom y₃ =
      (F.τ₃.f q).hom ((S.X₃.d (n + 1) n).hom x₃) at hh
    exact hh.trans (by rw [hx₃, map_zero])
  have hy₂ : (T.g.f (q + 1)).hom y₂ = y₃ := by
    have hh := ConcreteCategory.congr_hom (congrArg (fun m => m.f (q + 1)) F.comm₂₃) x₂
    change (T.g.f (q + 1)).hom y₂ = (F.τ₃.f (q + 1)).hom ((S.g.f (n + 1)).hom x₂) at hh
    exact hh.trans (congrArg (F.τ₃.f (q + 1)).hom hx₂)
  have hy₁ : (T.f.f q).hom y₁ = (T.X₂.d (q + 1) q).hom y₂ := by
    have hh := ConcreteCategory.congr_hom (congrArg (fun m => m.f q) F.comm₁₂) x₁
    change (T.f.f q).hom y₁ = (F.τ₂.f q).hom ((S.f.f n).hom x₁) at hh
    rw [hx₁] at hh
    exact hh.trans (ConcreteCategory.congr_hom (F.τ₂.comm (q + 1) q).symm x₂)
  have hδS := hS.δ_apply (n + 1) n (by simp) x₃ hx₃ x₂ hx₂ x₁ hx₁
    ((ComplexShape.down ℕ).next n) rfl
  have hδT := hT.δ_apply (q + 1) q (by simp) y₃ hy₃ y₂ hy₂ y₁ hy₁ ((ComplexShape.down ℕ).next q) rfl
  have hx : S.X₃.cyclesMk x₃ n (ChainComplex.next_nat_succ n) hx₃ = x := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles (n + 1))).mp inferInstance
    exact S.X₃.i_cyclesMk _ _ _ _
  rw [hx] at hδS
  change (hS.δ (n + 1) n (by simp)).hom ((S.X₃.homologyπ (n + 1)).hom x) =
    (S.X₁.homologyπ n).hom _ at hδS
  change (hT.δ (q + 1) q (by simp)).hom ((T.X₃.homologyπ (q + 1)).hom _) =
    (T.X₁.homologyπ q).hom _ at hδT
  let U := (properCycle_cap_tail_sc_iso S.X₃ p q).hom ≫
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (q + 1)).map F.τ₃
  let V := properCycle_cap_tail_sc_map S.X₁ p q ≫
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map F.τ₁
  have hU := properCycle_sc_homology_on_cycles S.X₃ T.X₃ (n + 1) (q + 1) U x
  have hV := properCycle_sc_homology_on_cycles S.X₁ T.X₁ n q V
    (S.X₁.cyclesMk x₁ ((ComplexShape.down ℕ).next n) rfl
      (hS.d_eq_zero_of_f_eq_d_apply (n + 1) n x₂ x₁ hx₁ _))
  have hUmid : U.τ₂ = F.τ₃.f (q + 1) := by
    apply ModuleCat.hom_ext
    ext c
    rfl
  have hVmid : V.τ₂ = F.τ₁.f q := by
    cases q <;> apply ModuleCat.hom_ext <;> ext c <;> rfl
  simp only [hUmid] at hU
  simp only [hVmid, S.X₁.i_cyclesMk] at hV
  have hUmap : ShortComplex.homologyMap U =
      (properCycle_cap_tail_homology_iso S.X₃ p q).hom ≫
        HomologicalComplex.homologyMap F.τ₃ (q + 1) := by
    dsimp only [U]
    rw [ShortComplex.homologyMap_comp]
    rfl
  have hVmap : ShortComplex.homologyMap V =
      properCycle_cap_tail_homology_map S.X₁ p q ≫
        HomologicalComplex.homologyMap F.τ₁ q := by
    dsimp only [V]
    rw [ShortComplex.homologyMap_comp]
    rfl
  rw [← Category.assoc, ← hUmap, ← hVmap]
  change (hT.δ (q + 1) q (by simp)).hom
      ((ShortComplex.homologyMap U).hom ((S.X₃.homologyπ (n + 1)).hom x)) =
    (ShortComplex.homologyMap V).hom
      ((hS.δ (n + 1) n (by simp)).hom ((S.X₃.homologyπ (n + 1)).hom x))
  erw [hU, hδS, hV]
  have hi₁ := S.X₁.i_cyclesMk x₁ ((ComplexShape.down ℕ).next n) rfl
    (hS.d_eq_zero_of_f_eq_d_apply (n + 1) n x₂ x₁ hx₁ _)
  change (S.X₁.iCycles n).hom _ = x₁ at hi₁
  simp only [hi₁]
  exact hδT

/-- The original homology comparison with a chain tail is natural in all degrees, including the actual endpoint injection.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality of homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_homology_map_naturality
    {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap f (p + q) ≫ properCycle_cap_tail_homology_map L p q =
      properCycle_cap_tail_homology_map K p q ≫
        HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f (properCycle_cap_tail_embedding p)) q := by
  cases q with
  | zero => exact properCycle_cap_tail_zero_homology_naturality f p
  | succ q => exact properCycle_cap_tail_homology_naturality f p q

end HodgeLean.Foundations.QuotientDuality
