import HodgeLean.Foundations.BundleThom.DirectedScalarFactorHelpers

/-! # Directed scalar coverage from actual rational generators

A quotient by the union of the directed ranges vanishes on every supplied generator.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- A directed family containing a jointly detecting family of scalar generators covers every scalar map to the target module.
Source: Hatcher, Algebraic Topology, §2.1, finite support of chains in directed unions. -/
theorem i1_scalarMap_factor_of_directed_generator_cover {ι τ : Type} [Nonempty ι]
    (V : ModuleCat ℚ) (L : ι → ModuleCat ℚ) (p : ∀ i, L i ⟶ V)
    (hdir : Directed (· ≤ ·) (fun i => LinearMap.range (p i).hom))
    (G : τ → (ModuleCat.of ℚ ℚ ⟶ V))
    (hgen : ∀ (M : ModuleCat ℚ) (f g : V ⟶ M),
      (∀ a, G a ≫ f = G a ≫ g) → f = g)
    (hcover : ∀ a, ∃ i, ∃ g : ModuleCat.of ℚ ℚ ⟶ L i, g ≫ p i = G a)
    (f : ModuleCat.of ℚ ℚ ⟶ V) :
    ∃ i, ∃ g : ModuleCat.of ℚ ℚ ⟶ L i, g ≫ p i = f := by
  let W : Submodule ℚ V := ⨆ i, LinearMap.range (p i).hom
  let q : V ⟶ ModuleCat.of ℚ (V ⧸ W) := ModuleCat.ofHom W.mkQ
  have hp (i : ι) : p i ≫ q = 0 := by
    apply ModuleCat.hom_ext
    ext x
    change W.mkQ (p i x) = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr
      ((le_iSup (fun j => LinearMap.range (p j).hom) i) ⟨x, rfl⟩)
  have hq : q = 0 := by
    apply hgen _ q 0
    intro a
    obtain ⟨i, g, hg⟩ := hcover a
    rw [← hg, Category.assoc, hp, comp_zero, comp_zero]
  have hW : W = ⊤ := by
    apply top_unique
    intro x _
    apply (Submodule.Quotient.mk_eq_zero W).mp
    exact ConcreteCategory.congr_hom hq x
  exact i1_scalarMap_factor_of_directed_ranges V L p hdir hW f

end HodgeLean.Foundations.BundleThom
