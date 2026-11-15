import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineSupIdealEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalEpiNatIso
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # Global epic ideal comparison from the intersection equation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The supplied intersection kernel equation gives epic global ideal comparison. -/
lemma unionConormal_idealMap_epi_of_sup
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) [IsClosedImmersion f] (g : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (hsup : (i' ≫ f).ker = i.ker ⊔ f.ker) :
    Epi (idealPullbackMap i i' f g h) := by
  apply unionConormal_epi_of_open_neighborhoods
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := W)
    (U := ⊤) (x := f x) (show f x ∈ (⊤ : W.Opens) from trivial)
  let V := f ⁻¹ᵁ U
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hU.preimage f
  have hp : i' ⁻¹ᵁ V = g ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    change i' ⁻¹ᵁ (f ⁻¹ᵁ U) = g ⁻¹ᵁ (i ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← h, Scheme.Hom.comp_preimage]
  let gU := g.resLE (i ⁻¹ᵁ U) (i' ⁻¹ᵁ V) hp.le
  have hgU : gU ≫ (i ⁻¹ᵁ U).ι = (i' ⁻¹ᵁ V).ι ≫ g := g.resLE_comp_ι hp.le
  have hUmap : gU ≫ (i ∣_ U) = (i' ∣_ V) ≫ (f ∣_ U) := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hgU,
      Category.assoc, h, ← Category.assoc, ← morphismRestrict_ι i' V]
    simp only [Category.assoc]
    rw [morphismRestrict_ι f U]
  have hsupU : ((i' ∣_ V) ≫ (f ∣_ U)).ker = (i ∣_ U).ker ⊔ (f ∣_ U).ker := by
    have he := unionConormal_restrict_kernel_sup (i' ≫ f) i f hsup U
    simpa only [morphismRestrict_comp, V] using he
  haveI : Epi (idealPullbackMap (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU hUmap) :=
    unionConormal_idealMap_epi_of_affine_sup (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU hUmap hsupU
  have h₀ : (i ⁻¹ᵁ U).ι ≫ i = (i ∣_ U) ≫ U.ι := (morphismRestrict_ι i U).symm
  have h₁ : (i' ⁻¹ᵁ V).ι ≫ i' = (i' ∣_ V) ≫ V.ι := (morphismRestrict_ι i' V).symm
  have hNew : (gU ≫ (i ⁻¹ᵁ U).ι) ≫ i = (i' ∣_ V) ≫ ((f ∣_ U) ≫ U.ι) := by
    rw [Category.assoc, h₀, ← Category.assoc, hUmap, Category.assoc]
  have hOld : ((i' ⁻¹ᵁ V).ι ≫ g) ≫ i = (i' ∣_ V) ≫ (V.ι ≫ f) := by
    rw [Category.assoc, h, ← Category.assoc, h₁, Category.assoc]
  haveI : IsIso (idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι h₀) :=
    idealPullbackMap_open_isIso i U
  haveI : Epi (idealPullbackMap i (i' ∣_ V) ((f ∣_ U) ≫ U.ι)
      (gU ≫ (i ⁻¹ᵁ U).ι) hNew) :=
    unionConormal_idealMap_comp_epi i (i ∣_ U) (i' ∣_ V) U.ι (f ∣_ U)
      (i ⁻¹ᵁ U).ι gU h₀ hUmap hNew
  haveI : Epi (idealPullbackMap i (i' ∣_ V) (V.ι ≫ f) ((i' ⁻¹ᵁ V).ι ≫ g) hOld) :=
    unionConormal_idealMap_epi_congr i (i' ∣_ V) ((f ∣_ U) ≫ U.ι) (V.ι ≫ f)
      (morphismRestrict_ι f U) (gU ≫ (i ⁻¹ᵁ U).ι) ((i' ⁻¹ᵁ V).ι ≫ g) hNew hOld
  haveI : IsIso (idealPullbackMap i' (i' ∣_ V) V.ι (i' ⁻¹ᵁ V).ι h₁) :=
    idealPullbackMap_open_isIso i' V
  haveI := unionConormal_idealMap_map_epi_of_comp i i' (i' ∣_ V) f V.ι g
    (i' ⁻¹ᵁ V).ι h h₁ hOld
  exact ⟨V, hx, unionConormal_epi_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm (idealPullbackMap i i' f g h)⟩

end HodgeLean.Foundations.Program.G32Native
