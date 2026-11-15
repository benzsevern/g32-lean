import HodgeLean.Adapters.CycleClassDivisorProductDefs

/-! # Open cochain obligation for the supported product
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
open scoped Simplicial
namespace HodgeLean.Adapters

private theorem ccm13_smallCochain_ext {R : Type} [CommRing R] {ι : Type}
    {Y : TopCat.{0}} {U : ι → Set Y} {n : ℕ}
    (phi psi : SmallCochain (R := R) Y U n)
    (h : ∀ sigma : (coverSmallSingularSubcomplex Y U : SSet) _⦋n⦌,
      phi (chainOfSimplex R sigma) = psi (chainOfSimplex R sigma)) : phi = psi := by
  have hc : ModuleCat.ofHom phi = ModuleCat.ofHom psi := by
    apply SSet.chainComplex_hom_ext
    intro sigma
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hi : ((coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
        (R := ModuleCat.of R R) sigma).hom a = a • chainOfSimplex R sigma := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change phi (((coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
      (R := ModuleCat.of R R) sigma).hom a) =
        psi (((coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
          (R := ModuleCat.of R R) sigma).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

theorem ccm13_relativeCupLift_small_zero_aux (Y : TopCat.{0})
    (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    smallCochainRestriction Y (ccm13_complementFamily Y S T) (p + q)
      (ccm13_relativeCupLift Y S T p q u v) = 0 := by
  let phi : Cochain ℚ (TopCat.toSSet.obj Y) p :=
    relativeCochainToAbsolute ℚ (TopPair.ofSubset Sᶜ) p u
  let psi : Cochain ℚ (TopCat.toSSet.obj Y) q :=
    relativeCochainToAbsolute ℚ (TopPair.ofSubset Tᶜ) q v
  change smallCochainRestriction Y (ccm13_complementFamily Y S T) (p + q)
    (cupCochain Y p q phi psi) = 0
  rw [smallCochainRestriction_cup]
  apply ccm13_smallCochain_ext
  intro σ
  rw [smallCupCochain_apply_simplex]
  unfold smallCochainRestriction
  simp_rw [cochainMap_apply, chainOfSimplex_map]
  simp only [LinearMap.zero_apply]
  obtain ⟨b, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
      (ccm13_complementFamily Y S T) σ.1).mp σ.2
  cases b with
  | false =>
      change (TopCat.toSSet.obj (TopPair.ofSubset Sᶜ).snd) _⦋p + q⦌ at y
      change (TopCat.toSSet.map (TopPair.ofSubset Sᶜ).map).app _ y = σ.1 at hy
      have hfront : frontFace (TopCat.toSSet.obj Y) σ.1 =
          (TopCat.toSSet.map (TopPair.ofSubset Sᶜ).map).app _
            (frontFace (TopCat.toSSet.obj (TopPair.ofSubset Sᶜ).snd) y) := by
        rw [← hy]
        rfl
      have hz := cochainMap_relativeCochainToAbsolute_eq_zero ℚ
        (TopPair.ofSubset Sᶜ) p u
      have heval := LinearMap.congr_fun hz
        (chainOfSimplex ℚ (frontFace (TopCat.toSSet.obj (TopPair.ofSubset Sᶜ).snd) y))
      simp only [cochainMap_apply, LinearMap.zero_apply] at heval
      rw [chainOfSimplex_map] at heval
      change phi
          (chainOfSimplex ℚ (frontFace
            (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) σ).1) * _ = 0
      have hfront' : (frontFace
          (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) σ).1 =
          (TopCat.toSSet.map (topologicalSubsetInclusion Y (Set.compl S))).app _
            (frontFace (TopCat.toSSet.obj (TopCat.of (Set.compl S))) y) := hfront
      rw [hfront']
      change phi _ = 0 at heval
      have heval' : phi (chainOfSimplex ℚ
          ((TopCat.toSSet.map (topologicalSubsetInclusion Y (Set.compl S))).app _
            (frontFace (TopCat.toSSet.obj (TopCat.of (Set.compl S))) y))) = 0 := heval
      rw [heval', zero_mul]
  | true =>
      change (TopCat.toSSet.obj (TopPair.ofSubset Tᶜ).snd) _⦋p + q⦌ at y
      change (TopCat.toSSet.map (TopPair.ofSubset Tᶜ).map).app _ y = σ.1 at hy
      have hback : backFace (TopCat.toSSet.obj Y) σ.1 =
          (TopCat.toSSet.map (TopPair.ofSubset Tᶜ).map).app _
            (backFace (TopCat.toSSet.obj (TopPair.ofSubset Tᶜ).snd) y) := by
        rw [← hy]
        rfl
      have hz := cochainMap_relativeCochainToAbsolute_eq_zero ℚ
        (TopPair.ofSubset Tᶜ) q v
      have heval := LinearMap.congr_fun hz
        (chainOfSimplex ℚ (backFace (TopCat.toSSet.obj (TopPair.ofSubset Tᶜ).snd) y))
      simp only [cochainMap_apply, LinearMap.zero_apply] at heval
      rw [chainOfSimplex_map] at heval
      change _ * psi
          (chainOfSimplex ℚ (backFace
            (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) σ).1) = 0
      have hback' : (backFace
          (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) σ).1 =
          (TopCat.toSSet.map (topologicalSubsetInclusion Y (Set.compl T))).app _
            (backFace (TopCat.toSSet.obj (TopCat.of (Set.compl T))) y) := hback
      rw [hback']
      change psi _ = 0 at heval
      have heval' : psi (chainOfSimplex ℚ
          ((TopCat.toSSet.map (topologicalSubsetInclusion Y (Set.compl T))).app _
            (backFace (TopCat.toSSet.obj (TopCat.of (Set.compl T))) y))) = 0 := heval
      rw [heval', mul_zero]

end HodgeLean.Adapters
