import HodgeLean.Foundations.BundleResolution.ChernEvenCapHomologyHelpers

/-! # Detecting quasi-isomorphisms of actual even cap comparisons

Nonpositive integer degrees use the actual cap homology maps. Positive
integer degrees use the relative homology below the cap degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_evenRelativeCapExtendedChainMap_quasiIso (P : TopPair) (k : ℕ)
    (φ : RelativeCochain ℚ P (2 * k)) (hφ : relativeCoboundary ℚ P (2 * k) φ = 0)
    (hcap : ∀ n, Function.Bijective (relativeCapHomologyMap ℚ P (2 * k) n φ hφ))
    (hlow : ∀ r : ℕ, r < 2 * k →
      IsZero (((relativeChainFunctor ℚ).obj P).homology r)) :
    QuasiIso (i1_evenRelativeCapExtendedChainMap P k φ hφ) := by
  let K := (relativeChainFunctor ℚ).obj P
  let L := ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj P.fst
  let F := i1_evenRelativeCapExtendedChainMap P k φ hφ
  apply (quasiIso_iff _).mpr
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  by_cases hi : i ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    let eK := K.extendHomologyIso (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
      (show (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).f (2 * k + n) = -(n : ℤ) by
        simp only [ComplexShape.embeddingUpIntLE_f]; omega)
    let eL := L.extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
      (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
        simp only [ComplexShape.embeddingUpIntLE_f]; omega)
    let t := ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P (2 * k) n φ hφ)
    haveI : IsIso t := (ConcreteCategory.isIso_iff_bijective t).mpr (hcap n)
    have hh : eK.inv ≫ homologyMap F (-(n : ℤ)) ≫ eL.hom = t :=
      i1_evenRelativeCapExtendedChainMap_homology P k n φ hφ
    have he : homologyMap F (-(n : ℤ)) = eK.hom ≫ t ≫ eL.inv := by
      rw [← hh]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    change IsIso (homologyMap F (-(n : ℤ)))
    rw [he]
    infer_instance
  · have hL : IsZero ((L.extend (ComplexShape.embeddingUpIntLE 0)).homology i) := by
      apply (exactAt_iff_isZero_homology _ _).mp
      exact L.extend_exactAt _ i (by
        intro n hn
        simp only [ComplexShape.embeddingUpIntLE_f] at hn
        omega)
    have hK : IsZero ((K.extend (ComplexShape.embeddingUpIntLE (2 * k : ℕ))).homology i) := by
      by_cases hp : i ≤ (2 * k : ℕ)
      · let r := (((2 * k : ℕ) : ℤ) - i).toNat
        have hr : (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).f r = i := by
          simp only [ComplexShape.embeddingUpIntLE_f]
          dsimp [r]
          omega
        exact (hlow r (by dsimp [r]; omega)).of_iso (K.extendHomologyIso _ hr)
      · apply (exactAt_iff_isZero_homology _ _).mp
        exact K.extend_exactAt _ i (by
          intro n hn
          simp only [ComplexShape.embeddingUpIntLE_f] at hn
          omega)
    exact hK.isIso hL _

end HodgeLean.Foundations.BundleResolution
