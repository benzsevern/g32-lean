import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence

/-! Primitive preimages from an equivariant relative comparison. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_relative_absolute_naturality
    (K : Type) [CommRing K] {X Y : TopPair.{0}} (f : X ⟶ Y)
    (n : ℕ) (u : RelativeCohomology K Y n) :
    relativeCohomologyToAbsolute K X n (relativeCohomologyMap K n f u) =
      cohomologyMap K n (TopPair.Hom.fst f) (relativeCohomologyToAbsolute K Y n u) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := K) f)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun t => HomologicalComplex.homologyMap t n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact ConcreteCategory.congr_hom hhom u

lemma persistence_primitive_preimage_of_relative_comparison
    (K : Type) [Field K] [CharZero K] (X Y : TopPair.{0})
    (dX : X ⟶ X) (dY : Y ⟶ Y) (f : X ⟶ Y)
    (hf : dX ≫ f = f ≫ dY) (m : ℕ) (hm : 0 < m)
    (hdX : End.of (TopPair.Hom.fst dX) ^ m = 1)
    (hdY : End.of (TopPair.Hom.fst dY) ^ m = 1)
    (ζ : K)
    (hX : ∀ n (v : Cohomology K X.snd n),
      cohomologyMap K n (TopPair.Hom.snd dX) v = ζ • v → v = 0)
    (hY : ∀ n (v : Cohomology K Y.snd n),
      cohomologyMap K n (TopPair.Hom.snd dY) v = ζ • v → v = 0)
    (n : ℕ) (hbij : Function.Bijective (relativeCohomologyMap K n f))
    (v : Cohomology K X.fst n)
    (hv : cohomologyMap K n (TopPair.Hom.fst dX) v = ζ • v) :
    ∃! u : Cohomology K Y.fst n,
      cohomologyMap K n (TopPair.Hom.fst dY) u = ζ • u ∧
      cohomologyMap K n (TopPair.Hom.fst f) u = v := by
  have hrel (u : RelativeCohomology K Y n) :
      relativeCohomologyMap K n dX (relativeCohomologyMap K n f u) =
      relativeCohomologyMap K n f (relativeCohomologyMap K n dY u) := by
    have h := congrArg (relativeCohomologyMap K n) hf
    rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at h
    exact LinearMap.congr_fun h u
  obtain ⟨x, hx, hxu⟩ := persistence_pair_primitive_lift K X dX m hm hdX ζ hX n v hv
  obtain ⟨y, hy⟩ := hbij.surjective x
  have hye : relativeCohomologyMap K n dY y = ζ • y := by
    apply hbij.injective
    rw [← hrel, hy, hx.1, map_smul, hy]
  let u := relativeCohomologyToAbsolute K Y n y
  have hue : cohomologyMap K n (TopPair.Hom.fst dY) u = ζ • u := by
    rw [← persistence_relative_absolute_naturality, hye, map_smul]
  have huv : cohomologyMap K n (TopPair.Hom.fst f) u = v := by
    rw [← persistence_relative_absolute_naturality, hy, hx.2]
  refine ⟨u, ⟨hue, huv⟩, ?_⟩
  intro u' hu'
  obtain ⟨y', hy', _⟩ := persistence_pair_primitive_lift K Y dY m hm hdY ζ hY n u' hu'.1
  have hxy : relativeCohomologyMap K n f y' = x := by
    apply hxu
    constructor
    · rw [hrel, hy'.1, map_smul]
    · rw [persistence_relative_absolute_naturality, hy'.2, hu'.2]
  have hyy : y' = y := hbij.injective (hxy.trans hy.symm)
  rw [← hy'.2, hyy]

lemma persistence_preimage_of_unique_relative_lifts
    (K : Type) [CommRing K] (X Y : TopPair.{0})
    (dX : X ⟶ X) (dY : Y ⟶ Y) (f : X ⟶ Y)
    (hf : dX ≫ f = f ≫ dY) (ζ : K) (n : ℕ)
    (hbij : Function.Bijective (relativeCohomologyMap K n f))
    (hX : ∀ v : Cohomology K X.fst n,
      cohomologyMap K n (TopPair.Hom.fst dX) v = ζ • v →
      ∃! u : RelativeCohomology K X n,
        relativeCohomologyMap K n dX u = ζ • u ∧
        relativeCohomologyToAbsolute K X n u = v)
    (hY : ∀ v : Cohomology K Y.fst n,
      cohomologyMap K n (TopPair.Hom.fst dY) v = ζ • v →
      ∃! u : RelativeCohomology K Y n,
        relativeCohomologyMap K n dY u = ζ • u ∧
        relativeCohomologyToAbsolute K Y n u = v)
    (v : Cohomology K X.fst n)
    (hv : cohomologyMap K n (TopPair.Hom.fst dX) v = ζ • v) :
    ∃! u : Cohomology K Y.fst n,
      cohomologyMap K n (TopPair.Hom.fst dY) u = ζ • u ∧
      cohomologyMap K n (TopPair.Hom.fst f) u = v := by
  have hrel (u : RelativeCohomology K Y n) :
      relativeCohomologyMap K n dX (relativeCohomologyMap K n f u) =
      relativeCohomologyMap K n f (relativeCohomologyMap K n dY u) := by
    have h := congrArg (relativeCohomologyMap K n) hf
    rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at h
    exact LinearMap.congr_fun h u
  obtain ⟨x, hx, hxu⟩ := hX v hv
  obtain ⟨y, hy⟩ := hbij.surjective x
  have hye : relativeCohomologyMap K n dY y = ζ • y := by
    apply hbij.injective
    rw [← hrel, hy, hx.1, map_smul, hy]
  let u := relativeCohomologyToAbsolute K Y n y
  have hue : cohomologyMap K n (TopPair.Hom.fst dY) u = ζ • u := by
    rw [← persistence_relative_absolute_naturality, hye, map_smul]
  have huv : cohomologyMap K n (TopPair.Hom.fst f) u = v := by
    rw [← persistence_relative_absolute_naturality, hy, hx.2]
  refine ⟨u, ⟨hue, huv⟩, ?_⟩
  intro u' hu'
  obtain ⟨y', hy', _⟩ := hY u' hu'.1
  have hxy : relativeCohomologyMap K n f y' = x := by
    apply hxu
    constructor
    · rw [hrel, hy'.1, map_smul]
    · rw [persistence_relative_absolute_naturality, hy'.2, hu'.2]
  have hyy : y' = y := hbij.injective (hxy.trans hy.symm)
  rw [← hy'.2, hyy]

end HodgeLean.Foundations.QuotientDuality
