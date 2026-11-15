import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Integer extensions for degree-lowering chain comparisons

Extending the source at offset p retains its lower chain degrees while
placing the degree p+n to degree n comparison in integer degree -n.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

variable (K L : ChainComplex (ModuleCat ℚ) ℕ) (p : ℕ)

def i1_degreeLoweringExtendedComponent
    (f : ∀ n : ℕ, K.X (p + n) ⟶ L.X n) (i : ℤ) :
    (K.extend (ComplexShape.embeddingUpIntLE (p : ℤ))).X i ⟶
      (L.extend (ComplexShape.embeddingUpIntLE 0)).X i :=
  if hi : i ≤ 0 then
    (K.extendXIso (ComplexShape.embeddingUpIntLE (p : ℤ))
      (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + (-i).toNat) = i by
        simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom ≫ f (-i).toNat ≫
      (L.extendXIso (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f (-i).toNat = i by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv
  else 0

theorem i1_degreeLoweringExtendedComponent_neg
    (f : ∀ n : ℕ, K.X (p + n) ⟶ L.X n) (n : ℕ) :
    i1_degreeLoweringExtendedComponent K L p f (-(n : ℤ)) =
      (K.extendXIso (ComplexShape.embeddingUpIntLE (p : ℤ))
        (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + n) = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom ≫ f n ≫
      (L.extendXIso (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv := by
  cases n <;> rfl

def i1_degreeLoweringExtendedChainMap
    (f : ∀ n : ℕ, K.X (p + n) ⟶ L.X n)
    (hf : ∀ n : ℕ, f (n + 1) ≫ L.d (n + 1) n =
      K.d (p + (n + 1)) (p + n) ≫ f n) :
    K.extend (ComplexShape.embeddingUpIntLE (p : ℤ)) ⟶
      L.extend (ComplexShape.embeddingUpIntLE 0) where
  f := i1_degreeLoweringExtendedComponent K L p f
  comm' i j hij := by
    change i + 1 = j at hij
    by_cases hj : j ≤ 0
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      have hi : i = -((n + 1 : ℕ) : ℤ) := by omega
      subst i
      rw [i1_degreeLoweringExtendedComponent_neg,
        i1_degreeLoweringExtendedComponent_neg]
      rw [K.extend_d_eq (ComplexShape.embeddingUpIntLE (p : ℤ))
        (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + (n + 1)) =
          -((n + 1 : ℕ) : ℤ) by simp only [ComplexShape.embeddingUpIntLE_f]; omega)
        (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + n) = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega),
        L.extend_d_eq (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f (n + 1) = -((n + 1 : ℕ) : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)
        (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using congrArg
        (fun t => (K.extendXIso (ComplexShape.embeddingUpIntLE (p : ℤ))
          (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + (n + 1)) =
            -((n + 1 : ℕ) : ℤ) by simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom ≫
          t ≫ (L.extendXIso (ComplexShape.embeddingUpIntLE 0)
            (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
              simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv) (hf n)
    · exact (L.isZero_extend_X (ComplexShape.embeddingUpIntLE 0) j (by
        intro n hn
        simp only [ComplexShape.embeddingUpIntLE_f] at hn
        omega)).eq_of_tgt _ _

theorem i1_degreeLoweringExtendedChainMap_naturality
    (K' L' : ChainComplex (ModuleCat ℚ) ℕ) (a : K ⟶ K') (b : L ⟶ L')
    (f : ∀ n : ℕ, K.X (p + n) ⟶ L.X n)
    (g : ∀ n : ℕ, K'.X (p + n) ⟶ L'.X n)
    (hf : ∀ n, f (n + 1) ≫ L.d (n + 1) n = K.d (p + (n + 1)) (p + n) ≫ f n)
    (hg : ∀ n, g (n + 1) ≫ L'.d (n + 1) n = K'.d (p + (n + 1)) (p + n) ≫ g n)
    (h : ∀ n, a.f (p + n) ≫ g n = f n ≫ b.f n) :
    HomologicalComplex.extendMap a (ComplexShape.embeddingUpIntLE (p : ℤ)) ≫
        i1_degreeLoweringExtendedChainMap K' L' p g hg =
      i1_degreeLoweringExtendedChainMap K L p f hf ≫
        HomologicalComplex.extendMap b (ComplexShape.embeddingUpIntLE 0) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    dsimp only [HomologicalComplex.comp_f, i1_degreeLoweringExtendedChainMap]
    rw [i1_degreeLoweringExtendedComponent_neg, i1_degreeLoweringExtendedComponent_neg,
      HomologicalComplex.extendMap_f a (ComplexShape.embeddingUpIntLE (p : ℤ))
        (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + n) = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega),
      HomologicalComplex.extendMap_f b (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun t => (K.extendXIso (ComplexShape.embeddingUpIntLE (p : ℤ))
        (show (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + n) = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom ≫
        t ≫ (L'.extendXIso (ComplexShape.embeddingUpIntLE 0)
          (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
            simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv) (h n)
  · exact (L'.isZero_extend_X (ComplexShape.embeddingUpIntLE 0) i (by
      intro n hn
      simp only [ComplexShape.embeddingUpIntLE_f] at hn
      omega)).eq_of_tgt _ _

end HodgeLean.Foundations.BundleResolution
