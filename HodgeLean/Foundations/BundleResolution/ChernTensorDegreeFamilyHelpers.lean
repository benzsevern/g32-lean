import HodgeLean.Foundations.Singular.TensorDegreeMaps

/-! # Degreewise linear families on actual total tensor chains

These maps require no compatibility with differentials. They allow
degreewise splittings to be transported to the actual total tensor groups.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory MonoidalCategory
namespace HodgeLean.Foundations.BundleResolution

variable (K K' L : ChainComplex (ModuleCat ℚ) ℕ)

def i1_tensorDegreeMapLeft (f : ∀ p, K.X p →ₗ[ℚ] K'.X p) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ⟶ (HomologicalComplex.tensorObj K' L).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun p q hpq => (ModuleCat.ofHom (f p) ▷ L.X q) ≫
      HomologicalComplex.ιTensorObj K' L p q n hpq)

theorem i1_tensorDegreeMapLeft_inclusion (f : ∀ p, K.X p →ₗ[ℚ] K'.X p)
    (p q n : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n hpq ≫ i1_tensorDegreeMapLeft K K' L f n =
      (ModuleCat.ofHom (f p) ▷ L.X q) ≫ HomologicalComplex.ιTensorObj K' L p q n hpq := by
  unfold i1_tensorDegreeMapLeft
  rw [HomologicalComplex.ι_mapBifunctorDesc]

theorem i1_tensorDegreeMapLeft_comp (K'' : ChainComplex (ModuleCat ℚ) ℕ)
    (f : ∀ p, K.X p →ₗ[ℚ] K'.X p) (g : ∀ p, K'.X p →ₗ[ℚ] K''.X p) (n : ℕ) :
    i1_tensorDegreeMapLeft K K' L f n ≫ i1_tensorDegreeMapLeft K' K'' L g n =
      i1_tensorDegreeMapLeft K K'' L (fun p => (g p).comp (f p)) n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc, i1_tensorDegreeMapLeft_inclusion, Category.assoc,
    i1_tensorDegreeMapLeft_inclusion, i1_tensorDegreeMapLeft_inclusion,
    ← Category.assoc, ← comp_whiskerRight]
  rfl

theorem i1_tensorDegreeMapLeft_id (n : ℕ) :
    i1_tensorDegreeMapLeft K K L (fun _ => LinearMap.id) n =
      𝟙 ((HomologicalComplex.tensorObj K L).X n) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [i1_tensorDegreeMapLeft_inclusion]
  change (𝟙 (K.X p) ▷ L.X q) ≫ _ = _
  rw [id_whiskerRight, Category.id_comp, Category.comp_id]

theorem i1_tensorDegreeMapLeft_add
    (f g : ∀ p, K.X p →ₗ[ℚ] K'.X p) (n : ℕ) :
    i1_tensorDegreeMapLeft K K' L (fun p => f p + g p) n =
      i1_tensorDegreeMapLeft K K' L f n + i1_tensorDegreeMapLeft K K' L g n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [Preadditive.comp_add, i1_tensorDegreeMapLeft_inclusion,
    i1_tensorDegreeMapLeft_inclusion, i1_tensorDegreeMapLeft_inclusion]
  change ((ModuleCat.ofHom (f p) + ModuleCat.ofHom (g p)) ▷ L.X q) ≫ _ = _
  rw [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

end HodgeLean.Foundations.BundleResolution
