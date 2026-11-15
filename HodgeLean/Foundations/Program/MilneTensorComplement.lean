import HodgeLean.Foundations.Program.MilneTensorCoefficients

noncomputable section
namespace HodgeLean.Foundations.Program
variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

def m1b_prodBilin (A : LinearMap.BilinForm ℂ U) (B : LinearMap.BilinForm ℂ W) :
    LinearMap.BilinForm ℂ (U × W) :=
  A.compl₁₂ (LinearMap.fst ℂ U W) (LinearMap.fst ℂ U W) +
    B.compl₁₂ (LinearMap.snd ℂ U W) (LinearMap.snd ℂ U W)

theorem m1b_prod_isometry (A : LinearMap.BilinForm ℂ U) (B : LinearMap.BilinForm ℂ W)
    (u : W →ₗ[ℂ] W) (hu : u ∈ m1b_isometries B) :
    (LinearMap.id.prodMap u) ∈ m1b_isometries (m1b_prodBilin A B) := by
  refine ⟨(Module.End.isUnit_iff _).mpr ?_, ?_⟩
  · obtain ⟨hi, hs⟩ := (Module.End.isUnit_iff _).mp hu.1
    constructor
    · intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      exact Prod.ext h₁ (hi h₂)
    · rintro ⟨x, y⟩
      obtain ⟨z, hz⟩ := hs y
      exact ⟨(x, z), Prod.ext rfl hz⟩
  · intro x y
    change A x.1 y.1 + B (u x.2) (u y.2) = A x.1 y.1 + B x.2 y.2
    rw [hu.2]

def m1b_splitCopies (r : ℕ) :
    ((Fin r → U) × (Fin r → W)) →ₗ[ℂ] (Fin r → U × W) where
  toFun x i := (x.1 i, x.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem m1b_complementCoefficient_isometry (A : LinearMap.BilinForm ℂ U)
    (B : LinearMap.BilinForm ℂ W) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → U × W) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin A B),
      ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (s : Finset (Fin n)) (x : Fin s.card → Fin r → U)
    (u : W →ₗ[ℂ] W) (hu : u ∈ m1b_isometries B) (y : Fin sᶜ.card → Fin r → W) :
    m1b_complementCoefficient (f.compLinearMap (fun _ => m1b_splitCopies r)) s x
      (fun i => m1b_copies r u (y i)) =
      m1b_complementCoefficient (f.compLinearMap (fun _ => m1b_splitCopies r)) s x y := by
  apply m1b_complementCoefficient_invariant
  intro v
  exact hf (LinearMap.id.prodMap u) (m1b_prod_isometry A B u hu)
    (fun i => m1b_splitCopies r (v i))

theorem m1b_prod_reflection_isometry (A : LinearMap.BilinForm ℂ U)
    (B : LinearMap.BilinForm ℂ W) :
    ((-LinearMap.id).prodMap LinearMap.id) ∈ m1b_isometries (m1b_prodBilin A B) := by
  refine ⟨(Module.End.isUnit_iff _).mpr ?_, ?_⟩
  · constructor
    · intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      exact Prod.ext (neg_injective h₁) h₂
    · rintro ⟨x, y⟩
      exact ⟨(-x, y), Prod.ext (neg_neg x) rfl⟩
  · intro x y
    change A (-x.1) (-y.1) + B x.2 y.2 = A x.1 y.1 + B x.2 y.2
    simp only [map_neg, LinearMap.neg_apply, neg_neg]

theorem m1b_complementCoefficient_isometry_odd (A : LinearMap.BilinForm ℂ U)
    (B : LinearMap.BilinForm ℂ W) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → U × W) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin A B),
      ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (s : Finset (Fin n)) (hs : Odd s.card) (x : Fin s.card → Fin r → U) :
    m1b_complementCoefficient (f.compLinearMap (fun _ => m1b_splitCopies r)) s x = 0 := by
  apply m1b_complementCoefficient_odd _ s hs x
  intro v
  exact hf ((-LinearMap.id).prodMap LinearMap.id) (m1b_prod_reflection_isometry A B)
    (fun i => m1b_splitCopies r (v i))

theorem m1b_complement_even_scale_expansion {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ)
    (hf : ∀ v : Fin n → U × W, f (fun i => (-(v i).1, (v i).2)) = f v)
    (t : ℂ) (x : Fin n → U) (y : Fin n → W) :
    f (fun i => (t • x i, y i)) = ∑ s : Finset (Fin n),
      (t ^ 2) ^ (s.card / 2) *
        m1b_complementCoefficient f s (fun j => x (s.orderEmbOfFin rfl j))
          (fun j => y (sᶜ.orderEmbOfFin rfl j)) := by
  rw [m1b_complementCoefficient_expansion]
  apply Finset.sum_congr rfl
  intro s _
  rw [m1b_complementCoefficient_smul]
  simp only [smul_apply, smul_eq_mul]
  by_cases he : Even s.card
  · congr 1
    rw [← pow_mul]
    congr 1
    obtain ⟨k, hk⟩ := he
    omega
  · rw [m1b_complementCoefficient_odd f s (Nat.not_even_iff_odd.mp he) _ hf]
    simp only [zero_apply, mul_zero]

end HodgeLean.Foundations.Program
