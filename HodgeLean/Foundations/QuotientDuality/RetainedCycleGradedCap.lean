import HodgeLean.Foundations.QuotientDuality.RetainedCycleAmbientCapSheaf

noncomputable section
open CategoryTheory Limits
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Signed degree-lowering maps give the actual cap morphism in the three degrees ending at zero. -/
def retainedGradedCapShortComplexZero (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) :
    K.sc' (p + 1) p ((ComplexShape.down ℕ).next p) ⟶ K.sc' 1 0 0 := by
  let s : ℤ := (-1) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine { τ₁ := s • cap 1, τ₂ := cap 0, τ₃ := 0, comm₁₂ := ?_, comm₂₃ := ?_ }
  · change (s • cap 1) ≫ K.d 1 0 = K.d (p + 1) p ≫ cap 0
    rw [Preadditive.zsmul_comp, hd 0]
    change s • (s • (K.d (p + 1) p ≫ cap 0)) = _
    rw [smul_smul, hs, one_smul]
  · change cap 0 ≫ K.d 0 0 = K.d p ((ComplexShape.down ℕ).next p) ≫ 0
    rw [K.shape 0 0 (by simp), comp_zero, comp_zero]

/-- Signed degree-lowering maps give the actual cap morphism in three adjacent positive degrees. -/
def retainedGradedCapShortComplexSucc (K : ChainComplex C ℕ) (p q : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) :
    K.sc' (p + (q + 2)) (p + (q + 1)) (p + q) ⟶ K.sc' (q + 2) (q + 1) q := by
  let s : ℤ := (-1) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := s • cap (q + 2)
      τ₂ := cap (q + 1)
      τ₃ := s • cap q
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · change (s • cap (q + 2)) ≫ K.d (q + 2) (q + 1) =
      K.d (p + (q + 2)) (p + (q + 1)) ≫ cap (q + 1)
    rw [Preadditive.zsmul_comp, hd (q + 1)]
    change s • (s • (K.d (p + (q + 2)) (p + (q + 1)) ≫ cap (q + 1))) = _
    rw [smul_smul, hs, one_smul]
  · change cap (q + 1) ≫ K.d (q + 1) q =
      K.d (p + (q + 1)) (p + q) ≫ (s • cap q)
    rw [Preadditive.comp_zsmul]
    exact hd q

/-- Signed cap maps induce actual morphisms between the canonical homology short complexes. -/
def retainedGradedCapShortComplexMap (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) (q : ℕ) :
    K.sc (p + q) ⟶ K.sc q :=
  match q with
  | 0 =>
      (K.isoSc' (p + 1) p ((ComplexShape.down ℕ).next p)
        (ChainComplex.prev ℕ p) rfl).hom ≫
      retainedGradedCapShortComplexZero K p cap hd ≫
      (K.isoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).inv
  | q + 1 =>
      (K.isoSc' (p + (q + 2)) (p + (q + 1)) (p + q)
        (by rw [ChainComplex.prev]; omega)
        (by rw [show p + (q + 1) = (p + q) + 1 by omega,
          ChainComplex.next_nat_succ])).hom ≫
      retainedGradedCapShortComplexSucc K p q cap hd ≫
      (K.isoSc' (q + 2) (q + 1) q (by rw [ChainComplex.prev]; omega)
        (ChainComplex.next_nat_succ q)).inv

/-- The induced short-complex map keeps the exact original cap map in its middle degree. -/
theorem retained_graded_cap_short_complex_map_middle (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) (q : ℕ) :
    (retainedGradedCapShortComplexMap K p cap hd q).τ₂ = cap q := by
  cases q <;> simp [retainedGradedCapShortComplexMap,
    retainedGradedCapShortComplexZero, retainedGradedCapShortComplexSucc]
  all_goals exact (Category.id_comp _).trans (Category.comp_id _)

/-- Equality of middle maps gives equality of the induced maps on actual homology. -/
theorem retained_homology_map_eq_of_middle
    {S T : ShortComplex C} [S.HasHomology] [T.HasHomology]
    (f g : S ⟶ T) (h : f.τ₂ = g.τ₂) :
    ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  rw [← cancel_epi S.homologyπ, ← cancel_mono T.homologyι]
  simp only [Category.assoc]
  rw [ShortComplex.π_homologyMap_ι, ShortComplex.π_homologyMap_ι, h]

end HodgeLean.Foundations.QuotientDuality
