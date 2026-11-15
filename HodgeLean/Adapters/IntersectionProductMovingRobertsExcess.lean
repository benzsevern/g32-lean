import HodgeLean.Adapters.IntersectionProductMovingRobertsScheme

/-! # Excess in terms of the homogeneous primes

For points `x`, `v` of an integral projective `X ⊂ ℙᴺ`, the excess `a3m_ExcessLE` of
`closure {x} ∩ closure {v}` is read off the affine cones: the generic points of the components of
the intersection are the relevant minimal primes over `P_x + P_v`
(`a3s_component_of_maximal`), and codimensions are `dim X - dim`, so excess at most `k` is the
bound `dim Y + dim X ≤ dim P_x + dim P_v + k` on cone dimensions (`a3s_excessLE_of_dim`,
`a3s_dim_of_excessLE`).

Source: Fulton, *Intersection Theory*, second edition, Example 11.4.1 (the excess `e(V, W)`);
Hartshorne, *Algebraic Geometry*, I, Exercise 2.6 and II, Exercise 3.20.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A maximal point of `closure {u} ∩ closure {v}` is the generic point of a component of the
scheme-theoretic intersection. -/
theorem a3s_component_of_maximal {X : Scheme} (u v w : X) (huw : u ⤳ w) (hvw : v ⤳ w)
    (hmax : ∀ z' : X, u ⤳ z' → v ⤳ z' → z' ⤳ w → z' = w) :
    ∃ w' : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
      (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w' = w ∧
      closure ({w'} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme := by
  set J := ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v
  have hrange : Set.range J.subschemeι = closure {u} ∩ closure {v} := by
    rw [Scheme.IdealSheafData.range_subschemeι, a3m_support_sup_primeIdeal]
  obtain ⟨w', hw'⟩ : w ∈ Set.range J.subschemeι :=
    hrange ▸ ⟨specializes_iff_mem_closure.1 huw, specializes_iff_mem_closure.1 hvw⟩
  have hemb := J.subschemeι.isClosedEmbedding
  refine ⟨w', hw', isIrreducible_singleton.closure, fun Z hZ hle => ?_⟩
  obtain ⟨z, hz⟩ := QuasiSober.sober hZ.closure isClosed_closure
  have hzw : z ⤳ w' := hz.specializes (subset_closure (hle (subset_closure rfl)))
  have hmem : J.subschemeι z ∈ closure {u} ∩ closure {v} := hrange ▸ ⟨z, rfl⟩
  have heq := hmax (J.subschemeι z) (specializes_iff_mem_closure.2 hmem.1)
    (specializes_iff_mem_closure.2 hmem.2) (hw' ▸ hzw.map J.subschemeι.continuous)
  have hzw' : z = w' := hemb.injective (heq.trans hw'.symm)
  calc Z ⊆ closure Z := subset_closure
    _ = closure {z} := hz.def.symm
    _ = closure {w'} := by rw [hzw']

section Excess

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

/-- Height, coheight and cone dimension of a point of `X` as natural numbers. -/
theorem a3s_nums (n : ℕ) (hn : Order.height (genericPoint X.left) = n) (x : X.left) :
    ∃ m c : ℕ, Order.height x = m ∧ Order.coheight x = c ∧ m + c = n ∧
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ (a3s_CX X).prime x) = (m + 1 : ℕ) := by
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg (X := X) x
  have hsum := a3m_height_add_coheight X x
  rw [hm, hn] at hsum
  have hc : Order.coheight x ≠ ⊤ := fun h => by
    rw [h, add_top] at hsum; exact ENat.top_ne_natCast n hsum
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hc
  rw [← hc] at hsum
  refine ⟨m, c, hm, hc.symm, by exact_mod_cast hsum, ?_⟩
  rw [← a3s_height_add_one X x, hm]
  push_cast
  rfl

/-- Excess bounds from dimension bounds of the cones. -/
theorem a3s_excessLE_of_dim (S : Set X.left) (x : X.left) (k : ℕ)
    (h : ∀ v ∈ S, ∀ Y : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ), Y.IsPrime →
      (a3s_CX X).prime x ⊔ (a3s_CX X).prime v ≤ Y → (∃ j, MvPolynomial.X j ∉ Y) →
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ Y) +
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) ≤
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ (a3s_CX X).prime x) +
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ (a3s_CX X).prime v) + k) :
    a3m_ExcessLE X.left S x k := by
  intro v hv w hw
  obtain ⟨hxw, hvw, -⟩ := a3m_component_spec x v w hw
  set z := (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left v).subschemeι w
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  have hb := h v hv ((a3s_CX X).prime z) inferInstance
    (sup_le ((a3s_CX X).prime_mono hxw) ((a3s_CX X).prime_mono hvw)) (a3s_relevant X z)
  obtain ⟨mx, cx, -, hcx, hx, hdx⟩ := a3s_nums X n hn x
  obtain ⟨mv, cv, -, hcv, hv', hdv⟩ := a3s_nums X n hn v
  obtain ⟨mz, cz, -, hcz, hz, hdz⟩ := a3s_nums X n hn z
  obtain ⟨mη, cη, hmη, -, -, hdη⟩ := a3s_nums X n hn (genericPoint X.left)
  have hη' : mη = n := by
    rw [hn] at hmη; exact_mod_cast hmη.symm
  change _ + ringKrullDim (_ ⧸ (a3s_CX X).prime (genericPoint X.left)) ≤ _ at hb
  rw [hdz, hdη, hdx, hdv] at hb
  have hb' : mz + 1 + (mη + 1) ≤ mx + 1 + (mv + 1) + k := by exact_mod_cast hb
  rw [hcx, hcv, hcz]
  exact_mod_cast (show cx + cv ≤ cz + k by omega)

/-- Dimension bounds of the cones from excess bounds. -/
theorem a3s_dim_of_excessLE (S : Set X.left) (u : X.left) (k : ℕ)
    (he : a3m_ExcessLE X.left S u k) (v : X.left) (hv : v ∈ S)
    (𝔶 : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ))
    (h𝔶 : 𝔶 ∈ ((a3s_CX X).prime u ⊔ (a3s_CX X).prime v).minimalPrimes)
    (hrel : ∃ j, MvPolynomial.X j ∉ 𝔶) :
    ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ 𝔶) +
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) ≤
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ (a3s_CX X).prime u) +
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ (a3s_CX X).prime v) + k := by
  have h𝔶p : 𝔶.IsPrime := h𝔶.1.1
  have hhom : 𝔶.IsHomogeneous (homogeneousSubmodule (Fin (a3s_N X + 1)) ℂ) :=
    a3m_isHomogeneous_of_mem_minimalPrimes
      (((a3s_CX X).isHomogeneous_prime u).sup ((a3s_CX X).isHomogeneous_prime v)) h𝔶
  have hu𝔶 : (a3s_CX X).prime u ≤ 𝔶 := le_sup_left.trans h𝔶.1.2
  have hv𝔶 : (a3s_CX X).prime v ≤ 𝔶 := le_sup_right.trans h𝔶.1.2
  obtain ⟨j, hj⟩ := hrel
  obtain ⟨w, hw⟩ := a3s_exists_point X 𝔶 hhom j hj ((a3s_IX_le X u).trans hu𝔶)
  have huw : u ⤳ w := (a3s_CX X).prime_le_iff.1 (hw ▸ hu𝔶)
  have hvw : v ⤳ w := (a3s_CX X).prime_le_iff.1 (hw ▸ hv𝔶)
  have hmax : ∀ z' : X.left, u ⤳ z' → v ⤳ z' → z' ⤳ w → z' = w := by
    intro z' huz hvz hzw
    have h1 : (a3s_CX X).prime u ⊔ (a3s_CX X).prime v ≤ (a3s_CX X).prime z' :=
      sup_le ((a3s_CX X).prime_mono huz) ((a3s_CX X).prime_mono hvz)
    have h2 : (a3s_CX X).prime z' ≤ 𝔶 := hw ▸ (a3s_CX X).prime_mono hzw
    have h3 := h𝔶.2 ⟨inferInstance, h1⟩ h2
    exact (a3s_CX X).prime_injective ((le_antisymm h2 h3).trans hw.symm)
  obtain ⟨w', hw', hcomp⟩ := a3s_component_of_maximal u v w huw hvw hmax
  have hb := he v hv w' hcomp
  rw [hw'] at hb
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  obtain ⟨mu, cu, -, hcu, hu, hdu⟩ := a3s_nums X n hn u
  obtain ⟨mv, cv, -, hcv, hv', hdv⟩ := a3s_nums X n hn v
  obtain ⟨mw, cw, -, hcw, hw'', hdw⟩ := a3s_nums X n hn w
  obtain ⟨mη, cη, hmη, -, -, hdη⟩ := a3s_nums X n hn (genericPoint X.left)
  have hη' : mη = n := by
    rw [hn] at hmη; exact_mod_cast hmη.symm
  rw [hcu, hcv, hcw] at hb
  have hb' : cu + cv ≤ cw + k := by exact_mod_cast hb
  change _ + ringKrullDim (_ ⧸ (a3s_CX X).prime (genericPoint X.left)) ≤ _
  rw [← hw, hdw, hdη, hdu, hdv]
  exact_mod_cast (show mw + 1 + (mη + 1) ≤ mu + 1 + (mv + 1) + k by omega)

end Excess

end HodgeLean.Adapters
