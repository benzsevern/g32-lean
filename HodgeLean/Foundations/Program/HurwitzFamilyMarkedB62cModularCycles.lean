import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCoefficients

noncomputable section

namespace HodgeLean.Foundations.Program

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
theorem b6m_integral_lifting_iff_modular_cycles (X : TopCat) (n : ℕ) :
    (∀ (c : (SingularChainComplex ℤ X).X 2)
      (z : (SingularChainComplex ℤ X).X 1),
      ((SingularChainComplex ℤ X).d 2 1).hom c = (n : ℤ) • z →
      ∃ w q : (SingularChainComplex ℤ X).X 2,
        ((SingularChainComplex ℤ X).d 2 1).hom w = 0 ∧ c - w = (n : ℤ) • q) ↔
    (∀ v : (SingularChainComplex (ZMod n) X).X 2,
      ((SingularChainComplex (ZMod n) X).d 2 1).hom v = 0 →
      ∃ w : (SingularChainComplex ℤ X).X 2,
        ((SingularChainComplex ℤ X).d 2 1).hom w = 0 ∧
          b6m_singularReduction X n 2 w = v) := by
  constructor
  · intro h v hv
    obtain ⟨c, rfl⟩ := b6m_singularReduction_surjective X n 2 v
    have hc : b6m_singularReduction X n 1
        (((SingularChainComplex ℤ X).d 2 1).hom c) = 0 :=
      (b6m_singularReduction_boundary X n 1 c).trans hv
    obtain ⟨z, hz⟩ := (b6m_singularReduction_zero_iff X n 1 _).mp hc
    obtain ⟨w, q, hw, hq⟩ := h c z hz
    refine ⟨w, hw, ?_⟩
    have he := (b6m_singularReduction_zero_iff X n 2 (c - w)).mpr ⟨q, hq⟩
    rw [map_sub, sub_eq_zero] at he
    exact he.symm
  · intro h c z hc
    have hz : b6m_singularReduction X n 1
        (((SingularChainComplex ℤ X).d 2 1).hom c) = 0 :=
      (b6m_singularReduction_zero_iff X n 1 _).mpr ⟨z, hc⟩
    have hv : ((SingularChainComplex (ZMod n) X).d 2 1).hom
        (b6m_singularReduction X n 2 c) = 0 :=
      (b6m_singularReduction_boundary X n 1 c).symm.trans hz
    obtain ⟨w, hw, he⟩ := h _ hv
    have hzero : b6m_singularReduction X n 2 (c - w) = 0 := by
      rw [map_sub, he, sub_self]
    obtain ⟨q, hq⟩ := (b6m_singularReduction_zero_iff X n 2 _).mp hzero
    exact ⟨w, q, hw, hq⟩

set_option backward.isDefEq.respectTransparency false in
theorem b6m_integral_cycle_lifting_of_modular_cycles (X : TopCat)
    (h : ∀ n : ℕ, n ≠ 0 → ∀ v : (SingularChainComplex (ZMod n) X).X 2,
      ((SingularChainComplex (ZMod n) X).d 2 1).hom v = 0 →
      ∃ w : (SingularChainComplex ℤ X).X 2,
        ((SingularChainComplex ℤ X).d 2 1).hom w = 0 ∧
          b6m_singularReduction X n 2 w = v)
    (n : ℤ) (hn : n ≠ 0)
    (c : (SingularChainComplex ℤ X).X 2)
    (z : (SingularChainComplex ℤ X).X 1)
    (hc : ((SingularChainComplex ℤ X).d 2 1).hom c = n • z) :
    ∃ w q : (SingularChainComplex ℤ X).X 2,
      ((SingularChainComplex ℤ X).d 2 1).hom w = 0 ∧ c - w = n • q := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact (b6m_integral_lifting_iff_modular_cycles X k).mpr
      (h k (by exact_mod_cast hn)) c z hc
  · have hk : k ≠ 0 := by
      intro hk
      subst k
      exact hn rfl
    have hc' : ((SingularChainComplex ℤ X).d 2 1).hom c = (k : ℤ) • (-z) := by
      simpa only [neg_zsmul, zsmul_neg] using hc
    obtain ⟨w, q, hw, hq⟩ :=
      (b6m_integral_lifting_iff_modular_cycles X k).mpr (h k hk) c (-z) hc'
    refine ⟨w, -q, hw, ?_⟩
    simpa only [neg_zsmul, zsmul_neg, neg_neg] using hq

set_option backward.isDefEq.respectTransparency false in
theorem b6m_modular_cycles_lift_of_homology_representatives (X : TopCat) (n : ℕ)
    (h : ∀ v : (SingularChainComplex (ZMod n) X).X 2,
      ((SingularChainComplex (ZMod n) X).d 2 1).hom v = 0 →
      ∃ w : (SingularChainComplex ℤ X).X 2,
        ((SingularChainComplex ℤ X).d 2 1).hom w = 0 ∧
        ∃ u : (SingularChainComplex (ZMod n) X).X 3,
          v = b6m_singularReduction X n 2 w +
            ((SingularChainComplex (ZMod n) X).d 3 2).hom u) :
    ∀ v : (SingularChainComplex (ZMod n) X).X 2,
      ((SingularChainComplex (ZMod n) X).d 2 1).hom v = 0 →
      ∃ w : (SingularChainComplex ℤ X).X 2,
        ((SingularChainComplex ℤ X).d 2 1).hom w = 0 ∧
          b6m_singularReduction X n 2 w = v := by
  intro v hv
  obtain ⟨c, rfl⟩ := b6m_singularReduction_surjective X n 2 v
  obtain ⟨w, hw, u, hu⟩ := h _ hv
  obtain ⟨W, q, hW, hq⟩ := b6m_cycle_lifting_of_modular_boundary X n c w hw u hu
  refine ⟨W, hW, ?_⟩
  have hzero := (b6m_singularReduction_zero_iff X n 2 (c - W)).mpr ⟨q, hq⟩
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.symm

end HodgeLean.Foundations.Program
