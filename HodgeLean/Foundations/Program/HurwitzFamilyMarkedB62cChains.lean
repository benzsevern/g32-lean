import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cIntegral

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

abbrev b6m_chainQuotient (Y : SSet.{0}) :=
  Simplicial.ChainGroup ℤ Y 1 ⧸ (Simplicial.boundary ℤ 1 (X := Y)).range.toAddSubgroup

def b6m_chainQuotientMap (Y : SSet.{0}) :
    Simplicial.ChainGroup ℤ Y 1 →+ b6m_chainQuotient Y :=
  QuotientAddGroup.mk' _

set_option backward.isDefEq.respectTransparency false in
theorem b6m_chainQuotient_triangle (Y : SSet.{0})
    (τ : Y.obj (Opposite.op (SimplexCategory.mk 2))) :
    b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ (Y.δ 0 τ)) -
      b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ (Y.δ 1 τ)) +
      b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ (Y.δ 2 τ)) = 0 := by
  have h : b6m_chainQuotientMap Y
      (Simplicial.boundary ℤ 1 (Simplicial.chainOfSimplex ℤ τ)) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨_, rfl⟩
  rw [Simplicial.boundary_chainOfSimplex, map_sum] at h
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc, map_zsmul,
    Simplicial.ChainGroup] using h

open HodgeLean.Adapters Convexity

def b6m_pathChain {T : Type} [TopologicalSpace T] (g : C(unitInterval, T)) :
    b6m_chainQuotient (TopCat.toSSet.obj (TopCat.of T)) :=
  b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex g))

theorem b6m_pathChain_triangle {T : Type} [TopologicalSpace T]
    (f : C(StdSimplex ℝ (Fin 3), T)) (g₀ g₁ g₂ : C(unitInterval, T))
    (h₀ : ∀ t, f (StdSimplex.map (0 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) = g₀ t)
    (h₁ : ∀ t, f (StdSimplex.map (1 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) = g₁ t)
    (h₂ : ∀ t, f (StdSimplex.map (2 : Fin 3).succAbove (StdSimplex.homeomorphI.symm t)) = g₂ t) :
    b6m_pathChain g₀ - b6m_pathChain g₁ + b6m_pathChain g₂ = 0 := by
  let Y := TopCat.toSSet.obj (TopCat.of T)
  have h := b6m_chainQuotient_triangle Y (b3Rest2_triSimplex f)
  have h' : b6m_pathChain (simplexPath (Y.δ 0 (b3Rest2_triSimplex f))) -
      b6m_pathChain (simplexPath (Y.δ 1 (b3Rest2_triSimplex f))) +
      b6m_pathChain (simplexPath (Y.δ 2 (b3Rest2_triSimplex f))) = 0 := by
    simpa only [b6m_pathChain, Y,
      b3Rest2_pathSimplex_simplexPath (T := T)] using h
  have e : ∀ i : Fin 3, ∀ g : C(unitInterval, T),
      (∀ t, f (StdSimplex.map i.succAbove (StdSimplex.homeomorphI.symm t)) = g t) →
      simplexPath (Y.δ i (b3Rest2_triSimplex f)) = g :=
    fun i g hg ↦ ContinuousMap.ext fun t ↦ (b3Rest2_face f i t).trans (hg t)
  rwa [e 0 g₀ h₀, e 1 g₁ h₁, e 2 g₂ h₂] at h'

theorem b6m_pathChain_subdiv {T : Type} [TopologicalSpace T]
    (g : C(unitInterval, T)) (a b c : unitInterval) :
    b6m_pathChain (b3Rest2_restr g a c) =
      b6m_pathChain (b3Rest2_restr g a b) + b6m_pathChain (b3Rest2_restr g b c) := by
  have h := b6m_pathChain_triangle
    (g.comp ⟨b3Rest2_bary a b c, b3Rest2_continuous_bary a b c⟩)
    (b3Rest2_restr g b c) (b3Rest2_restr g a c) (b3Rest2_restr g a b) ?_ ?_ ?_
  · apply sub_eq_zero.mp
    calc
      _ = -(b6m_pathChain (b3Rest2_restr g b c) - b6m_pathChain (b3Rest2_restr g a c) +
        b6m_pathChain (b3Rest2_restr g a b)) := by abel
      _ = 0 := by rw [h, neg_zero]
  all_goals
    intro t
    obtain ⟨⟨w00, w01, w02⟩, ⟨w10, w11, w12⟩, ⟨w20, w21, w22⟩⟩ := b3Rest2_face_weights t
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, b3Rest2_restr_apply]
    congr 1
    apply Subtype.ext
    simp only [b3Rest2_bary, b3Rest2_affI, w00, w01, w02, w10, w11, w12, w20, w21, w22]
    ring

theorem b6m_pathChain_const {T : Type} [TopologicalSpace T] (x : T) :
    b6m_pathChain (ContinuousMap.const unitInterval x) = 0 := by
  have e : ∀ a b : unitInterval,
      b3Rest2_restr (ContinuousMap.const unitInterval x) a b =
        ContinuousMap.const unitInterval x := by
    intro a b
    ext t
    rfl
  have h := b6m_pathChain_subdiv (ContinuousMap.const unitInterval x) 0 0 0
  simp only [e] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem b6m_pathChain_reverse {T : Type} [TopologicalSpace T]
    (g : C(unitInterval, T)) :
    b6m_pathChain (b3Rest2_restr g 1 0) = -b6m_pathChain g := by
  have e : b3Rest2_restr g 0 0 = ContinuousMap.const unitInterval (g 0) := by
    ext t
    simp [b3Rest2_restr, b3Rest2_affI]
  have h := b6m_pathChain_subdiv g 0 1 0
  rw [e, b6m_pathChain_const, b3Rest2_restr_zero_one] at h
  calc
    _ = (b6m_pathChain g + b6m_pathChain (b3Rest2_restr g 1 0)) - b6m_pathChain g := by abel
    _ = -b6m_pathChain g := by rw [← h, zero_sub]

theorem b6m_pathChain_trans {T : Type} [TopologicalSpace T] {x y z : T}
    (p : Path x y) (q : Path y z) :
    b6m_pathChain (p.trans q).toContinuousMap =
      b6m_pathChain p.toContinuousMap + b6m_pathChain q.toContinuousMap := by
  let m : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have e₀ : b3Rest2_restr (p.trans q).toContinuousMap 0 m = p.toContinuousMap := by
    ext t
    change (p.trans q) (b3Rest2_affI 0 m t) = p t
    rw [← (p.trans q).extend_extends']
    have ht : (b3Rest2_affI 0 m t : ℝ) = (t : ℝ) / 2 := by
      simp [b3Rest2_affI, m, div_eq_mul_inv]
    rw [ht, Path.extend_trans_of_le_half p q (by linarith [t.2.2])]
    rw [show 2 * ((t : ℝ) / 2) = t by ring, p.extend_extends']
  have e₁ : b3Rest2_restr (p.trans q).toContinuousMap m 1 = q.toContinuousMap := by
    ext t
    change (p.trans q) (b3Rest2_affI m 1 t) = q t
    rw [← (p.trans q).extend_extends']
    have ht : (b3Rest2_affI m 1 t : ℝ) = 1 / 2 + (t : ℝ) / 2 := by
      simp [b3Rest2_affI, m]
      ring
    rw [ht, Path.extend_trans_of_half_le p q (by linarith [t.2.1])]
    rw [show 2 * (1 / 2 + (t : ℝ) / 2) - 1 = t by ring, q.extend_extends']
  have h := b6m_pathChain_subdiv (p.trans q).toContinuousMap 0 m 1
  rwa [b3Rest2_restr_zero_one, e₀, e₁] at h

theorem b6m_pathChain_symm {T : Type} [TopologicalSpace T] {x y : T}
    (p : Path x y) : b6m_pathChain p.symm.toContinuousMap = -b6m_pathChain p.toContinuousMap := by
  have e : b3Rest2_restr p.toContinuousMap 1 0 = p.symm.toContinuousMap := by
    ext t
    change p (b3Rest2_affI 1 0 t) = p (unitInterval.symm t)
    congr 1
    apply Subtype.ext
    simp [b3Rest2_affI, unitInterval.coe_symm_eq, sub_eq_add_neg]
  rw [← e]
  exact b6m_pathChain_reverse _

theorem b6m_pathChain_loop {T : Type} [TopologicalSpace T] {x : T} (γ : Path x x) :
    ∃ p : C(UnitAddCircle, T), b6m_pathChain γ.toContinuousMap =
      b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex p)) := by
  obtain ⟨p, hp⟩ := RiemannRochTop_path_circle_factor γ
  refine ⟨p, ?_⟩
  have e : γ.toContinuousMap = simplexPath (loopSimplex p) := by
    rw [spec_simplexPath_loopSimplex]
    ext t
    exact (hp t).symm
  simp only [b6m_pathChain, e, b3Rest2_pathSimplex_simplexPath (T := T)]

theorem b6m_pathChain_based {T : Type} [TopologicalSpace T] {a x y : T}
    (p : Path a x) (g : Path x y) (q : Path a y) :
    ∃ c : C(UnitAddCircle, T), b6m_pathChain g.toContinuousMap =
      b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex c)) +
        b6m_pathChain q.toContinuousMap - b6m_pathChain p.toContinuousMap := by
  obtain ⟨c, hc⟩ := b6m_pathChain_loop ((p.trans g).trans q.symm)
  refine ⟨c, ?_⟩
  rw [← hc, b6m_pathChain_trans, b6m_pathChain_trans, b6m_pathChain_symm]
  abel

theorem b6m_chainMap_ext (Y : SSet.{0}) (n : ℕ) (M : Type) [AddCommGroup M]
    (f g : Simplicial.ChainGroup ℤ Y n →ₗ[ℤ] M)
    (h : ∀ σ : Y.obj (Opposite.op (SimplexCategory.mk n)),
      f (Simplicial.chainOfSimplex ℤ σ) = g (Simplicial.chainOfSimplex ℤ σ)) : f = g := by
  suffices e : ModuleCat.ofHom f = ModuleCat.ofHom g from congrArg ModuleCat.Hom.hom e
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ℤ at a
  have hi : (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a =
      a • Simplicial.chainOfSimplex ℤ σ := by
    rw [Simplicial.chainOfSimplex, ← map_zsmul]
    simp
  change f ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a) =
    g ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a)
  rw [hi, map_zsmul, map_zsmul, h]

theorem b6m_simplex_endpoints {T : Type} [TopologicalSpace T]
    (σ : (TopCat.toSSet.obj (TopCat.of T)).obj (Opposite.op (SimplexCategory.mk 1)))
    (i : Fin 2) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of T)).δ i σ) =
      simplexPath σ (if i = 0 then 1 else 0) := by
  simp only [TopCat.toSSetObj₀Equiv_apply, simplexPath, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  erw [TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  have hd : (default : StdSimplex ℝ (Fin 1)) = StdSimplex.single 0 := by
    apply StdSimplex.ext
    refine Finsupp.ext fun j ↦ ?_
    fin_cases j
    simp [StdSimplex.weights_apply_eq_one]
  rw [hd, StdSimplex.map_single]
  fin_cases i
  · simp only [Fin.zero_eta, ite_true, StdSimplex.homeomorphI_symm_one]
    rfl
  · simp only [Fin.mk_one, one_ne_zero, ite_false, StdSimplex.homeomorphI_symm_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem b6m_cycle_chain_span (T : Type) [TopologicalSpace T] [PathConnectedSpace T]
    (z : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hz : Simplicial.boundary ℤ 0 z = 0) :
    b6m_chainQuotientMap _ z ∈ Submodule.span ℤ (Set.range
      (fun p : C(UnitAddCircle, T) ↦
        b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex p)))) := by
  classical
  let Y := TopCat.toSSet.obj (TopCat.of T)
  let L : Submodule ℤ (b6m_chainQuotient Y) := Submodule.span ℤ (Set.range
    (fun p : C(UnitAddCircle, T) ↦
      b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex p))))
  let M := b6m_chainQuotient Y ⧸ L
  letI : Module ℤ M := AddCommGroup.toIntModule M
  let π : b6m_chainQuotient Y →ₗ[ℤ] M := L.mkQ
  let φ : Simplicial.ChainGroup ℤ Y 1 →ₗ[ℤ] M :=
    { toFun := fun c ↦ π (b6m_chainQuotientMap Y c)
      map_add' := by intro c d; simp
      map_smul' := by
        intro n c
        change π (b6m_chainQuotientMap Y
          ((Simplicial.ChainGroup ℤ Y 1).isModule.smul n c)) = n • π (b6m_chainQuotientMap Y c)
        rw [int_smul_eq_zsmul]
        exact map_zsmul (π.toAddMonoidHom.comp (b6m_chainQuotientMap Y)) n c }
  let a : T := Classical.choice inferInstance
  let p := fun x : T ↦ PathConnectedSpace.somePath a x
  let η := b6m_integralCochain Y 0 M
    (fun v ↦ π (b6m_pathChain (p (TopCat.toSSetObj₀Equiv v)).toContinuousMap))
  have heq : φ = η.comp (Simplicial.boundary ℤ 0) := by
    apply b6m_chainMap_ext Y 1 M
    intro σ
    let g := simplexPath σ
    let gp : Path (g 0) (g 1) := ⟨g, rfl, rfl⟩
    obtain ⟨c, hc⟩ := b6m_pathChain_based (p (g 0)) gp (p (g 1))
    have hl : π (b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ (loopSimplex c))) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero L).mpr
      exact Submodule.subset_span ⟨c, rfl⟩
    have h := congrArg π hc
    rw [map_sub, map_add, hl, zero_add] at h
    change π (b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ σ)) =
      η (Simplicial.boundary ℤ 0 (Simplicial.chainOfSimplex ℤ σ))
    rw [Simplicial.boundary_chainOfSimplex, map_sum]
    simp only [η, Fin.sum_univ_succ, Fin.sum_univ_zero, map_smul,
      b6m_integralCochain_simplex]
    erw [b6m_simplex_endpoints (T := T) σ 0, b6m_simplex_endpoints (T := T) σ 1]
    simpa [g, gp, b6m_pathChain, b3Rest2_pathSimplex_simplexPath (T := T),
      Y, sub_eq_add_neg, Simplicial.ChainGroup] using h
  apply (Submodule.Quotient.mk_eq_zero L).mp
  change φ z = 0
  rw [heq]
  change η (Simplicial.boundary ℤ 0 z) = 0
  rw [hz, map_zero]

end HodgeLean.Foundations.Program
