import HodgeLean.Foundations.Program.CompensationEightfoldDefs

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

variable {K Z : Type*} [Field K] [AddCommGroup Z] [Module K Z]

def cq8_wedgePair : Z →ₗ[K] Z →ₗ[K] ⋀[K]^2 Z where
  toFun u :=
    { toFun := fun v => exteriorPower.ιMulti K 2 ![u, v]
      map_add' := by
        intro v w
        apply Subtype.ext
        simp [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, mul_add]
      map_smul' := by
        intro c v
        apply Subtype.ext
        simp [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, smul_mul_assoc, mul_smul_comm] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, add_mul]
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, smul_mul_assoc, mul_smul_comm]

theorem cq8_wedgePair_map (F : Z →ₗ[K] Z) (u v : Z) :
    exteriorPower.map 2 F (cq8_wedgePair (K := K) u v) = cq8_wedgePair (K := K) (F u) (F v) := by
  exact DFunLike.congr_fun (exteriorPower.map_comp_ιMulti F) ![u, v]

theorem cq8_wedgePair_zero (P : Submodule K Z) [Module.Finite K P]
    (hP : Module.finrank K P ≤ 1) (u v : Z) (hu : u ∈ P) (hv : v ∈ P) :
    cq8_wedgePair (K := K) u v = 0 := by
  let a : Fin 2 → P := ![⟨u, hu⟩, ⟨v, hv⟩]
  have hdep : ¬LinearIndependent K a := by
    intro hh
    have hc := hh.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    omega
  exact ((exteriorPower.ιMulti K 2).compLinearMap P.subtype).map_linearDependent a hdep

theorem cq8_exterior_two_sup (P Q : Submodule K Z)
    [Module.Finite K P] [Module.Finite K Q]
    (hP : Module.finrank K P ≤ 1) (hQ : Module.finrank K Q ≤ 1)
    (F : Z →ₗ[K] Z) (a b : K)
    (hFP : ∀ u ∈ P, F u = a • u) (hFQ : ∀ v ∈ Q, F v = b • v) :
    ∀ x ∈ LinearMap.range (exteriorPower.map 2 (P ⊔ Q).subtype),
      exteriorPower.map 2 F x = (a * b) • x := by
  have hpair (u v : ↥(P ⊔ Q)) :
      exteriorPower.map 2 F (cq8_wedgePair (K := K) (u : Z) v) =
        (a * b) • cq8_wedgePair (K := K) (u : Z) v := by
    obtain ⟨p, hp, q, hq, hu⟩ := Submodule.mem_sup.mp u.property
    obtain ⟨r, hr, s, hs, hv⟩ := Submodule.mem_sup.mp v.property
    rw [← hu, ← hv]
    simp only [map_add, LinearMap.add_apply, cq8_wedgePair_map, hFP _ hp, hFP _ hr,
      hFQ _ hq, hFQ _ hs, map_smul, LinearMap.smul_apply, smul_smul,
      cq8_wedgePair_zero P hP p r hp hr, cq8_wedgePair_zero Q hQ q s hq hs,
      smul_zero, zero_add, add_zero, smul_add]
    rw [mul_comm b a]
  rintro _ ⟨x, rfl⟩
  have hh : (exteriorPower.map 2 F).comp (exteriorPower.map 2 (P ⊔ Q).subtype) =
      (a * b) • exteriorPower.map 2 (P ⊔ Q).subtype := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span K 2 ↥(P ⊔ Q))
    rintro _ ⟨v, rfl⟩
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply,
      show exteriorPower.map 2 (P ⊔ Q).subtype (exteriorPower.ιMulti K 2 ![v 0, v 1]) =
        cq8_wedgePair (K := K) (v 0 : Z) (v 1) from
        DFunLike.congr_fun (exteriorPower.map_comp_ιMulti (P ⊔ Q).subtype) _] using
      hpair (v 0) (v 1)
  exact LinearMap.congr_fun hh x

theorem cq8_exterior_invariant (P : Submodule K Z) (F : Z →ₗ[K] Z)
    (hF : ∀ x ∈ P, F x ∈ P) (n : ℕ) :
    ∀ x ∈ LinearMap.range (exteriorPower.map n P.subtype),
      exteriorPower.map n F x ∈ LinearMap.range (exteriorPower.map n P.subtype) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨exteriorPower.map n (F.restrict hF) y, ?_⟩
  change ((exteriorPower.map n P.subtype).comp
    (exteriorPower.map n (F.restrict hF))) y =
      ((exteriorPower.map n F).comp (exteriorPower.map n P.subtype)) y
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
  rfl

theorem cq8_weilClasses_invariant {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}
    (A : HodgeBlocks.WeilAction M d) (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (hW : A.IsWeilType) (f : Module.End ℚ V)
    (hs : ∀ x ∈ A.Vs, f.baseChange ℂ x ∈ A.Vs)
    (hb : ∀ x ∈ A.Vsbar, f.baseChange ℂ x ∈ A.Vsbar) :
    (A.weilClasses hH hW).map
      (exteriorPower.map (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) f) ≤ A.weilClasses hH hW := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let n := k + k
  have hp := cq8_exterior_invariant A.Vs (f.baseChange ℂ) hs n
  have hq := cq8_exterior_invariant A.Vsbar (f.baseChange ℂ) hb n
  rintro _ ⟨w, hw, rfl⟩
  change HodgeBlocks.complexifyWedge n (exteriorPower.map n f w) ∈
    LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map n A.Vsbar.subtype)
  rw [HodgeBlocks.complexifyWedge_exteriorPower_map]
  change HodgeBlocks.complexifyWedge n w ∈
    LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map n A.Vsbar.subtype) at hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hw
  rw [← hxy, map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hp x hx))
    (Submodule.mem_sup_right (hq y hy))

end HodgeLean.Foundations.Program
