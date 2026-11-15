import HodgeLean.Foundations.Program.SchoenCycleS1i4GermMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Projection onto the first coordinates.
Source: Mathlib, ContinuousLinearMap.pi and ContinuousLinearMap.proj. -/
def s2e_nativeAnalytic_baseProjection (d : ℕ) :
    (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.castSucc

example (d : ℕ) (z : Fin (d + 1) → ℂ) (j : Fin d) :
    s2e_nativeAnalytic_baseProjection d z j = z j.castSucc := rfl

theorem s2e_remainder_germ_identity (d k : ℕ)
    (f g q : (Fin (d + 1) → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (hq : AnalyticAt ℂ q 0)
    (b : Fin k → (Fin d → ℂ) → ℂ) (hb : ∀ i, AnalyticAt ℂ (b i) 0)
    (he : f =ᶠ[nhds 0] (fun z => g z * q z +
      ∑ i : Fin k, b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ))) :
    (⟨Filter.Germ.ofFun f, ⟨f, hf, rfl⟩⟩ : s2e_nativeAnalyticGermRing (d + 1)) =
      (⟨Filter.Germ.ofFun g, ⟨g, hg, rfl⟩⟩ : s2e_nativeAnalyticGermRing (d + 1)) *
      ⟨Filter.Germ.ofFun q, ⟨q, hq, rfl⟩⟩ +
      ∑ i : Fin k, s2e_nativeAnalytic_pullback (d + 1) d (s2e_nativeAnalytic_baseProjection d)
        ⟨Filter.Germ.ofFun (b i), ⟨b i, hb i, rfl⟩⟩ *
        s2e_nativeAnalytic_coordinate (d + 1) (Fin.last d) ^ (i : ℕ) := by
  apply Subtype.ext
  change Filter.Germ.ofFun f = (s2e_nativeAnalyticGermRing (d + 1)).subtype
    ((⟨Filter.Germ.ofFun g, ⟨g, hg, rfl⟩⟩ : s2e_nativeAnalyticGermRing (d + 1)) *
      ⟨Filter.Germ.ofFun q, ⟨q, hq, rfl⟩⟩ +
      ∑ i : Fin k, s2e_nativeAnalytic_pullback (d + 1) d (s2e_nativeAnalytic_baseProjection d)
        ⟨Filter.Germ.ofFun (b i), ⟨b i, hb i, rfl⟩⟩ *
        s2e_nativeAnalytic_coordinate (d + 1) (Fin.last d) ^ (i : ℕ))
  rw [map_add, map_mul, map_sum]
  change Filter.Germ.ofFun f = Filter.Germ.ofFun (g * q) +
    ∑ i : Fin k, Filter.Germ.ofFun (fun z => b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ))
  calc
    _ = (Filter.Germ.coeRingHom (nhds (0 : Fin (d + 1) → ℂ)))
        (g * q + ∑ i : Fin k, fun z => b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ)) :=
      Filter.Germ.coe_eq.mpr (by
        filter_upwards [he] with z hz
        simpa only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply] using hz)
    _ = _ := by rw [map_add, map_sum]; rfl

theorem s2e_remainder_evaluation_linear (d k n : ℕ)
    (ι : s2e_nativeAnalyticGermRing d →+* s2e_nativeAnalyticGermRing (d + 1))
    (b : Fin n → Fin k → s2e_nativeAnalyticGermRing d)
    (c : Fin n → s2e_nativeAnalyticGermRing d) :
    (∑ i : Fin k, ι ((∑ j : Fin n, c j • b j) i) *
      s2e_nativeAnalytic_coordinate (d + 1) (Fin.last d) ^ (i : ℕ)) =
    ∑ j : Fin n, ι (c j) * ∑ i : Fin k, ι (b j i) *
      s2e_nativeAnalytic_coordinate (d + 1) (Fin.last d) ^ (i : ℕ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem s2e_analytic_ideal_fg_of_regular (d k : ℕ)
    (hprev : IsNoetherianRing (s2e_nativeAnalyticGermRing d))
    (I : Ideal (s2e_nativeAnalyticGermRing (d + 1)))
    (g : (Fin (d + 1) → ℂ) → ℂ) (hg : AnalyticAt ℂ g 0)
    (hgI : (⟨Filter.Germ.ofFun g, ⟨g, hg, rfl⟩⟩ : s2e_nativeAnalyticGermRing (d + 1)) ∈ I)
    (hdiv : ∀ f : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ f 0 →
      ∃ q : (Fin (d + 1) → ℂ) → ℂ, ∃ b : Fin k → (Fin d → ℂ) → ℂ,
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (b i) 0) ∧
        f =ᶠ[nhds 0] (fun z => g z * q z +
          ∑ i : Fin k, b i (fun j => z j.castSucc) * z (Fin.last d) ^ (i : ℕ))) :
    I.FG := by
  classical
  let G : s2e_nativeAnalyticGermRing (d + 1) := ⟨Filter.Germ.ofFun g, ⟨g, hg, rfl⟩⟩
  let ι := s2e_nativeAnalytic_pullback (d + 1) d (s2e_nativeAnalytic_baseProjection d)
  let x := s2e_nativeAnalytic_coordinate (d + 1) (Fin.last d)
  let ev := fun v : Fin k → s2e_nativeAnalyticGermRing d => ∑ i : Fin k, ι (v i) * x ^ (i : ℕ)
  obtain ⟨n, b, hb, hgen⟩ := s2e_s1i4_finite_remainder_module_aux d k hprev ι I
  let J := Ideal.span (insert G (Set.range (fun j : Fin n => ev (b j))))
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro a (rfl | ⟨j, rfl⟩)
    · exact hgI
    · exact hb j
  have hIJ : I ≤ J := by
    intro a ha
    obtain ⟨f, hf, he⟩ := a.property
    obtain ⟨q, β, hq, hβ, hrel⟩ := hdiv f hf
    let Q : s2e_nativeAnalyticGermRing (d + 1) := ⟨Filter.Germ.ofFun q, ⟨q, hq, rfl⟩⟩
    let v : Fin k → s2e_nativeAnalyticGermRing d :=
      fun i => ⟨Filter.Germ.ofFun (β i), ⟨β i, hβ i, rfl⟩⟩
    have hdecomp : a = G * Q + ev v := by
      have h := s2e_remainder_germ_identity d k f g q hf hg hq β hβ hrel
      have haeq : (⟨Filter.Germ.ofFun f, ⟨f, hf, rfl⟩⟩ : s2e_nativeAnalyticGermRing (d + 1)) = a :=
        Subtype.ext he
      exact haeq ▸ h
    have hvI : ev v ∈ I := by
      have hh := I.sub_mem ha (I.mul_mem_right Q (show G ∈ I from hgI))
      simpa only [hdecomp, add_sub_cancel_left] using hh
    obtain ⟨c, hc⟩ := hgen v hvI
    have hvJ : ev v ∈ J := by
      rw [hc]
      change (∑ i : Fin k, ι ((∑ j : Fin n, c j • b j) i) * x ^ (i : ℕ)) ∈ J
      rw [s2e_remainder_evaluation_linear d k n ι b c]
      exact Submodule.sum_mem J fun j _ => J.mul_mem_left (ι (c j))
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))
    rw [hdecomp]
    exact J.add_mem (J.mul_mem_right Q (Ideal.subset_span (Set.mem_insert _ _))) hvJ
  rw [show I = J from le_antisymm hIJ hJI]
  exact Submodule.fg_span ((Set.finite_range (fun j : Fin n => ev (b j))).insert G)

end HodgeLean.Foundations.Program
