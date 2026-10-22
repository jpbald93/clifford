import Clifford.Third

/-!
# Layer 14: Mathlib-only restatements and witnesses for Clifford's circle theorems

The `l14_*` statements mention only Mathlib notions. The circles are `EuclideanGeometry.Sphere ℂ`
through a common point `M` (arbitrary, not necessarily the origin), with pairwise distinct centres.
`Pᵢⱼ` is **any** point other than `M` lying on circles `i` and `j`; the bridge `l14b_second`
shows it is the library's `secondInter`. The circle `Γᵢⱼₖ` through `Pᵢⱼ, Pᵢₖ, Pⱼₖ` is expressed
with `EuclideanGeometry.Cospherical` (for non-collinear points this is "lies on the circle through
them"). The conclusions are those of the library (existential, as in `clifford_one` /
`clifford_two`), translated by `M`.
`l14w_*` are explicit Gaussian-rational configurations.
-/

namespace Clifford

open EuclideanGeometry ComplexConjugate Complex

/-! ### Bridges -/

/-- A point `≠ 0` on the two circles through `0` with centres `c ≠ d` is `secondInter c d`. -/
theorem l14b_sec_eq {c d z : ℂ} (hcd : c ≠ d) (hz : z ≠ 0) (h1 : dist z c = ‖c‖)
    (h2 : dist z d = ‖d‖) : z = secondInter c d := by
  have k1 : (z - c) * conj (z - c) = c * conj c := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      ← Complex.dist_eq, h1]
  have k2 : (z - d) * conj (z - d) = d * conj d := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      ← Complex.dist_eq, h2]
  have hA : conj c - conj d ≠ 0 := by
    rw [← map_sub]; exact (map_ne_zero _).2 (sub_ne_zero.2 hcd)
  simp only [map_sub] at k1 k2
  have key : z * (z * (conj c - conj d) - (conj c * d - c * conj d)) = 0 := by
    linear_combination (d - z) * k1 + (z - c) * k2
  have h := (mul_eq_zero.1 key).resolve_left hz
  unfold secondInter sec
  rw [eq_div_iff hA]
  linear_combination h

/-- A point `P ≠ M` on two circles through `M` with distinct centres is the library's second
intersection (after translating `M` to the origin), and that second intersection is `≠ 0`. -/
theorem l14b_second {M : ℂ} {s t : Sphere ℂ} (hs : M ∈ s) (ht : M ∈ t)
    (hst : s.center ≠ t.center) {P : ℂ} (h : P ∈ s ∧ P ∈ t ∧ P ≠ M) :
    P - M = secondInter (s.center - M) (t.center - M) ∧
      secondInter (s.center - M) (t.center - M) ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [mem_sphere] at hs ht h1 h2
  have e : ∀ c : ℂ, dist (P - M) (c - M) = dist P c := fun c => by
    rw [Complex.dist_eq, Complex.dist_eq]; ring_nf
  have f : ∀ c : ℂ, ‖c - M‖ = dist M c := fun c => by rw [Complex.dist_eq, norm_sub_rev]
  have hz : P - M ≠ 0 := sub_ne_zero.2 h3
  have eq := l14b_sec_eq (c := s.center - M) (d := t.center - M)
    (fun h => hst (sub_left_injective h)) hz (by rw [e, f, h1, hs]) (by rw [e, f, h2, ht])
  exact ⟨eq, eq ▸ hz⟩

theorem l14b_collinear_sub {a b c M : ℂ} (h : Collinear ℝ ({a - M, b - M, c - M} : Set ℂ)) :
    Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a - M) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  refine ⟨v, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · obtain ⟨r, hr⟩ := hv (p - M) (by simp)
    refine ⟨r, ?_⟩
    rw [vadd_eq_add, Complex.real_smul] at hr ⊢
    linear_combination hr
  · obtain ⟨r, hr⟩ := hv (p - M) (by simp)
    refine ⟨r, ?_⟩
    rw [vadd_eq_add, Complex.real_smul] at hr ⊢
    linear_combination hr

theorem l14b_cospherical_add {s : Set ℂ} (M : ℂ) (h : Cospherical s) :
    Cospherical ((· + M) '' s) := by
  obtain ⟨c, r, hr⟩ := h
  refine ⟨c + M, r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [dist_add_right]; exact hr x hx

theorem l14b_collinear_add {s : Set ℂ} (M : ℂ) (h : Collinear ℝ s) :
    Collinear ℝ ((· + M) '' s) := by
  obtain ⟨p, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).1 h
  refine (collinear_iff_exists_forall_eq_smul_vadd _).2 ⟨p + M, v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, rfl⟩ := hv x hx
  exact ⟨r, by simp only [vadd_eq_add]; ring⟩

/-- A point on the library's `gam` gives a `Cospherical` statement for the original points. -/
theorem l14b_gam {c₁ c₂ c₃ M P12 P13 P23 X : ℂ} (e12 : P12 - M = secondInter c₁ c₂)
    (e13 : P13 - M = secondInter c₁ c₃) (e23 : P23 - M = secondInter c₂ c₃)
    (hX : X ∈ gam c₁ c₂ c₃) (hn : ¬ Collinear ℝ ({P12, P13, P23} : Set ℂ)) :
    Cospherical ({P12, P13, P23, X + M} : Set ℂ) := by
  have hn' : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ) := by
    rw [← e12, ← e13, ← e23]; exact fun h => hn (l14b_collinear_sub h)
  have m1 := mem_circumcircle_left (secondInter c₁ c₂) (secondInter c₁ c₃) (secondInter c₂ c₃)
  have m2 := mem_circumcircle_middle hn'
  have m3 := mem_circumcircle_right hn'
  unfold gam at hX
  rw [← e12, ← e13, ← e23] at m1 m2 m3 hX
  set S := circumcircle (P12 - M) (P13 - M) (P23 - M)
  have hs : ({P12, P13, P23, X + M} : Set ℂ) = (· + M) '' {P12 - M, P13 - M, P23 - M, X} := by
    simp only [Set.image_insert_eq, Set.image_singleton, sub_add_cancel]
  rw [hs]
  refine l14b_cospherical_add M ⟨S.center, S.radius, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> assumption

/-! ### Clifford's first theorem (n = 4) -/

/-- **Clifford's first circle theorem**, Mathlib-only statement. -/
theorem l14_clifford_one (M : ℂ) (s₁ s₂ s₃ s₄ : Sphere ℂ)
    (hM : M ∈ s₁ ∧ M ∈ s₂ ∧ M ∈ s₃ ∧ M ∈ s₄)
    (d12 : s₁.center ≠ s₂.center) (d13 : s₁.center ≠ s₃.center) (d14 : s₁.center ≠ s₄.center)
    (d23 : s₂.center ≠ s₃.center) (d24 : s₂.center ≠ s₄.center) (d34 : s₃.center ≠ s₄.center)
    (P12 P13 P14 P23 P24 P34 : ℂ)
    (m12 : P12 ∈ s₁ ∧ P12 ∈ s₂ ∧ P12 ≠ M) (m13 : P13 ∈ s₁ ∧ P13 ∈ s₃ ∧ P13 ≠ M)
    (m14 : P14 ∈ s₁ ∧ P14 ∈ s₄ ∧ P14 ≠ M) (m23 : P23 ∈ s₂ ∧ P23 ∈ s₃ ∧ P23 ≠ M)
    (m24 : P24 ∈ s₂ ∧ P24 ∈ s₄ ∧ P24 ≠ M) (m34 : P34 ∈ s₃ ∧ P34 ∈ s₄ ∧ P34 ≠ M)
    (n123 : ¬ Collinear ℝ ({P12, P13, P23} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({P12, P14, P24} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({P13, P14, P34} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({P23, P24, P34} : Set ℂ)) :
    ∃ P : ℂ, Cospherical ({P12, P13, P23, P} : Set ℂ) ∧ Cospherical ({P12, P14, P24, P} : Set ℂ) ∧
      Cospherical ({P13, P14, P34, P} : Set ℂ) ∧ Cospherical ({P23, P24, P34, P} : Set ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  obtain ⟨e12, z12⟩ := l14b_second h1 h2 d12 m12
  obtain ⟨e13, z13⟩ := l14b_second h1 h3 d13 m13
  obtain ⟨e14, z14⟩ := l14b_second h1 h4 d14 m14
  obtain ⟨e23, z23⟩ := l14b_second h2 h3 d23 m23
  obtain ⟨e24, z24⟩ := l14b_second h2 h4 d24 m24
  obtain ⟨e34, z34⟩ := l14b_second h3 h4 d34 m34
  have nc : ∀ {a b c : ℂ} {x y z : ℂ}, a - M = x → b - M = y → c - M = z →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) → ¬ Collinear ℝ ({x, y, z} : Set ℂ) :=
    fun ea eb ec hn h => hn (l14b_collinear_sub (by rw [ea, eb, ec]; exact h))
  obtain ⟨X, x1, x2, x3, x4⟩ := clifford_one _ _ _ _ z12 z13 z14 z23 z24 z34
    (nc e12 e13 e23 n123) (nc e12 e14 e24 n124) (nc e13 e14 e34 n134) (nc e23 e24 e34 n234)
  exact ⟨X + M, l14b_gam e12 e13 e23 x1 n123, l14b_gam e12 e14 e24 x2 n124,
    l14b_gam e13 e14 e34 x3 n134, l14b_gam e23 e24 e34 x4 n234⟩

/-! ### Clifford's second theorem (n = 5) -/

/-- **Clifford's second circle theorem**, Mathlib-only statement. -/
theorem l14_clifford_two (M : ℂ) (s₁ s₂ s₃ s₄ s₅ : Sphere ℂ)
    (hM : M ∈ s₁ ∧ M ∈ s₂ ∧ M ∈ s₃ ∧ M ∈ s₄ ∧ M ∈ s₅)
    (d12 : s₁.center ≠ s₂.center) (d13 : s₁.center ≠ s₃.center) (d14 : s₁.center ≠ s₄.center)
    (d15 : s₁.center ≠ s₅.center) (d23 : s₂.center ≠ s₃.center) (d24 : s₂.center ≠ s₄.center)
    (d25 : s₂.center ≠ s₅.center) (d34 : s₃.center ≠ s₄.center) (d35 : s₃.center ≠ s₅.center)
    (d45 : s₄.center ≠ s₅.center)
    (P12 P13 P14 P15 P23 P24 P25 P34 P35 P45 : ℂ)
    (m12 : P12 ∈ s₁ ∧ P12 ∈ s₂ ∧ P12 ≠ M) (m13 : P13 ∈ s₁ ∧ P13 ∈ s₃ ∧ P13 ≠ M)
    (m14 : P14 ∈ s₁ ∧ P14 ∈ s₄ ∧ P14 ≠ M) (m15 : P15 ∈ s₁ ∧ P15 ∈ s₅ ∧ P15 ≠ M)
    (m23 : P23 ∈ s₂ ∧ P23 ∈ s₃ ∧ P23 ≠ M) (m24 : P24 ∈ s₂ ∧ P24 ∈ s₄ ∧ P24 ≠ M)
    (m25 : P25 ∈ s₂ ∧ P25 ∈ s₅ ∧ P25 ≠ M) (m34 : P34 ∈ s₃ ∧ P34 ∈ s₄ ∧ P34 ≠ M)
    (m35 : P35 ∈ s₃ ∧ P35 ∈ s₅ ∧ P35 ≠ M) (m45 : P45 ∈ s₄ ∧ P45 ∈ s₅ ∧ P45 ≠ M)
    (n123 : ¬ Collinear ℝ ({P12, P13, P23} : Set ℂ)) (n124 : ¬ Collinear ℝ ({P12, P14, P24} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({P12, P15, P25} : Set ℂ)) (n134 : ¬ Collinear ℝ ({P13, P14, P34} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({P13, P15, P35} : Set ℂ)) (n145 : ¬ Collinear ℝ ({P14, P15, P45} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({P23, P24, P34} : Set ℂ)) (n235 : ¬ Collinear ℝ ({P23, P25, P35} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({P24, P25, P45} : Set ℂ)) (n345 : ¬ Collinear ℝ ({P34, P35, P45} : Set ℂ)) :
    ∃ Q₁ Q₂ Q₃ Q₄ Q₅ : ℂ,
      (Cospherical ({P23, P24, P34, Q₁} : Set ℂ) ∧ Cospherical ({P23, P25, P35, Q₁} : Set ℂ) ∧
        Cospherical ({P24, P25, P45, Q₁} : Set ℂ) ∧ Cospherical ({P34, P35, P45, Q₁} : Set ℂ)) ∧
      (Cospherical ({P13, P14, P34, Q₂} : Set ℂ) ∧ Cospherical ({P13, P15, P35, Q₂} : Set ℂ) ∧
        Cospherical ({P14, P15, P45, Q₂} : Set ℂ) ∧ Cospherical ({P34, P35, P45, Q₂} : Set ℂ)) ∧
      (Cospherical ({P12, P14, P24, Q₃} : Set ℂ) ∧ Cospherical ({P12, P15, P25, Q₃} : Set ℂ) ∧
        Cospherical ({P14, P15, P45, Q₃} : Set ℂ) ∧ Cospherical ({P24, P25, P45, Q₃} : Set ℂ)) ∧
      (Cospherical ({P12, P13, P23, Q₄} : Set ℂ) ∧ Cospherical ({P12, P15, P25, Q₄} : Set ℂ) ∧
        Cospherical ({P13, P15, P35, Q₄} : Set ℂ) ∧ Cospherical ({P23, P25, P35, Q₄} : Set ℂ)) ∧
      (Cospherical ({P12, P13, P23, Q₅} : Set ℂ) ∧ Cospherical ({P12, P14, P24, Q₅} : Set ℂ) ∧
        Cospherical ({P13, P14, P34, Q₅} : Set ℂ) ∧ Cospherical ({P23, P24, P34, Q₅} : Set ℂ)) ∧
      (Cospherical ({Q₁, Q₂, Q₃, Q₄, Q₅} : Set ℂ) ∨ Collinear ℝ ({Q₁, Q₂, Q₃, Q₄, Q₅} : Set ℂ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hM
  obtain ⟨e12, z12⟩ := l14b_second h1 h2 d12 m12
  obtain ⟨e13, z13⟩ := l14b_second h1 h3 d13 m13
  obtain ⟨e14, z14⟩ := l14b_second h1 h4 d14 m14
  obtain ⟨e15, z15⟩ := l14b_second h1 h5 d15 m15
  obtain ⟨e23, z23⟩ := l14b_second h2 h3 d23 m23
  obtain ⟨e24, z24⟩ := l14b_second h2 h4 d24 m24
  obtain ⟨e25, z25⟩ := l14b_second h2 h5 d25 m25
  obtain ⟨e34, z34⟩ := l14b_second h3 h4 d34 m34
  obtain ⟨e35, z35⟩ := l14b_second h3 h5 d35 m35
  obtain ⟨e45, z45⟩ := l14b_second h4 h5 d45 m45
  have nc : ∀ {a b c : ℂ} {x y z : ℂ}, a - M = x → b - M = y → c - M = z →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) → ¬ Collinear ℝ ({x, y, z} : Set ℂ) :=
    fun ea eb ec hn h => hn (l14b_collinear_sub (by rw [ea, eb, ec]; exact h))
  obtain ⟨X₁, X₂, X₃, X₄, X₅, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩,
    ⟨d1, d2, d3, d4⟩, ⟨f1, f2, f3, f4⟩, hfin⟩ :=
    clifford_two _ _ _ _ _ z12 z13 z14 z15 z23 z24 z25 z34 z35 z45
      (nc e12 e13 e23 n123) (nc e12 e14 e24 n124) (nc e12 e15 e25 n125) (nc e13 e14 e34 n134)
      (nc e13 e15 e35 n135) (nc e14 e15 e45 n145) (nc e23 e24 e34 n234) (nc e23 e25 e35 n235)
      (nc e24 e25 e45 n245) (nc e34 e35 e45 n345)
  have himg : ({X₁ + M, X₂ + M, X₃ + M, X₄ + M, X₅ + M} : Set ℂ) =
      (· + M) '' {X₁, X₂, X₃, X₄, X₅} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
  refine ⟨X₁ + M, X₂ + M, X₃ + M, X₄ + M, X₅ + M,
    ⟨l14b_gam e23 e24 e34 a1 n234, l14b_gam e23 e25 e35 a2 n235, l14b_gam e24 e25 e45 a3 n245,
      l14b_gam e34 e35 e45 a4 n345⟩,
    ⟨l14b_gam e13 e14 e34 b1 n134, l14b_gam e13 e15 e35 b2 n135, l14b_gam e14 e15 e45 b3 n145,
      l14b_gam e34 e35 e45 b4 n345⟩,
    ⟨l14b_gam e12 e14 e24 c1 n124, l14b_gam e12 e15 e25 c2 n125, l14b_gam e14 e15 e45 c3 n145,
      l14b_gam e24 e25 e45 c4 n245⟩,
    ⟨l14b_gam e12 e13 e23 d1 n123, l14b_gam e12 e15 e25 d2 n125, l14b_gam e13 e15 e35 d3 n135,
      l14b_gam e23 e25 e35 d4 n235⟩,
    ⟨l14b_gam e12 e13 e23 f1 n123, l14b_gam e12 e14 e24 f2 n124, l14b_gam e13 e14 e34 f3 n134,
      l14b_gam e23 e24 e34 f4 n234⟩, ?_⟩
  rw [himg]
  rcases hfin with h | h
  · exact Or.inl (l14b_cospherical_add M h)
  · exact Or.inr (l14b_collinear_add M h)


/-! ### Clifford's third theorem (n = 6) -/

theorem l14b_nc {a b c x y z M : ℂ} (ea : a - M = x) (eb : b - M = y) (ec : c - M = z)
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : ¬ Collinear ℝ ({x, y, z} : Set ℂ) :=
  fun h => hn (l14b_collinear_sub (by rw [ea, eb, ec]; exact h))

/-- The library's Clifford point of four circles, translated back by `M`, lies on the four `Γ`
circles (stated with `Cospherical` in the original coordinates). -/
theorem l14b_cp {M Pij Pik Pil Pjk Pjl Pkl ci cj ck cl : ℂ}
    (eij : Pij - M = secondInter ci cj) (eik : Pik - M = secondInter ci ck)
    (eil : Pil - M = secondInter ci cl) (ejk : Pjk - M = secondInter cj ck)
    (ejl : Pjl - M = secondInter cj cl) (ekl : Pkl - M = secondInter ck cl)
    (zij : secondInter ci cj ≠ 0) (zik : secondInter ci ck ≠ 0) (zil : secondInter ci cl ≠ 0)
    (zjk : secondInter cj ck ≠ 0) (zjl : secondInter cj cl ≠ 0) (zkl : secondInter ck cl ≠ 0)
    (nijk : ¬ Collinear ℝ ({Pij, Pik, Pjk} : Set ℂ)) (nijl : ¬ Collinear ℝ ({Pij, Pil, Pjl} : Set ℂ))
    (nikl : ¬ Collinear ℝ ({Pik, Pil, Pkl} : Set ℂ)) (njkl : ¬ Collinear ℝ ({Pjk, Pjl, Pkl} : Set ℂ)) :
    Cospherical ({Pij, Pik, Pjk, cliffordPoint ci cj ck cl + M} : Set ℂ) ∧
      Cospherical ({Pij, Pil, Pjl, cliffordPoint ci cj ck cl + M} : Set ℂ) ∧
      Cospherical ({Pik, Pil, Pkl, cliffordPoint ci cj ck cl + M} : Set ℂ) ∧
      Cospherical ({Pjk, Pjl, Pkl, cliffordPoint ci cj ck cl + M} : Set ℂ) := by
  obtain ⟨x1, x2, x3, x4⟩ := cliffordPoint_mem_gams ci cj ck cl zij zik zil zjk zjl zkl
    (l14b_nc eij eik ejk nijk) (l14b_nc eij eil ejl nijl) (l14b_nc eik eil ekl nikl)
    (l14b_nc ejk ejl ekl njkl)
  exact ⟨l14b_gam eij eik ejk x1 nijk, l14b_gam eij eil ejl x2 nijl, l14b_gam eik eil ekl x3 nikl,
    l14b_gam ejk ejl ekl x4 njkl⟩

theorem l14b_k {PA PB PC : ℂ → Prop} {M x y z : ℂ}
    (k : ∀ A B C : ℂ, PA A → PB B → PC C → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (ha : PA (x + M)) (hb : PB (y + M)) (hc : PC (z + M)) :
    ¬ Collinear ℝ ({x, y, z} : Set ℂ) := by
  intro h
  apply k _ _ _ ha hb hc
  have := l14b_collinear_add M h
  simpa only [Set.image_insert_eq, Set.image_singleton] using this

theorem l14b_six (M : ℂ) {x₁ x₂ x₃ x₄ x₅ Q : ℂ} {S : Sphere ℂ}
    (f : ∀ P ∈ ({x₁, x₂, x₃, x₄, x₅} : Set ℂ), P ∈ S) (g : Q ∈ S) :
    Cospherical ({x₁ + M, x₂ + M, x₃ + M, x₄ + M, x₅ + M, Q + M} : Set ℂ) := by
  have hs : ({x₁ + M, x₂ + M, x₃ + M, x₄ + M, x₅ + M, Q + M} : Set ℂ) =
      (· + M) '' {x₁, x₂, x₃, x₄, x₅, Q} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
  rw [hs]
  refine l14b_cospherical_add M ⟨S.center, S.radius, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact mem_sphere.1 g
    | exact mem_sphere.1 (f _ (by simp))

/-- **Clifford's third circle theorem (n = 6)**, Mathlib-only statement. The Clifford point of
four circles is quantified by its defining property (a point on the four `Γ` circles of the
triples); the non-degeneracy hypotheses `m₁ … m₆` are required for **every** such choice. -/
theorem l14_clifford_three (M : ℂ) (s₁ s₂ s₃ s₄ s₅ s₆ : Sphere ℂ)
    (hM : M ∈ s₁ ∧ M ∈ s₂ ∧ M ∈ s₃ ∧ M ∈ s₄ ∧ M ∈ s₅ ∧ M ∈ s₆)
    (d12 : s₁.center ≠ s₂.center)
    (d13 : s₁.center ≠ s₃.center)
    (d14 : s₁.center ≠ s₄.center)
    (d15 : s₁.center ≠ s₅.center)
    (d16 : s₁.center ≠ s₆.center)
    (d23 : s₂.center ≠ s₃.center)
    (d24 : s₂.center ≠ s₄.center)
    (d25 : s₂.center ≠ s₅.center)
    (d26 : s₂.center ≠ s₆.center)
    (d34 : s₃.center ≠ s₄.center)
    (d35 : s₃.center ≠ s₅.center)
    (d36 : s₃.center ≠ s₆.center)
    (d45 : s₄.center ≠ s₅.center)
    (d46 : s₄.center ≠ s₆.center)
    (d56 : s₅.center ≠ s₆.center)
    (P12 P13 P14 P15 P16 P23 P24 P25 P26 P34 P35 P36 P45 P46 P56 : ℂ)
    (m12 : P12 ∈ s₁ ∧ P12 ∈ s₂ ∧ P12 ≠ M)
    (m13 : P13 ∈ s₁ ∧ P13 ∈ s₃ ∧ P13 ≠ M)
    (m14 : P14 ∈ s₁ ∧ P14 ∈ s₄ ∧ P14 ≠ M)
    (m15 : P15 ∈ s₁ ∧ P15 ∈ s₅ ∧ P15 ≠ M)
    (m16 : P16 ∈ s₁ ∧ P16 ∈ s₆ ∧ P16 ≠ M)
    (m23 : P23 ∈ s₂ ∧ P23 ∈ s₃ ∧ P23 ≠ M)
    (m24 : P24 ∈ s₂ ∧ P24 ∈ s₄ ∧ P24 ≠ M)
    (m25 : P25 ∈ s₂ ∧ P25 ∈ s₅ ∧ P25 ≠ M)
    (m26 : P26 ∈ s₂ ∧ P26 ∈ s₆ ∧ P26 ≠ M)
    (m34 : P34 ∈ s₃ ∧ P34 ∈ s₄ ∧ P34 ≠ M)
    (m35 : P35 ∈ s₃ ∧ P35 ∈ s₅ ∧ P35 ≠ M)
    (m36 : P36 ∈ s₃ ∧ P36 ∈ s₆ ∧ P36 ≠ M)
    (m45 : P45 ∈ s₄ ∧ P45 ∈ s₅ ∧ P45 ≠ M)
    (m46 : P46 ∈ s₄ ∧ P46 ∈ s₆ ∧ P46 ≠ M)
    (m56 : P56 ∈ s₅ ∧ P56 ∈ s₆ ∧ P56 ≠ M)
    (n123 : ¬ Collinear ℝ ({P12, P13, P23} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({P12, P14, P24} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({P12, P15, P25} : Set ℂ))
    (n126 : ¬ Collinear ℝ ({P12, P16, P26} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({P13, P14, P34} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({P13, P15, P35} : Set ℂ))
    (n136 : ¬ Collinear ℝ ({P13, P16, P36} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({P14, P15, P45} : Set ℂ))
    (n146 : ¬ Collinear ℝ ({P14, P16, P46} : Set ℂ))
    (n156 : ¬ Collinear ℝ ({P15, P16, P56} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({P23, P24, P34} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({P23, P25, P35} : Set ℂ))
    (n236 : ¬ Collinear ℝ ({P23, P26, P36} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({P24, P25, P45} : Set ℂ))
    (n246 : ¬ Collinear ℝ ({P24, P26, P46} : Set ℂ))
    (n256 : ¬ Collinear ℝ ({P25, P26, P56} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({P34, P35, P45} : Set ℂ))
    (n346 : ¬ Collinear ℝ ({P34, P36, P46} : Set ℂ))
    (n356 : ¬ Collinear ℝ ({P35, P36, P56} : Set ℂ))
    (n456 : ¬ Collinear ℝ ({P45, P46, P56} : Set ℂ))
    (k6 : ∀ A B C : ℂ, (Cospherical ({P12, P13, P23, A} : Set ℂ) ∧ Cospherical ({P12, P14, P24, A} : Set ℂ) ∧ Cospherical ({P13, P14, P34, A} : Set ℂ) ∧ Cospherical ({P23, P24, P34, A} : Set ℂ)) → (Cospherical ({P12, P13, P23, B} : Set ℂ) ∧ Cospherical ({P12, P15, P25, B} : Set ℂ) ∧ Cospherical ({P13, P15, P35, B} : Set ℂ) ∧ Cospherical ({P23, P25, P35, B} : Set ℂ)) → (Cospherical ({P12, P14, P24, C} : Set ℂ) ∧ Cospherical ({P12, P15, P25, C} : Set ℂ) ∧ Cospherical ({P14, P15, P45, C} : Set ℂ) ∧ Cospherical ({P24, P25, P45, C} : Set ℂ)) → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (k5 : ∀ A B C : ℂ, (Cospherical ({P12, P13, P23, A} : Set ℂ) ∧ Cospherical ({P12, P14, P24, A} : Set ℂ) ∧ Cospherical ({P13, P14, P34, A} : Set ℂ) ∧ Cospherical ({P23, P24, P34, A} : Set ℂ)) → (Cospherical ({P12, P13, P23, B} : Set ℂ) ∧ Cospherical ({P12, P16, P26, B} : Set ℂ) ∧ Cospherical ({P13, P16, P36, B} : Set ℂ) ∧ Cospherical ({P23, P26, P36, B} : Set ℂ)) → (Cospherical ({P12, P14, P24, C} : Set ℂ) ∧ Cospherical ({P12, P16, P26, C} : Set ℂ) ∧ Cospherical ({P14, P16, P46, C} : Set ℂ) ∧ Cospherical ({P24, P26, P46, C} : Set ℂ)) → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (k4 : ∀ A B C : ℂ, (Cospherical ({P12, P13, P23, A} : Set ℂ) ∧ Cospherical ({P12, P15, P25, A} : Set ℂ) ∧ Cospherical ({P13, P15, P35, A} : Set ℂ) ∧ Cospherical ({P23, P25, P35, A} : Set ℂ)) → (Cospherical ({P12, P13, P23, B} : Set ℂ) ∧ Cospherical ({P12, P16, P26, B} : Set ℂ) ∧ Cospherical ({P13, P16, P36, B} : Set ℂ) ∧ Cospherical ({P23, P26, P36, B} : Set ℂ)) → (Cospherical ({P12, P15, P25, C} : Set ℂ) ∧ Cospherical ({P12, P16, P26, C} : Set ℂ) ∧ Cospherical ({P15, P16, P56, C} : Set ℂ) ∧ Cospherical ({P25, P26, P56, C} : Set ℂ)) → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (k3 : ∀ A B C : ℂ, (Cospherical ({P12, P14, P24, A} : Set ℂ) ∧ Cospherical ({P12, P15, P25, A} : Set ℂ) ∧ Cospherical ({P14, P15, P45, A} : Set ℂ) ∧ Cospherical ({P24, P25, P45, A} : Set ℂ)) → (Cospherical ({P12, P14, P24, B} : Set ℂ) ∧ Cospherical ({P12, P16, P26, B} : Set ℂ) ∧ Cospherical ({P14, P16, P46, B} : Set ℂ) ∧ Cospherical ({P24, P26, P46, B} : Set ℂ)) → (Cospherical ({P12, P15, P25, C} : Set ℂ) ∧ Cospherical ({P12, P16, P26, C} : Set ℂ) ∧ Cospherical ({P15, P16, P56, C} : Set ℂ) ∧ Cospherical ({P25, P26, P56, C} : Set ℂ)) → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (k2 : ∀ A B C : ℂ, (Cospherical ({P13, P14, P34, A} : Set ℂ) ∧ Cospherical ({P13, P15, P35, A} : Set ℂ) ∧ Cospherical ({P14, P15, P45, A} : Set ℂ) ∧ Cospherical ({P34, P35, P45, A} : Set ℂ)) → (Cospherical ({P13, P14, P34, B} : Set ℂ) ∧ Cospherical ({P13, P16, P36, B} : Set ℂ) ∧ Cospherical ({P14, P16, P46, B} : Set ℂ) ∧ Cospherical ({P34, P36, P46, B} : Set ℂ)) → (Cospherical ({P13, P15, P35, C} : Set ℂ) ∧ Cospherical ({P13, P16, P36, C} : Set ℂ) ∧ Cospherical ({P15, P16, P56, C} : Set ℂ) ∧ Cospherical ({P35, P36, P56, C} : Set ℂ)) → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (k1 : ∀ A B C : ℂ, (Cospherical ({P23, P24, P34, A} : Set ℂ) ∧ Cospherical ({P23, P25, P35, A} : Set ℂ) ∧ Cospherical ({P24, P25, P45, A} : Set ℂ) ∧ Cospherical ({P34, P35, P45, A} : Set ℂ)) → (Cospherical ({P23, P24, P34, B} : Set ℂ) ∧ Cospherical ({P23, P26, P36, B} : Set ℂ) ∧ Cospherical ({P24, P26, P46, B} : Set ℂ) ∧ Cospherical ({P34, P36, P46, B} : Set ℂ)) → (Cospherical ({P23, P25, P35, C} : Set ℂ) ∧ Cospherical ({P23, P26, P36, C} : Set ℂ) ∧ Cospherical ({P25, P26, P56, C} : Set ℂ) ∧ Cospherical ({P35, P36, P56, C} : Set ℂ)) → ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    : ∃ Q1234 Q1235 Q1236 Q1245 Q1246 Q1256 Q1345 Q1346 Q1356 Q1456 Q2345 Q2346 Q2356 Q2456 Q3456 Z : ℂ,
      (Cospherical ({P12, P13, P23, Q1234} : Set ℂ) ∧ Cospherical ({P12, P14, P24, Q1234} : Set ℂ) ∧ Cospherical ({P13, P14, P34, Q1234} : Set ℂ) ∧ Cospherical ({P23, P24, P34, Q1234} : Set ℂ)) ∧
      (Cospherical ({P12, P13, P23, Q1235} : Set ℂ) ∧ Cospherical ({P12, P15, P25, Q1235} : Set ℂ) ∧ Cospherical ({P13, P15, P35, Q1235} : Set ℂ) ∧ Cospherical ({P23, P25, P35, Q1235} : Set ℂ)) ∧
      (Cospherical ({P12, P13, P23, Q1236} : Set ℂ) ∧ Cospherical ({P12, P16, P26, Q1236} : Set ℂ) ∧ Cospherical ({P13, P16, P36, Q1236} : Set ℂ) ∧ Cospherical ({P23, P26, P36, Q1236} : Set ℂ)) ∧
      (Cospherical ({P12, P14, P24, Q1245} : Set ℂ) ∧ Cospherical ({P12, P15, P25, Q1245} : Set ℂ) ∧ Cospherical ({P14, P15, P45, Q1245} : Set ℂ) ∧ Cospherical ({P24, P25, P45, Q1245} : Set ℂ)) ∧
      (Cospherical ({P12, P14, P24, Q1246} : Set ℂ) ∧ Cospherical ({P12, P16, P26, Q1246} : Set ℂ) ∧ Cospherical ({P14, P16, P46, Q1246} : Set ℂ) ∧ Cospherical ({P24, P26, P46, Q1246} : Set ℂ)) ∧
      (Cospherical ({P12, P15, P25, Q1256} : Set ℂ) ∧ Cospherical ({P12, P16, P26, Q1256} : Set ℂ) ∧ Cospherical ({P15, P16, P56, Q1256} : Set ℂ) ∧ Cospherical ({P25, P26, P56, Q1256} : Set ℂ)) ∧
      (Cospherical ({P13, P14, P34, Q1345} : Set ℂ) ∧ Cospherical ({P13, P15, P35, Q1345} : Set ℂ) ∧ Cospherical ({P14, P15, P45, Q1345} : Set ℂ) ∧ Cospherical ({P34, P35, P45, Q1345} : Set ℂ)) ∧
      (Cospherical ({P13, P14, P34, Q1346} : Set ℂ) ∧ Cospherical ({P13, P16, P36, Q1346} : Set ℂ) ∧ Cospherical ({P14, P16, P46, Q1346} : Set ℂ) ∧ Cospherical ({P34, P36, P46, Q1346} : Set ℂ)) ∧
      (Cospherical ({P13, P15, P35, Q1356} : Set ℂ) ∧ Cospherical ({P13, P16, P36, Q1356} : Set ℂ) ∧ Cospherical ({P15, P16, P56, Q1356} : Set ℂ) ∧ Cospherical ({P35, P36, P56, Q1356} : Set ℂ)) ∧
      (Cospherical ({P14, P15, P45, Q1456} : Set ℂ) ∧ Cospherical ({P14, P16, P46, Q1456} : Set ℂ) ∧ Cospherical ({P15, P16, P56, Q1456} : Set ℂ) ∧ Cospherical ({P45, P46, P56, Q1456} : Set ℂ)) ∧
      (Cospherical ({P23, P24, P34, Q2345} : Set ℂ) ∧ Cospherical ({P23, P25, P35, Q2345} : Set ℂ) ∧ Cospherical ({P24, P25, P45, Q2345} : Set ℂ) ∧ Cospherical ({P34, P35, P45, Q2345} : Set ℂ)) ∧
      (Cospherical ({P23, P24, P34, Q2346} : Set ℂ) ∧ Cospherical ({P23, P26, P36, Q2346} : Set ℂ) ∧ Cospherical ({P24, P26, P46, Q2346} : Set ℂ) ∧ Cospherical ({P34, P36, P46, Q2346} : Set ℂ)) ∧
      (Cospherical ({P23, P25, P35, Q2356} : Set ℂ) ∧ Cospherical ({P23, P26, P36, Q2356} : Set ℂ) ∧ Cospherical ({P25, P26, P56, Q2356} : Set ℂ) ∧ Cospherical ({P35, P36, P56, Q2356} : Set ℂ)) ∧
      (Cospherical ({P24, P25, P45, Q2456} : Set ℂ) ∧ Cospherical ({P24, P26, P46, Q2456} : Set ℂ) ∧ Cospherical ({P25, P26, P56, Q2456} : Set ℂ) ∧ Cospherical ({P45, P46, P56, Q2456} : Set ℂ)) ∧
      (Cospherical ({P34, P35, P45, Q3456} : Set ℂ) ∧ Cospherical ({P34, P36, P46, Q3456} : Set ℂ) ∧ Cospherical ({P35, P36, P56, Q3456} : Set ℂ) ∧ Cospherical ({P45, P46, P56, Q3456} : Set ℂ)) ∧
      Cospherical ({Q1234, Q1235, Q1245, Q1345, Q2345, Z} : Set ℂ) ∧
      Cospherical ({Q1234, Q1236, Q1246, Q1346, Q2346, Z} : Set ℂ) ∧
      Cospherical ({Q1235, Q1236, Q1256, Q1356, Q2356, Z} : Set ℂ) ∧
      Cospherical ({Q1245, Q1246, Q1256, Q1456, Q2456, Z} : Set ℂ) ∧
      Cospherical ({Q1345, Q1346, Q1356, Q1456, Q3456, Z} : Set ℂ) ∧
      Cospherical ({Q2345, Q2346, Q2356, Q2456, Q3456, Z} : Set ℂ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  obtain ⟨e12, z12⟩ := l14b_second h1 h2 d12 m12
  obtain ⟨e13, z13⟩ := l14b_second h1 h3 d13 m13
  obtain ⟨e14, z14⟩ := l14b_second h1 h4 d14 m14
  obtain ⟨e15, z15⟩ := l14b_second h1 h5 d15 m15
  obtain ⟨e16, z16⟩ := l14b_second h1 h6 d16 m16
  obtain ⟨e23, z23⟩ := l14b_second h2 h3 d23 m23
  obtain ⟨e24, z24⟩ := l14b_second h2 h4 d24 m24
  obtain ⟨e25, z25⟩ := l14b_second h2 h5 d25 m25
  obtain ⟨e26, z26⟩ := l14b_second h2 h6 d26 m26
  obtain ⟨e34, z34⟩ := l14b_second h3 h4 d34 m34
  obtain ⟨e35, z35⟩ := l14b_second h3 h5 d35 m35
  obtain ⟨e36, z36⟩ := l14b_second h3 h6 d36 m36
  obtain ⟨e45, z45⟩ := l14b_second h4 h5 d45 m45
  obtain ⟨e46, z46⟩ := l14b_second h4 h6 d46 m46
  obtain ⟨e56, z56⟩ := l14b_second h5 h6 d56 m56
  have C1234 := l14b_cp e12 e13 e14 e23 e24 e34 z12 z13 z14 z23 z24 z34 n123 n124 n134 n234
  have C1235 := l14b_cp e12 e13 e15 e23 e25 e35 z12 z13 z15 z23 z25 z35 n123 n125 n135 n235
  have C1236 := l14b_cp e12 e13 e16 e23 e26 e36 z12 z13 z16 z23 z26 z36 n123 n126 n136 n236
  have C1245 := l14b_cp e12 e14 e15 e24 e25 e45 z12 z14 z15 z24 z25 z45 n124 n125 n145 n245
  have C1246 := l14b_cp e12 e14 e16 e24 e26 e46 z12 z14 z16 z24 z26 z46 n124 n126 n146 n246
  have C1256 := l14b_cp e12 e15 e16 e25 e26 e56 z12 z15 z16 z25 z26 z56 n125 n126 n156 n256
  have C1345 := l14b_cp e13 e14 e15 e34 e35 e45 z13 z14 z15 z34 z35 z45 n134 n135 n145 n345
  have C1346 := l14b_cp e13 e14 e16 e34 e36 e46 z13 z14 z16 z34 z36 z46 n134 n136 n146 n346
  have C1356 := l14b_cp e13 e15 e16 e35 e36 e56 z13 z15 z16 z35 z36 z56 n135 n136 n156 n356
  have C1456 := l14b_cp e14 e15 e16 e45 e46 e56 z14 z15 z16 z45 z46 z56 n145 n146 n156 n456
  have C2345 := l14b_cp e23 e24 e25 e34 e35 e45 z23 z24 z25 z34 z35 z45 n234 n235 n245 n345
  have C2346 := l14b_cp e23 e24 e26 e34 e36 e46 z23 z24 z26 z34 z36 z46 n234 n236 n246 n346
  have C2356 := l14b_cp e23 e25 e26 e35 e36 e56 z23 z25 z26 z35 z36 z56 n235 n236 n256 n356
  have C2456 := l14b_cp e24 e25 e26 e45 e46 e56 z24 z25 z26 z45 z46 z56 n245 n246 n256 n456
  have C3456 := l14b_cp e34 e35 e36 e45 e46 e56 z34 z35 z36 z45 z46 z56 n345 n346 n356 n456
  obtain ⟨Z, ⟨f1, g1⟩, ⟨f2, g2⟩, ⟨f3, g3⟩, ⟨f4, g4⟩, ⟨f5, g5⟩, ⟨f6, g6⟩⟩ :=
    clifford_three _ _ _ _ _ _ z12 z13 z14 z15 z16 z23 z24 z25 z26 z34 z35 z36 z45 z46 z56 (l14b_nc e12 e13 e23 n123) (l14b_nc e12 e14 e24 n124) (l14b_nc e12 e15 e25 n125) (l14b_nc e12 e16 e26 n126) (l14b_nc e13 e14 e34 n134) (l14b_nc e13 e15 e35 n135) (l14b_nc e13 e16 e36 n136) (l14b_nc e14 e15 e45 n145) (l14b_nc e14 e16 e46 n146) (l14b_nc e15 e16 e56 n156) (l14b_nc e23 e24 e34 n234) (l14b_nc e23 e25 e35 n235) (l14b_nc e23 e26 e36 n236) (l14b_nc e24 e25 e45 n245) (l14b_nc e24 e26 e46 n246) (l14b_nc e25 e26 e56 n256) (l14b_nc e34 e35 e45 n345) (l14b_nc e34 e36 e46 n346) (l14b_nc e35 e36 e56 n356) (l14b_nc e45 e46 e56 n456)
      (l14b_k k6 C1234 C1235 C1245) (l14b_k k5 C1234 C1236 C1246) (l14b_k k4 C1235 C1236 C1256) (l14b_k k3 C1245 C1246 C1256) (l14b_k k2 C1345 C1346 C1356) (l14b_k k1 C2345 C2346 C2356)
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, C1234, C1235, C1236, C1245, C1246, C1256, C1345, C1346, C1356, C1456, C2345, C2346, C2356, C2456, C3456, l14b_six M f1 g1, l14b_six M f2 g2, l14b_six M f3 g3, l14b_six M f4 g4, l14b_six M f5 g5, l14b_six M f6 g6⟩

/-! ### Witnesses -/

theorem l14b_mem {z c : ℂ} {r : ℝ} (h : (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 = r) :
    z ∈ (⟨c, Real.sqrt r⟩ : Sphere ℂ) := by
  rw [mem_sphere, Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [sub_re, sub_im]
  linear_combination h

theorem l14b_cosph {s : Set ℂ} (o : ℂ) (r : ℝ)
    (h : ∀ x ∈ s, (x.re - o.re) ^ 2 + (x.im - o.im) ^ 2 = r) : Cospherical s :=
  ⟨o, Real.sqrt r, fun x hx => l14b_mem (h x hx)⟩

theorem l14b_not_collinear {a b c : ℂ}
    (h : (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re) ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_re, add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Witness for `l14_clifford_one`: four circles through `M = 0` with centres `3 - i`, `1 + 3i`,
`-1 + 3i`, `-3 - i`; the six second intersections `4+2i, 2+2i, -2i, 6i, -2+2i, -4+2i`; the four
`Γ` circles with centres `3+5i, 1+i, -1+i, -3+5i`; the Clifford point `4i`, distinct from all six
second intersections. -/
theorem l14w_clifford_one :
    ((⟨0, 0⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ)) ∧
    ((⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    (((⟨4, 2⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨4, 2⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨4, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨2, 2⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨2, 2⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨2, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, -2⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, 6⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 6⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 6⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-2, 2⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-2, 2⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-2, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-4, 2⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-4, 2⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-4, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (¬ Collinear ℝ ({(⟨4, 2⟩ : ℂ), (⟨2, 2⟩ : ℂ), (⟨0, 6⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨4, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-2, 2⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨2, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-4, 2⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, 6⟩ : ℂ), (⟨-2, 2⟩ : ℂ), (⟨-4, 2⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨4, 2⟩ : ℂ), (⟨2, 2⟩ : ℂ), (⟨0, 6⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨4, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-2, 2⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨2, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-4, 2⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, 6⟩ : ℂ), (⟨-2, 2⟩ : ℂ), (⟨-4, 2⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨4, 2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨2, 2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨0, 6⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨-2, 2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨-4, 2⟩ : ℂ)) := by
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num)⟩) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_cosph (⟨3, 5⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨1, 1⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-1, 1⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 5⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  exact by norm_num [Complex.ext_iff]

/-- Witness for `l14_clifford_two`: five circles through `M = 0` with centres `-3-2i, -i, -1-2i, -2-i, -2+3i`; all ten second intersections, the ten `Γ` circles (explicit centre and squared radius), the five Clifford points `Q₁ … Q₅` (pairwise distinct, distinct from every second intersection) and the Clifford circle (centre `(-16 - 81i)/17`); the `Q`'s are not collinear, so the conclusion holds through its `Cospherical` branch. -/
theorem l14w_clifford_two :
    ((⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ)) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    (((⟨3/5, -9/5⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨3/5, -9/5⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨3/5, -9/5⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, -4⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨0, -4⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, -4⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-1, 1⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-1, 1⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-1, 1⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-5, 1⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-5, 1⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-5, 1⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨1, -1⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨1, -1⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨1, -1⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, -2⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-4/5, -2/5⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨-4/5, -2/5⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-4/5, -2/5⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-3, -3⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-3, -3⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-3, -3⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-35/13, -7/13⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-35/13, -7/13⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-35/13, -7/13⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-4, 0⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-4, 0⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-4, 0⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (¬ Collinear ℝ ({(⟨3/5, -9/5⟩ : ℂ), (⟨0, -4⟩ : ℂ), (⟨1, -1⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨3/5, -9/5⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨0, -2⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨3/5, -9/5⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, -4⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨-3, -3⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, -4⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨-1, 1⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4, 0⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨1, -1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-3, -3⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨1, -1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, -2⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-4, 0⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨-3, -3⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-4, 0⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨0, -4⟩ : ℂ), (⟨1, -1⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨0, -4⟩ : ℂ), (⟨1, -1⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-1, 1⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -2⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-1, 1⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-3, -3⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -2⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-3, -3⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-91/17, -41/17⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨-91/17, -41/17⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨20/17, -158/17⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-29/17, 3/17⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-52/17, -4/17⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-29/17, 3/17⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-52/17, -4/17⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-52/17, -4/17⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) := by
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num)⟩) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_cosph (⟨8, -5⟩ : ℂ) (65 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-1/5, -2/5⟩ : ℂ) (13/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-6/7, -11/7⟩ : ℂ) (325/49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (25 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨8, -5⟩ : ℂ) (65 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-5, -6⟩ : ℂ) (49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-10, -9⟩ : ℂ) (125 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-7/5, -26/5⟩ : ℂ) (117/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-1/5, -2/5⟩ : ℂ) (13/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-5, -6⟩ : ℂ) (49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-8/3, -7/3⟩ : ℂ) (65/9 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-6/7, -11/7⟩ : ℂ) (325/49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-10, -9⟩ : ℂ) (125 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-43/11, -18/11⟩ : ℂ) (325/121 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (25 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-7/5, -26/5⟩ : ℂ) (117/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-8/3, -7/3⟩ : ℂ) (65/9 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-43/11, -18/11⟩ : ℂ) (325/121 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-16/17, -81/17⟩ : ℂ) (25 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  exact by norm_num [Complex.ext_iff]

end Clifford
