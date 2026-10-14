import Mathlib

/-!
# Clifford's first circle theorem (n = 4)

Four circles `C₁, …, C₄` pass through a common point `M`, which we place at the origin of `ℂ`.
Circle `i` is the circle with centre `cᵢ` through `0`.  For `i ≠ j` the circles `i, j` meet again at
`secondInter cᵢ cⱼ`.  For each triple `{i, j, k}` the three second intersection points
`P_ij, P_ik, P_jk` determine a circle `Γ_ijk` (`gam cᵢ cⱼ cₖ`); Clifford's theorem says that the four
circles `Γ_123, Γ_124, Γ_134, Γ_234` pass through a common point.

Circles are Mathlib's `EuclideanGeometry.Sphere ℂ`, and "lies on" is `∈` (i.e. `dist p s.center = s.radius`).

## Proof strategy
Everything is computed in conjugate coordinates: a point `z` is paired with `conj z`.  The algebra is
done over an arbitrary field `K` with *independent* variables `cᵢ, dᵢ` (playing `cᵢ, conj cᵢ`), which
keeps the certificate polynomials small, and is then specialised to `dᵢ = conj cᵢ`.
The common point is the explicit rational function `XN / NN`.  `NN ≠ 0` follows from an explicit
resultant identity `(A₁ c₄ + A₀) NN + B₀ conj(NN) = d₄ (d₁ - d₄)(d₂ - d₄)(d₃ - d₄) e₁₂ e₁₃ e₂₃ L₁₂₃ D₁₂₃`.
-/

open EuclideanGeometry ComplexConjugate

namespace Clifford

/-! ### Generic algebra over a field -/

section Generic

variable {K : Type*} [Field K]

/-- Second intersection, in conjugate coordinates (`dᵢ` plays the role of `conj cᵢ`). -/
def sec (c1 d1 c2 d2 : K) : K := (d1 * c2 - c1 * d2) / (d1 - d2)

/-- `ee = 0` iff the origin and the two centres are collinear. -/
def ee (c1 d1 c2 d2 : K) : K := c1 * d2 - c2 * d1

/-- `LL = 0` iff the three centres are collinear. -/
def LL (c1 d1 c2 d2 c3 d3 : K) : K := c1 * (d2 - d3) - d1 * (c2 - c3) + (c2 * d3 - c3 * d2)

/-- `DD = 0` iff the second intersection points of a triple are collinear (given the rest). -/
def DD (c1 d1 c2 d2 c3 d3 : K) : K :=
  c1*c2*d1*d3 - c1*c2*d2*d3 - c1*c3*d1*d2 + c1*c3*d2*d3 + c2*c3*d1*d2 - c2*c3*d1*d3

/-- Denominator of the common point. -/
def NN (c1 d1 c2 d2 c3 d3 c4 d4 : K) : K :=
  c1*c2*d1*d3^2*d4 - c1*c2*d1*d3*d4^2 - c1*c2*d2*d3^2*d4 + c1*c2*d2*d3*d4^2 - c1*c3*d1*d2^2*d4 + c1*c3*d1*d2*d4^2 + c1*c3*d2^2*d3*d4 - c1*c3*d2*d3*d4^2 + c1*c4*d1*d2^2*d3 - c1*c4*d1*d2*d3^2 - c1*c4*d2^2*d3*d4 + c1*c4*d2*d3^2*d4 + c2*c3*d1^2*d2*d4 - c2*c3*d1^2*d3*d4 - c2*c3*d1*d2*d4^2 + c2*c3*d1*d3*d4^2 - c2*c4*d1^2*d2*d3 + c2*c4*d1^2*d3*d4 + c2*c4*d1*d2*d3^2 - c2*c4*d1*d3^2*d4 + c3*c4*d1^2*d2*d3 - c3*c4*d1^2*d2*d4 - c3*c4*d1*d2^2*d3 + c3*c4*d1*d2^2*d4

/-- Numerator of the common point. -/
def XN (c1 d1 c2 d2 c3 d3 c4 d4 : K) : K :=
  -c1^2*c2*d2*d3^2*d4 + c1^2*c2*d2*d3*d4^2 + c1^2*c3*d2^2*d3*d4 - c1^2*c3*d2*d3*d4^2 - c1^2*c4*d2^2*d3*d4 + c1^2*c4*d2*d3^2*d4 + c1*c2^2*d1*d3^2*d4 - c1*c2^2*d1*d3*d4^2 - c1*c3^2*d1*d2^2*d4 + c1*c3^2*d1*d2*d4^2 + c1*c4^2*d1*d2^2*d3 - c1*c4^2*d1*d2*d3^2 - c2^2*c3*d1^2*d3*d4 + c2^2*c3*d1*d3*d4^2 + c2^2*c4*d1^2*d3*d4 - c2^2*c4*d1*d3^2*d4 + c2*c3^2*d1^2*d2*d4 - c2*c3^2*d1*d2*d4^2 - c2*c4^2*d1^2*d2*d3 + c2*c4^2*d1*d2*d3^2 - c3^2*c4*d1^2*d2*d4 + c3^2*c4*d1*d2^2*d4 + c3*c4^2*d1^2*d2*d3 - c3*c4^2*d1*d2^2*d3

/-- Denominator of the circumcentre of three points (conjugate coordinates). -/
def den3 (A a B b C c : K) : K := a * (B - C) + b * (C - A) + c * (A - B)

/-- Circumcentre of three points (conjugate coordinates). -/
def ctr (A a B b C c : K) : K := (A * a * (B - C) + B * b * (C - A) + C * c * (A - B)) / den3 A a B b C c

/-- Concyclicity polynomial (cross-ratio form) of four points `A, B, C, Z`. -/
def TT (A a B b C c Z z : K) : K := (A - B) * (C - Z) * (a - c) * (b - z) - (a - b) * (c - z) * (A - C) * (B - Z)

lemma LL_swap (c1 d1 c2 d2 c3 d3 : K) : LL d1 c1 d2 c2 d3 c3 = -LL c1 d1 c2 d2 c3 d3 := by
  unfold LL; ring

lemma ee_swap (c1 d1 c2 d2 : K) : ee d1 c1 d2 c2 = -ee c1 d1 c2 d2 := by
  unfold ee; ring

lemma den3_swap (A a B b C c : K) : den3 a A b B c C = -den3 A a B b C c := by
  unfold den3; ring

lemma sec_sub_sec₁ (c1 d1 c2 d2 c3 d3 : K) (h12 : d1 - d2 ≠ 0) (h13 : d1 - d3 ≠ 0) :
    sec c1 d1 c2 d2 - sec c1 d1 c3 d3 = -(d1 * LL c1 d1 c2 d2 c3 d3) * (d1 - d2)⁻¹ * (d1 - d3)⁻¹ := by
  unfold sec LL; field_simp; ring

lemma sec_sub_sec₂ (c1 d1 c2 d2 c3 d3 : K) (h12 : d1 - d2 ≠ 0) (h23 : d2 - d3 ≠ 0) :
    sec c1 d1 c2 d2 - sec c2 d2 c3 d3 = -(d2 * LL c1 d1 c2 d2 c3 d3) * (d1 - d2)⁻¹ * (d2 - d3)⁻¹ := by
  unfold sec LL; field_simp; ring

lemma sec13_sub_X (c1 d1 c2 d2 c3 d3 c4 d4 : K) (h13 : d1 - d3 ≠ 0)
    (hN : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) :
    sec c1 d1 c3 d3 - XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4 =
      d1 * d3 * ee c2 d2 c4 d4 * LL c1 d1 c2 d2 c3 d3 * LL c1 d1 c3 d3 c4 d4 *
        (d1 - d3)⁻¹ * (NN c1 d1 c2 d2 c3 d3 c4 d4)⁻¹ := by
  rw [mul_assoc _ (d1 - d3)⁻¹, ← mul_inv, ← div_eq_mul_inv]
  rw [sec, div_sub_div _ _ h13 hN, div_left_inj' (mul_ne_zero h13 hN)]
  unfold XN NN ee LL; ring

lemma sec23_sub_X (c1 d1 c2 d2 c3 d3 c4 d4 : K) (h23 : d2 - d3 ≠ 0)
    (hN : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) :
    sec c2 d2 c3 d3 - XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4 =
      d2 * d3 * ee c1 d1 c4 d4 * LL c1 d1 c2 d2 c3 d3 * LL c2 d2 c3 d3 c4 d4 *
        (d2 - d3)⁻¹ * (NN c1 d1 c2 d2 c3 d3 c4 d4)⁻¹ := by
  rw [mul_assoc _ (d2 - d3)⁻¹, ← mul_inv, ← div_eq_mul_inv]
  rw [sec, div_sub_div _ _ h23 hN, div_left_inj' (mul_ne_zero h23 hN)]
  unfold XN NN ee LL; ring

/-- The candidate point is concyclic with the three second intersection points of triple `123`. -/
lemma TT_X (c1 d1 c2 d2 c3 d3 c4 d4 : K)
    (h12 : d1 - d2 ≠ 0) (h13 : d1 - d3 ≠ 0) (h23 : d2 - d3 ≠ 0)
    (g12 : c1 - c2 ≠ 0) (g13 : c1 - c3 ≠ 0) (g23 : c2 - c3 ≠ 0)
    (hN : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) (hN' : NN d1 c1 d2 c2 d3 c3 d4 c4 ≠ 0) :
    TT (sec c1 d1 c2 d2) (sec d1 c1 d2 c2) (sec c1 d1 c3 d3) (sec d1 c1 d3 c3)
      (sec c2 d2 c3 d3) (sec d2 c2 d3 c3)
      (XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4)
      (XN d1 c1 d2 c2 d3 c3 d4 c4 / NN d1 c1 d2 c2 d3 c3 d4 c4) = 0 := by
  unfold TT
  rw [sec_sub_sec₁ c1 d1 c2 d2 c3 d3 h12 h13, sec_sub_sec₂ c1 d1 c2 d2 c3 d3 h12 h23,
    sec_sub_sec₁ d1 c1 d2 c2 d3 c3 g12 g13, sec_sub_sec₂ d1 c1 d2 c2 d3 c3 g12 g23,
    sec13_sub_X c1 d1 c2 d2 c3 d3 c4 d4 h13 hN, sec23_sub_X c1 d1 c2 d2 c3 d3 c4 d4 h23 hN,
    sec13_sub_X d1 c1 d2 c2 d3 c3 d4 c4 g13 hN', sec23_sub_X d1 c1 d2 c2 d3 c3 d4 c4 g23 hN',
    LL_swap d1 c1 d2 c2 d3 c3, LL_swap d1 c1 d3 c3 d4 c4, LL_swap d2 c2 d3 c3 d4 c4,
    ee_swap d1 c1 d4 c4, ee_swap d2 c2 d4 c4]
  ring

/-- If `T(A,B,C,Z) = 0` then `Z` is at the same (squared, conjugate-coordinate) distance from the
circumcentre of `A, B, C` as `A` is. -/
lemma circ_aux (A a B b C c Z z : K) (hden : den3 A a B b C c ≠ 0) (hT : TT A a B b C c Z z = 0) :
    (Z - ctr A a B b C c) * (z - ctr a A b B c C) = (A - ctr A a B b C c) * (a - ctr a A b B c C) := by
  have hden' : den3 a A b B c C ≠ 0 := by rw [den3_swap]; exact neg_ne_zero.2 hden
  have key : (Z - ctr A a B b C c) * (z - ctr a A b B c C) - (A - ctr A a B b C c) * (a - ctr a A b B c C)
      = TT A a B b C c Z z / den3 a A b B c C := by
    unfold ctr
    rw [eq_div_iff hden']
    field_simp
    unfold TT den3
    ring
  rw [hT, zero_div] at key
  exact sub_eq_zero.1 key

lemma den3_sec (c1 d1 c2 d2 c3 d3 : K)
    (h12 : d1 - d2 ≠ 0) (h13 : d1 - d3 ≠ 0) (h23 : d2 - d3 ≠ 0)
    (g12 : c1 - c2 ≠ 0) (g13 : c1 - c3 ≠ 0) (g23 : c2 - c3 ≠ 0) :
    den3 (sec c1 d1 c2 d2) (sec d1 c1 d2 c2) (sec c1 d1 c3 d3) (sec d1 c1 d3 c3)
      (sec c2 d2 c3 d3) (sec d2 c2 d3 c3) =
    -(LL c1 d1 c2 d2 c3 d3 ^ 2 * DD c1 d1 c2 d2 c3 d3) /
      ((c1 - c2) * (c1 - c3) * (c2 - c3) * (d1 - d2) * (d1 - d3) * (d2 - d3)) := by
  unfold den3 sec LL DD
  field_simp
  ring

/-- Coefficient of `c4` in `NN`. -/
def Rn1 (c1 d1 c2 d2 c3 d3 d4 : K) : K :=
  c1*d1*d2^2*d3 - c1*d1*d2*d3^2 - c1*d2^2*d3*d4 + c1*d2*d3^2*d4 - c2*d1^2*d2*d3 + c2*d1^2*d3*d4 + c2*d1*d2*d3^2 - c2*d1*d3^2*d4 + c3*d1^2*d2*d3 - c3*d1^2*d2*d4 - c3*d1*d2^2*d3 + c3*d1*d2^2*d4

/-- Constant coefficient (in `c4`) of `NN`. -/
def Rn0 (c1 d1 c2 d2 c3 d3 d4 : K) : K :=
  c1*c2*d1*d3^2*d4 - c1*c2*d1*d3*d4^2 - c1*c2*d2*d3^2*d4 + c1*c2*d2*d3*d4^2 - c1*c3*d1*d2^2*d4 + c1*c3*d1*d2*d4^2 + c1*c3*d2^2*d3*d4 - c1*c3*d2*d3*d4^2 + c2*c3*d1^2*d2*d4 - c2*c3*d1^2*d3*d4 - c2*c3*d1*d2*d4^2 + c2*c3*d1*d3*d4^2

/-- Coefficient of `c4 ^ 2` in the conjugate of `NN`. -/
def Rm2 (c1 d1 c2 d2 c3 d3 : K) : K :=
  c1*c2*d1*d3 - c1*c2*d2*d3 - c1*c3*d1*d2 + c1*c3*d2*d3 + c2*c3*d1*d2 - c2*c3*d1*d3

/-- Coefficient of `c4` in the conjugate of `NN`. -/
def Rm1 (c1 d1 c2 d2 c3 d3 d4 : K) : K :=
  c1^2*c2*d2*d3 - c1^2*c2*d3*d4 - c1^2*c3*d2*d3 + c1^2*c3*d2*d4 - c1*c2^2*d1*d3 + c1*c2^2*d3*d4 + c1*c3^2*d1*d2 - c1*c3^2*d2*d4 + c2^2*c3*d1*d3 - c2^2*c3*d1*d4 - c2*c3^2*d1*d2 + c2*c3^2*d1*d4

/-- Resultant certificate (eliminating `c4`) showing `NN` and its conjugate cannot both vanish. -/
lemma resultant_NN (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    (Rm2 c1 d1 c2 d2 c3 d3 * Rn1 c1 d1 c2 d2 c3 d3 d4 * c4
        + (Rn1 c1 d1 c2 d2 c3 d3 d4 * Rm1 c1 d1 c2 d2 c3 d3 d4
          - Rm2 c1 d1 c2 d2 c3 d3 * Rn0 c1 d1 c2 d2 c3 d3 d4)) * NN c1 d1 c2 d2 c3 d3 c4 d4
      - Rn1 c1 d1 c2 d2 c3 d3 d4 ^ 2 * NN d1 c1 d2 c2 d3 c3 d4 c4 =
    d4 * (d1 - d4) * (d2 - d4) * (d3 - d4) * ee c1 d1 c2 d2 * ee c1 d1 c3 d3 * ee c2 d2 c3 d3 *
      LL c1 d1 c2 d2 c3 d3 * DD c1 d1 c2 d2 c3 d3 := by
  unfold Rn1 Rn0 Rm2 Rm1 NN ee LL DD
  ring

lemma NN_perm₁ (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    NN c1 d1 c2 d2 c4 d4 c3 d3 = -NN c1 d1 c2 d2 c3 d3 c4 d4 := by unfold NN; ring
lemma XN_perm₁ (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    XN c1 d1 c2 d2 c4 d4 c3 d3 = -XN c1 d1 c2 d2 c3 d3 c4 d4 := by unfold XN; ring
lemma NN_perm₂ (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    NN c1 d1 c3 d3 c4 d4 c2 d2 = NN c1 d1 c2 d2 c3 d3 c4 d4 := by unfold NN; ring
lemma XN_perm₂ (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    XN c1 d1 c3 d3 c4 d4 c2 d2 = XN c1 d1 c2 d2 c3 d3 c4 d4 := by unfold XN; ring
lemma NN_perm₃ (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    NN c2 d2 c3 d3 c4 d4 c1 d1 = -NN c1 d1 c2 d2 c3 d3 c4 d4 := by unfold NN; ring
lemma XN_perm₃ (c1 d1 c2 d2 c3 d3 c4 d4 : K) :
    XN c2 d2 c3 d3 c4 d4 c1 d1 = -XN c1 d1 c2 d2 c3 d3 c4 d4 := by unfold XN; ring

end Generic

/-! ### The geometric objects in `ℂ` -/

/-- The circle with centre `c` passing through the origin `M = 0`. -/
noncomputable def circ (c : ℂ) : Sphere ℂ := ⟨c, ‖c‖⟩

/-- A circle passes through the common point `M`, placed at the origin. -/
def ThroughOrigin (s : Sphere ℂ) : Prop := (0 : ℂ) ∈ s

/-- The second intersection point (other than the origin) of the circles through `0` with centres
`c₁` and `c₂`. In real coordinates, with `cᵢ = pᵢ + qᵢ i`, `a = p₁ - p₂`, `b = q₁ - q₂`,
`λ = 2 (q₁ a - p₁ b) / (a² + b²)`, this is the point `(-λ b, λ a)`. -/
noncomputable def secondInter (c₁ c₂ : ℂ) : ℂ := sec c₁ (conj c₁) c₂ (conj c₂)

/-- Circumcentre of three points of `ℂ`. -/
noncomputable def ccenter (A B C : ℂ) : ℂ := ctr A (conj A) B (conj B) C (conj C)

/-- The circle through three points `A, B, C` (meaningful when they are not collinear). -/
noncomputable def circumcircle (A B C : ℂ) : Sphere ℂ := ⟨ccenter A B C, dist A (ccenter A B C)⟩

/-- `Γ_ijk`: the circle through the three second intersection points of circles `i, j, k`. -/
noncomputable def gam (cᵢ cⱼ cₖ : ℂ) : Sphere ℂ :=
  circumcircle (secondInter cᵢ cⱼ) (secondInter cᵢ cₖ) (secondInter cⱼ cₖ)

lemma dist_eq_dist_iff (Z A O : ℂ) :
    dist Z O = dist A O ↔ (Z - O) * conj (Z - O) = (A - O) * conj (A - O) := by
  rw [Complex.dist_eq, Complex.dist_eq, Complex.mul_conj, Complex.mul_conj, Complex.ofReal_inj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  constructor
  · intro h; rw [h]
  · intro h; exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem circ_throughOrigin (c : ℂ) : ThroughOrigin (circ c) := by
  simp [ThroughOrigin, circ, EuclideanGeometry.mem_sphere, Complex.dist_eq]

lemma conj_sec (c1 d1 c2 d2 : ℂ) : conj (sec c1 d1 c2 d2) = sec (conj c1) (conj d1) (conj c2) (conj d2) := by
  simp [sec, map_div₀, map_sub, map_mul]

lemma conj_ctr (A a B b C c : ℂ) :
    conj (ctr A a B b C c) = ctr (conj A) (conj a) (conj B) (conj b) (conj C) (conj c) := by
  simp [ctr, den3, map_div₀, map_sub, map_mul, map_add]

lemma conj_XN (c1 d1 c2 d2 c3 d3 c4 d4 : ℂ) :
    conj (XN c1 d1 c2 d2 c3 d3 c4 d4) =
      XN (conj c1) (conj d1) (conj c2) (conj d2) (conj c3) (conj d3) (conj c4) (conj d4) := by
  simp [XN, map_sub, map_mul, map_add, map_pow, map_neg]

lemma conj_NN (c1 d1 c2 d2 c3 d3 c4 d4 : ℂ) :
    conj (NN c1 d1 c2 d2 c3 d3 c4 d4) =
      NN (conj c1) (conj d1) (conj c2) (conj d2) (conj c3) (conj d3) (conj c4) (conj d4) := by
  simp [NN, map_sub, map_mul, map_add, map_pow]

lemma secondInter_symm (c₁ c₂ : ℂ) : secondInter c₁ c₂ = secondInter c₂ c₁ := by
  unfold secondInter sec
  rw [← neg_sub (conj c₁), div_neg, ← neg_div]
  congr 1; ring

/-- The second intersection point lies on the first circle. -/
theorem secondInter_mem_left (c₁ c₂ : ℂ) : secondInter c₁ c₂ ∈ circ c₁ := by
  rw [EuclideanGeometry.mem_sphere]
  change dist (secondInter c₁ c₂) c₁ = ‖c₁‖
  have h0 : ‖c₁‖ = dist 0 c₁ := by simp [Complex.dist_eq]
  rw [h0, dist_eq_dist_iff]
  by_cases h : conj c₁ - conj c₂ = 0
  · simp [secondInter, sec, h]
  · rw [secondInter]
    simp only [map_sub, conj_sec, Complex.conj_conj, zero_sub, map_neg]
    have h' : c₁ - c₂ ≠ 0 := by
      intro h''; apply h; rw [← map_sub, h'', map_zero]
    unfold sec
    field_simp
    ring

/-- The second intersection point lies on the second circle. -/
theorem secondInter_mem_right (c₁ c₂ : ℂ) : secondInter c₁ c₂ ∈ circ c₂ := by
  rw [secondInter_symm]; exact secondInter_mem_left c₂ c₁

/-- Non-collinear points have nonzero circumcentre denominator. -/
lemma den3_ne_zero {A B C : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    den3 A (conj A) B (conj B) C (conj C) ≠ 0 := by
  intro h0
  apply h
  by_cases hAB : A = B
  · subst hAB
    rw [Set.insert_eq_of_mem (Set.mem_insert _ _)]
    exact collinear_pair ℝ _ _
  · rw [collinear_iff_of_mem (p₀ := A) (by simp)]
    refine ⟨B - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    have hu : B - A ≠ 0 := sub_ne_zero.2 (Ne.symm hAB)
    have hu' : conj (B - A) ≠ 0 := (map_ne_zero _).2 hu
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨((p - A) * conj (B - A)).re / Complex.normSq (B - A), ?_⟩
      have hc : conj ((p - A) * conj (B - A)) = (p - A) * conj (B - A) := by
        simp only [map_mul, map_sub, Complex.conj_conj]
        unfold den3 at h0
        linear_combination -h0
      have hreal : (((p - A) * conj (B - A)).re : ℂ) = (p - A) * conj (B - A) :=
        Complex.conj_eq_iff_re.1 hc
      rw [vadd_eq_add, Complex.real_smul, Complex.ofReal_div, hreal, ← Complex.mul_conj]
      field_simp
      ring

/-- `Z` lies on the circumcircle of `A, B, C` provided they are not collinear and `T = 0`. -/
lemma mem_circumcircle_of_TT {A B C Z : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (hT : TT A (conj A) B (conj B) C (conj C) Z (conj Z) = 0) : Z ∈ circumcircle A B C := by
  rw [EuclideanGeometry.mem_sphere]
  change dist Z (ccenter A B C) = dist A (ccenter A B C)
  rw [dist_eq_dist_iff, map_sub, map_sub, ccenter, conj_ctr]
  simp only [Complex.conj_conj]
  exact circ_aux _ _ _ _ _ _ _ _ (den3_ne_zero h) hT

theorem mem_circumcircle_left (A B C : ℂ) : A ∈ circumcircle A B C := by
  rw [EuclideanGeometry.mem_sphere]; rfl

theorem mem_circumcircle_middle {A B C : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    B ∈ circumcircle A B C :=
  mem_circumcircle_of_TT h (by unfold TT; ring)

theorem mem_circumcircle_right {A B C : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    C ∈ circumcircle A B C :=
  mem_circumcircle_of_TT h (by unfold TT; ring)

/-- The common point of Clifford's theorem (explicit). -/
noncomputable def cliffordPoint (c₁ c₂ c₃ c₄ : ℂ) : ℂ :=
  XN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) /
    NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄)

/-- Consequences of `secondInter cᵢ cⱼ ≠ 0`. -/
lemma secondInter_ne_zero_iff' {c₁ c₂ : ℂ} (h : secondInter c₁ c₂ ≠ 0) :
    conj c₁ - conj c₂ ≠ 0 ∧ c₁ - c₂ ≠ 0 ∧ ee c₁ (conj c₁) c₂ (conj c₂) ≠ 0 := by
  unfold secondInter sec at h
  obtain ⟨hn, hd⟩ := div_ne_zero_iff.1 h
  refine ⟨hd, ?_, ?_⟩
  · intro h'; apply hd; rw [← map_sub, h', map_zero]
  · intro h'; apply hn; unfold ee at h'; linear_combination -h'

/-- The main computation, for the triple `{1, 2, 3}`. -/
lemma cliffordPoint_mem_gam (c₁ c₂ c₃ c₄ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0)
    (hnc : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ)) :
    cliffordPoint c₁ c₂ c₃ c₄ ∈ gam c₁ c₂ c₃ := by
  obtain ⟨d12, g12, e12⟩ := secondInter_ne_zero_iff' h12
  obtain ⟨d13, g13, e13⟩ := secondInter_ne_zero_iff' h13
  obtain ⟨d14, -, e14⟩ := secondInter_ne_zero_iff' h14
  obtain ⟨d23, g23, e23⟩ := secondInter_ne_zero_iff' h23
  obtain ⟨d24, -, -⟩ := secondInter_ne_zero_iff' h24
  obtain ⟨d34, -, -⟩ := secondInter_ne_zero_iff' h34
  have hden := den3_ne_zero hnc
  unfold secondInter at hden
  simp only [conj_sec, Complex.conj_conj] at hden
  rw [den3_sec _ _ _ _ _ _ d12 d13 d23 g12 g13 g23] at hden
  have hL : LL c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) ≠ 0 := by
    intro h0; apply hden; rw [h0]; ring
  have hD : DD c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) ≠ 0 := by
    intro h0; apply hden; rw [h0]; ring
  have hc4 : conj c₄ ≠ 0 := by
    intro h0; apply e14; unfold ee; rw [h0, (map_eq_zero _).1 h0]; ring
  have hN : NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) ≠ 0 := by
    intro h0
    have h0' : NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ = 0 := by
      have := congrArg conj h0
      rw [conj_NN, map_zero] at this
      simpa only [Complex.conj_conj] using this
    have hR := resultant_NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄)
    rw [h0, h0', mul_zero, mul_zero, sub_zero] at hR
    have d14' : conj c₁ - conj c₄ ≠ 0 := d14
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hc4 d14) d24) d34) e12) e13) e23) hL) hD) hR.symm
  have hN' : NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ ≠ 0 := by
    intro h0; apply hN
    have := congrArg conj h0
    rw [conj_NN, map_zero] at this
    simpa only [Complex.conj_conj] using this
  apply mem_circumcircle_of_TT hnc
  unfold secondInter cliffordPoint
  rw [map_div₀, conj_XN, conj_NN]
  simp only [conj_sec, Complex.conj_conj]
  exact TT_X _ _ _ _ _ _ _ _ d12 d13 d23 g12 g13 g23 hN hN'

lemma cliffordPoint_perm₁ (c₁ c₂ c₃ c₄ : ℂ) : cliffordPoint c₁ c₂ c₄ c₃ = cliffordPoint c₁ c₂ c₃ c₄ := by
  unfold cliffordPoint; rw [XN_perm₁, NN_perm₁, neg_div_neg_eq]

lemma cliffordPoint_perm₂ (c₁ c₂ c₃ c₄ : ℂ) : cliffordPoint c₁ c₃ c₄ c₂ = cliffordPoint c₁ c₂ c₃ c₄ := by
  unfold cliffordPoint; rw [XN_perm₂, NN_perm₂]

lemma cliffordPoint_perm₃ (c₁ c₂ c₃ c₄ : ℂ) : cliffordPoint c₂ c₃ c₄ c₁ = cliffordPoint c₁ c₂ c₃ c₄ := by
  unfold cliffordPoint; rw [XN_perm₃, NN_perm₃, neg_div_neg_eq]

/-- **Clifford's first circle theorem (n = 4).**
Four circles through the origin `M` with centres `c₁, c₂, c₃, c₄`; any two of them meet again at a point
`secondInter cᵢ cⱼ ≠ M` (general position: no two circles are tangent at `M` or coincide), and for each
triple the three second intersection points are not collinear (so that `Γ_ijk` is a genuine circle through
them, see `mem_circumcircle_left/middle/right`).  Then the four circles `Γ_123, Γ_124, Γ_134, Γ_234`
pass through a common point. -/
theorem clifford_one (c₁ c₂ c₃ c₄ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ)) :
    ∃ P : ℂ, P ∈ gam c₁ c₂ c₃ ∧ P ∈ gam c₁ c₂ c₄ ∧ P ∈ gam c₁ c₃ c₄ ∧ P ∈ gam c₂ c₃ c₄ := by
  refine ⟨cliffordPoint c₁ c₂ c₃ c₄, ?_, ?_, ?_, ?_⟩
  · exact cliffordPoint_mem_gam c₁ c₂ c₃ c₄ h12 h13 h14 h23 h24 h34 n123
  · rw [← cliffordPoint_perm₁]
    exact cliffordPoint_mem_gam c₁ c₂ c₄ c₃ h12 h14 h13 h24 h23
      (by rwa [secondInter_symm]) n124
  · rw [← cliffordPoint_perm₂]
    exact cliffordPoint_mem_gam c₁ c₃ c₄ c₂ h13 h14 h12 h34 (by rwa [secondInter_symm])
      (by rwa [secondInter_symm]) n134
  · rw [← cliffordPoint_perm₃]
    exact cliffordPoint_mem_gam c₂ c₃ c₄ c₁ h23 h24 (by rwa [secondInter_symm]) h34
      (by rwa [secondInter_symm]) (by rwa [secondInter_symm]) n234

end Clifford
