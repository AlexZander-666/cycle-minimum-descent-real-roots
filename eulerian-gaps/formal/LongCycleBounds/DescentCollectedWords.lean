import LongCycleBounds.DescentSignedLogCoefficients
import LongCycleBounds.DescentResidualWindow

noncomputable section
namespace LongCycleBounds.DescentMesh.Collected
open Finset Polynomial Real FixedCycleCount DescentNecklace

abbrev degrees (k i : ℕ) := i.divisors.filter (fun h ↦ h<k ∧ h < i)
abbrev Atom (k H : ℕ) := (i : ↥(Icc 1 H)) × ↥(degrees k i.val)
abbrev Word (k H : ℕ) := (t : Fin H) × (Fin (t.val+1) → Atom k H)
def length {k H} (a : Atom k H) := a.1.val
def degree {k H} (a : Atom k H) := a.2.val
def scalar {k H} (a : Atom k H) : ℝ := (SignedBounds.signedSum k (degree a) (length a/degree a):ℝ)/length a
def loss {k H} (a : Atom k H) := length a-degree a
def WL {k H} (w : Word k H) := ∑ i,length (w.2 i)
def WD {k H} (w : Word k H) := ∑ i,degree (w.2 i)
def WS {k H} (w : Word k H) := ∑ i,loss (w.2 i)
def WC {k H} (w : Word k H) := (∏ i,scalar (w.2 i))/((w.1.val+1).factorial:ℝ)

private theorem degrees_lt {k H} (a : Atom k H) : degree a < length a := (mem_filter.mp a.2.prop).2.2

theorem degrees_twice {k H} (a : Atom k H) : 2*degree a ≤ length a := by
  have dm := (mem_filter.mp a.2.prop).1
  have hd := Nat.dvd_of_mem_divisors dm
  have lt := degrees_lt a
  change degree a ∣ length a at hd
  obtain ⟨q,hq⟩ := hd
  have lq : 2 ≤ q := by
    by_contra! hn
    have := Nat.mul_le_mul_left (degree a) (show q≤1 by omega)
    omega
  simpa only [hq,Nat.mul_comm 2] using Nat.mul_le_mul_left (degree a) lq

theorem wl_eq {k H} (w : Word k H) : WD w + WS w = WL w := by
  simp only [WD,WS,WL,←sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ Nat.add_sub_of_le (degrees_lt (w.2 i)).le

theorem word_half {k H} (w : Word k H) : WL w ≤ 2*WS w := by
  have eq := wl_eq w
  have le : 2*WD w ≤ WL w := by
    unfold WD WL
    rw [mul_sum]
    exact sum_le_sum fun i _ ↦ degrees_twice _
  omega

def logPoly (k H : ℕ) : BiPoly := ∑ a : Atom k H,biTerm (length a) (degree a) (scalar a)
def Taylor (k H : ℕ) : BiPoly := 1+∑ t∈range H,biTerm 0 0 (((t+1).factorial:ℝ)⁻¹)*(logPoly k H)^(t+1)

private theorem group_poly (k H : ℕ) : logPoly k H =
    ∑ i∈Icc 1 H,monomial i (∑ h∈degrees k i,monomial h ((SignedBounds.signedSum k h (i/h):ℝ)/i)) := by
  simp only [logPoly,Fintype.sum_sigma,biTerm,length,degree,scalar,map_sum]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply sum_congr rfl
  intro i _
  conv_rhs => rw [←Finset.sum_coe_sort]

theorem log_coeff (k H i h : ℕ) (hi : 0 < i) (cut : i ≤ H) :
    ((logPoly k H).coeff i).coeff h =
      if h∈i.divisors ∧ h<k ∧ h < i then (SignedBounds.signedSum k h (i/h):ℝ)/i else 0 := by
  rw [group_poly]
  have e : i∈Icc 1 H := mem_Icc.mpr ⟨hi,cut⟩
  simp [finsetSum_coeff,coeff_monomial,e,degrees,hi.ne']

theorem congr_log {k H : ℕ} (hk : 3 ≤ k) :
    X^(H+1) ∣ badLogPolynomial k H H-logPoly k H := by
  apply X_pow_dvd_iff.mpr
  intro i hi
  rw [coeff_sub,sub_eq_zero]
  apply Polynomial.ext
  intro h
  by_cases zero : i=0
  · subst i
    have z := X_dvd_iff.mp (X_dvd_badLogPolynomial hk H H)
    rw [z,group_poly,finsetSum_coeff]
    simp [coeff_monomial]
  · rw [signed_log_coefficient hk (by omega) (by omega),log_coeff k H i h (by omega) (by omega)]

theorem congr_taylor {k H : ℕ} (hk : 3 ≤ k) :
    X^(H+1) ∣ badTaylor k H H H-Taylor k H := by
  simp only [badTaylor,Taylor,add_sub_add_left_eq_sub,←sum_sub_distrib,←mul_sub]
  apply dvd_sum
  intro t _
  exact dvd_mul_of_dvd_right ((congr_log hk).trans (sub_dvd_pow_sub_pow _ _ _)) _

theorem original_row {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) :
    (profilePolynomial n k).map (Rat.castHom ℝ) = (goodPolynomial n k*Taylor k n).coeff n := by
  rw [profile_eq_expansion hk hn]
  have h := dvd_mul_of_dvd_right (congr_taylor (H:=n) hk) (goodPolynomial n k)
  have hz := X_pow_dvd_iff.mp h n (show n<n+1 by omega)
  simpa only [mul_sub,coeff_sub,sub_eq_zero,expansionRow] using hz

theorem taylor_words (k H : ℕ) : Taylor k H =
    1+∑ w : Word k H, biTerm (WL w) (WD w) (WC w) := by
  unfold Taylor
  congr 1
  rw [Fintype.sum_sigma,←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  have eq : (logPoly k H)^(i.val+1) = ∑ w : Fin (i.val+1)→Atom k H,
      ∏ a,biTerm (length (w a)) (degree (w a)) (scalar (w a)) := by
    rw [←Fintype.prod_sum (fun (_ : Fin (i.val+1)) (z : Atom k H) ↦ biTerm (length z) (degree z) (scalar z))]
    simp [logPoly]
  rw [eq,mul_sum]
  apply sum_congr rfl
  intro w _
  rw [biTerm_product,biTerm_mul,zero_add,zero_add]
  simp only [WL,WD,WC,div_eq_inv_mul]

#print axioms original_row
#print axioms taylor_words
end LongCycleBounds.DescentMesh.Collected
