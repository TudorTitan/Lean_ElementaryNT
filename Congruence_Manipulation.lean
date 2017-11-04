-- gcd and div and mod and lt and le are all in core
-- but most of the theorems about them are here

import data.int.basic
import data.int.order
import data.nat.gcd

-- a congruent to b modulo m
def cong (a:int) (b: int) (m: int): Prop := m ∣ a - b

-- p is prime
def is_prime (p:nat): Prop := ∀ x y: int, ↑p ∣ (x*y) → ↑p ∣ x ∨ ↑p ∣ y

-- Solution to linear diophantine equation with constants a b k
def LDE (a:int) (b:int) (k:int): Prop := ∃ x y: int, a*x + b*y = k

theorem WOP {k: nat} (p:nat → Prop) (H: p k): ∃ n: nat, p n ∧ (∀ y:nat, p y → y ≥ n) :=
begin
    revert H,
    apply @nat.strong_induction_on (λ h, p h → (∃ (n : ℕ), p n ∧ ∀ (y : ℕ), p y → y ≥ n)) k,
    intros x Hx Hpx,
    induction x,
    apply exists.intro 0,
    split, exact Hpx,
    intros, exact nat.zero_le y,
    cases classical.em (∃ y, y < nat.succ a ∧ p y),
    cases a_1,
    apply Hx, apply a_2.1, apply a_2.2,
    apply exists.intro (nat.succ a),
    split, assumption,
    intros,
    by_contradiction,
    apply a_1,
    apply exists.intro y,
    exact ⟨lt_of_not_ge a_3,a_2⟩
end

--

lemma SwapSums (a b x : int) : (a-b) + (-x + x) = (a-x) - (b-x) :=
begin
    simp, rw [add_comm x], simp
end

lemma NegCommViaMul (a:int) (b:int) : (-1)*(a - b) = b - a := by simp

lemma simplifyTransum (a: int) (b: int) (c: int) : (a-b) + (b-c) = a - c := by simp [add_assoc]

theorem Mreflex (a:int) (m: int): cong a a m :=
begin
    unfold cong,
    apply exists.intro (0:ℤ),
    simp
end

theorem Msymmetric {a b : int} {m: int} (H1: cong a b m): cong b a m :=
begin
    cases H1,
    apply exists.intro (-a_1),
    simp,
    rw ←a_2,
    simp
end

theorem Mtrans {a b c: int} (m: nat) (H1: cong a b m) (H2: cong b c m): cong a c m :=
begin
    cases H1,
    cases H2,
    apply exists.intro (a_1 + a_3),
    rw [mul_add,←a_2,←a_4],
    simp,
    rw [←add_assoc b],
    simp
end

theorem Mmul {x a b: int} (n:int) (H1: cong a b n) : cong (a*x) (b*x) n:=
begin
    cases H1,
    apply exists.intro (a_1*x),
    rw [←mul_assoc,←a_2,sub_mul]
end 

theorem Msub {a b: int} {n:nat} (x:int) (H1: cong a b n) : cong (a-x) (b-x) n:=
begin
    unfold cong at *,
    simp at *,
    rw [add_comm x,add_assoc],
    simp,
    exact H1
end 

theorem MinsertLeft {a b c: int} {n:int} (H1: cong a b n) (H2: a = c): cong c b n := begin
    rw H2 at H1,
    exact H1
end

theorem MinsertRight {a b c: int} {n:int} (H1: cong a b n) (H2: b = c): cong a c n:=
begin
    rw H2 at H1,
    exact H1
end

theorem Madd {a b: int} {n:nat} (x: int) (H1: cong a b n) : cong (a+x) (b+x) n:=
begin
    unfold cong at *,
    simp at *,
    rw [add_comm x,add_assoc],
    simp,
    exact H1
end

theorem Mcancel {p:nat} {a b x} (H1: is_prime p) (H2: cong (x*a) (x*b) p): (cong a b p) ∨ ↑p ∣ x  :=
begin
    unfold is_prime at H1,
    unfold cong at *,
    rw ←mul_sub at H2,
    simp at *,
    cases H2,
    cases (H1 x (a-b) _),
    left, exact a_3,
    right, exact a_3,
    exact ⟨a_1,a_2⟩
end 

theorem MDsum {a b c d n: int} (H1: cong a b n) (H2: cong c d n): cong (a+c) (b+d) n :=
begin
    unfold cong at *,
    simp [add_assoc],
    rw [add_comm c,add_assoc,add_comm (-d),←add_assoc],
    cases H1,
    cases H2,
    simp at a_2,
    simp at a_4,
    rw [a_2,a_4,←mul_add],
    apply exists.intro (a_1+a_3),
    refl
end

theorem basicInequality {a b : int} (H1: b ∣ a) (HA: a > 0) : a ≥ b :=
begin
    cases b,
    cases a_1,
    apply le_of_lt HA,
    cases H1,
    simp at *,
    rw nat.succ_eq_add_one,
    change a ≥ a_1+1,
    apply int.add_one_le_of_lt,
    cases a_2,
    cases a_2,
    change a = 0*(a_1+1) at a_3,
    simp at a_3,
    apply false.elim (ne_of_lt HA a_3.symm),
    rw a_3,
    change (a_1:ℤ) < ↑((nat.succ a_2) * (nat.succ a_1)),
    suffices : 1 * a_1 < (nat.succ a_2) * (nat.succ a_1),
        simp at *,
        apply int.coe_nat_lt_coe_nat_of_lt,
        exact this,
    apply mul_lt_mul',
        apply nat.le_add_left,
        apply nat.lt_succ_self,
        apply nat.zero_le,
        apply nat.zero_lt_succ,
    have HA1: a ≤ 0,
        apply int.le_of_lt,
        apply int.neg_of_sign_eq_neg_one,
        rw a_3,
        apply int.sign_mul,
    apply false.elim (((lt_iff_not_ge _ _).1 HA) HA1),
    apply le_of_lt,
    apply lt_of_lt_of_le,
    apply int.neg_of_sign_eq_neg_one,
    simp [int.sign],
    apply le_of_lt HA
end

-- Division algorithm
-- depedencies on data.int.basic and data.int.order
theorem DivAlgo (a : int) (b : int) (Hb : b>0): ∃ q r : int, a = b*q + r ∧ 0 ≤ r ∧ b > r :=
begin
    apply exists.intro (a/b),
    apply exists.intro (a%b),
    split,
    rw add_comm,
    rw int.mod_add_div,
    split,
    apply int.mod_nonneg a (int.ne_of_lt Hb).symm,
    apply int.mod_lt_of_pos, exact Hb
end

--Lemma for proving that Z is a principal ideal domain later on

lemma LDEsimp {a b p :int} (W1: (LDE a b p ∧ p > 0) ∧ (∀ (q: int), LDE a b q ∧ q > 0 → q ≥ p)) : p ∣ a :=
begin
    cases W1.1.1 with x W2,
    cases W2 with y W3,
    have App: ∃ m n: int, a = p*m + n ∧ 0 ≤ n ∧ p > n, from DivAlgo a p W1.1.2,
    cases App with m D1,
    cases D1 with n D,
    have D1 := D.1,
    rw ←W3 at D1,
    have A: a*(1-x*m) + b*(-(y*m)) = n,
        simp [mul_add],
        rw [←neg_add,←mul_assoc,←mul_assoc],
        apply add_neg_eq_of_eq_add,
        rw [←add_mul,add_comm],
        apply D1,
    have Z1: n = 0,
        cases lt_or_eq_of_le D.2.1,
            have C0: LDE a b n := ⟨1-x*m,⟨-(y*m),A⟩⟩,
            have C1: n ≥ p := W1.2 n ⟨C0,a_1⟩,
            apply false.elim ((not_lt_of_ge C1) D.2.2),
            simp [a_1],
    simp [W3,Z1] at D1,
    exact ⟨m,D1⟩
end

lemma LDEcomm {a b p: int} (H: LDE a b p) : LDE b a p :=
begin
    cases H,
    cases a_2,
    rw add_comm at a_3,
    apply exists.intro,
    apply exists.intro,
    exact a_3
end

lemma PisGCD {j b p: int} (W2: p > 0) (W11: LDE j b p) (y: int): y ∣ j ∧ y ∣ b → p ≥ y :=
begin
    intro P,
    have F: y ∣ p,
        cases P.1,
        cases P.2,
        simp [LDE] at *,
        cases W11,
        cases a_5,
        rw [a_1,a_3,mul_assoc,mul_assoc,←mul_add] at a_6,
        simp [has_dvd.dvd],
        exact ⟨_,a_6.symm⟩,
    exact basicInequality F W2
end

theorem mul_sign : ∀ (i : int), i * int.sign i = int.nat_abs i
| (n+1:ℕ) := by {simp [int.sign], rw ←int.abs_eq_nat_abs, refl}
| 0       := by {simp [int.sign], refl}
| -[1+ n] := by {simp [int.sign], refl}

theorem sign_mul : ∀ (i : int), int.sign i * i = int.nat_abs i
| (n+1:ℕ) := by {simp [int.sign], rw ←int.abs_eq_nat_abs, refl}
| 0       := by {simp [int.sign], refl}
| -[1+ n] := by {simp [int.sign], refl}

theorem nat_le_int {j b : ℤ} {n : ℕ} (hn : ∀ (y : ℕ), LDE j b y ∧ y > 0 → y ≥ n) {q : ℤ} (hq : LDE j b q ∧ q > 0) : q ≥ n :=
begin
    have hqq : q = ↑(int.nat_abs q),
    induction q,
    refl,
    exfalso,
    apply not_le_of_gt hq.2,
    apply le_of_lt,
    apply (int.sign_eq_neg_one_iff_neg _).1,
    simp [int.sign],
    have hqn : int.nat_abs q ≥ n,
    apply hn,
    exact ⟨hqq ▸ hq.1, (int.nat_abs_pos_of_ne_zero (int.ne_of_lt hq.2).symm)⟩,
    have hqn := int.coe_nat_le_coe_nat_of_le hqn,
    exact hqq.symm ▸ hqn,
end

theorem IntegersFormPID (j : int) (b : int): LDE j b (int.gcd j b) :=
let p := int.gcd j b in
begin
    cases classical.em (j=0),
    rw a,
    unfold LDE,
    simp [int.gcd],
    change ∃ (y : ℤ), b * y = ↑(nat.gcd 0 (int.nat_abs b)),
    rw nat.gcd_zero_left,
    apply exists.intro,
    exact mul_sign b,
    have H : ∃ n: nat, (LDE j b n ∧ n > 0) ∧ (∀ y:nat, (LDE j b y ∧ y > 0) → y ≥ n),
        apply @WOP (int.nat_abs j + int.nat_abs b) (λ h, LDE j b h ∧ h > 0),
        split,
        apply exists.intro (int.sign j),
        apply exists.intro (int.sign b),
        rw [mul_sign,mul_sign],
        refl,
        have H: int.nat_abs j > 0,
            apply nat.lt_of_le_and_ne,
            apply nat.zero_le,
            intro H, apply a, exact int.eq_zero_of_nat_abs_eq_zero H.symm,
        apply nat.add_pos_left H,
    cases H with n hn,
    have Hj : ↑n ∣ j,
        apply LDEsimp,
        split,
        split,
        exact hn.1.1,
        exact int.coe_nat_lt_coe_nat_of_lt hn.1.2,
        intros q hq,
        apply nat_le_int,
        intros y hy,
        exact hn.2 y hy,
        exact hq,
    have Hb : ↑n ∣ b,
        apply LDEsimp,
        split,
        split,
        exact LDEcomm hn.1.1,
        exact int.coe_nat_lt_coe_nat_of_lt hn.1.2,
        intros q hq,
        apply nat_le_int,
        intros y hy,
        exact hn.2 y hy,
        rw (iff.intro LDEcomm LDEcomm),
        exact hq,
    have Hp : nat.gcd (int.nat_abs j) (int.nat_abs b) = p, refl,
    cases (nat.gcd_dvd_left (int.nat_abs j) (int.nat_abs b)),
    rw Hp at a_2,
    have a_2 : int.sign j * int.nat_abs j = int.sign j * p * a_1 := by {rw [a_2,mul_assoc], refl},
    rw int.sign_mul_nat_abs at a_2,
    have Hpn : n ∣ p,
        unfold has_dvd.dvd at *,
        cases Hj,
        cases Hb,
        apply nat.dvd_gcd,
        have a_4 : int.nat_abs j = n * int.nat_abs a_3,
        rw [a_4,int.nat_abs_mul], refl,
        exact exists.intro _ a_4,
        have a_6 : int.nat_abs b = n * int.nat_abs a_5,
        rw [a_6,int.nat_abs_mul], refl,
        exact exists.intro _ a_6,
    have Hnp : p ∣ n,
        have hj : p ∣ int.nat_abs j := nat.gcd_dvd_left (int.nat_abs j) (int.nat_abs b),
        have hb : p ∣ int.nat_abs b := nat.gcd_dvd_right (int.nat_abs j) (int.nat_abs b),
        have h := hn.1.1,
        unfold LDE at h,
        cases hj,
        cases hb,
        have a_4 : j = p * (a_3 * int.sign j),
            suffices : int.sign j * int.nat_abs j = p * (a_3 * int.sign j),
            rw [int.sign_mul_nat_abs] at this, exact this,
            rw a_4,
            simp, refl,
        have a_6 : b = p * (a_5 * int.sign b),
            suffices : int.sign b * int.nat_abs b = p * (a_5 * int.sign b),
            rw [int.sign_mul_nat_abs] at this, exact this,
            rw a_6,
            simp, refl,
        cases hn.1.1,
        cases a_8,
        rw [a_4,a_6,mul_assoc,mul_assoc,mul_assoc,mul_assoc,←mul_add] at a_9,
        have a_9 := congr_arg int.nat_abs a_9,
        rw [int.nat_abs_mul] at a_9,
        change p * _ = n at a_9,
        apply exists.intro,
        apply a_9_1.symm,
    have H : n = p := nat.dvd_antisymm Hpn Hnp,
    rw H at hn,
    exact hn.1.1
end
