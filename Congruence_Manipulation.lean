
-- a congruent to b modulo m
def cong (a:int) (b: int) (m: int): Prop := ∃ x: int, a-b = m*x

-- p is prime
def is_prime (p:nat): Prop := ∀ x y: int, cong (x*y) 0 p → cong x 0 p ∨ cong y 0 p

-- f is the floor of a/b
def floor (a:int) (b:int) (f:int): Prop  := (f*b ≤ a ∧ ∀  y: int, y*b ≤ a → y≤f)

-- g is the gcd of a and b
def gcd (a:int) (b:int) (g:int): Prop := g > 0 ∧ cong a 0 g ∧ cong b 0 g ∧ 
    (∀ y:nat, cong a 0 y ∧ cong b 0 y → g ≥ y) 

-- Solution to linear diophantine equation with constants a b k
def LDE (a:int) (b:int) (k:int): Prop := ∃ x y: int, a*x + b*y = k



-- existence of floor, gcd, and a solution to LDEs.
axiom Efloor (a: int) (b:int): ∃ x:int, floor a b x

axiom Egcd (a:int) (b: int): ∃ x: nat, gcd a b x

axiom ELDE (a:int) (b: int): ∃ k: int, LDE a b k ∧ k > 0 ∧ (∀ y: int, LDE a b y → y ≥ k)  

-- All of the above can be proven from Wop, but are temporarily axiomatised

axiom WOP {k: nat} (p:nat → Prop) (H: p k): ∃ n: nat, p n ∧ (∀ y:nat, p y → y ≥ n)

--

lemma SwapSums (a b x : int) : (a-b) + (-x + x) = (a-x) - (b-x) :=
begin
have goal: (a-b) + (-x + x) = (a-x) - (b-x), from calc
(a-b) + (-x + x) = (a-b) + (-x + x) : eq.refl ((a-b) + (-x + x))
... = (a-b) + (x-x) : by rw [neg_add_eq_sub]
... = (a-b) + x - x : by rw [add_sub_assoc]
... = (a-b) - x + x : by rw [sub_add_eq_add_sub (a-b) x x]
... = a-(x+b) + x: by rw [sub_add_eq_sub_sub_swap]
... = a- x -b + x: by rw [sub_add_eq_sub_sub]
... = a- x + -b + x: by rw [sub_eq_add_neg]
... = a- x + (-b + x): by rw [add_assoc]
... = (a-x) + (x - b): by rw [neg_add_eq_sub]
... = (a-x) + -(b - x) : by rw [eq.symm (neg_sub b x)]
... = (a-x) -(b - x) : by rw [eq.symm (sub_eq_add_neg (a-x) (b-x))],
exact goal
end

lemma NegCommViaMul (a:int) (b:int) : (-1)*(a - b) = b - a :=
begin
calc
(-1)*(a - b) = (-1)*(a - b) : eq.refl (-1*(a - b))
... = -(a - b)  : eq.symm (neg_eq_neg_one_mul ((a - b)))
... = -(-b + a): by rw [eq.symm (neg_add_eq_sub b a)]
... = -(-b) + -a : neg_add (-b) a
... = b + -a : by rw [neg_neg b]
... = b - a : eq.symm (sub_eq_add_neg b a)
end

lemma simplifyTransum (a: int) (b: int) (c: int) : (a-b) + (b-c) = a - c :=
begin
have H: a - c = (a-b) + (b-c), from calc
 a-c = b-c + (a-b) : sub_eq_sub_add_sub a c b
 ... = (a-b) + (b-c) : add_comm (b-c) (a-b),
have H2: (a-b) + (b-c) = a - c, from eq.symm H,
exact H2
end

theorem Mreflex (a:int) (m: nat): cong a a m :=
begin
have H1: a-a = 0, from trans_rel_left eq (sub_eq_add_neg a a) (add_right_neg a),
have H2: a-a = m*0, from trans_rel_left eq (H1) (eq.symm (mul_zero m)),
exact exists.intro 0 H2
end

theorem Msymmetric {a b : int} {m: int} (H1: cong a b m): cong b a m :=
begin
have H: (cong b a m), from exists.elim H1 (fun (k:int) (Hw1 : a-b = m*k),
have introMinusOne: -1*(a - b) = -1*(m*k), from by rw [Hw1],
have simplifiedLeft: b - a = -1*(m*k), from trans_rel_left eq (eq.symm (NegCommViaMul a b)) introMinusOne,
have rearrange : b - a = m*((-1)*k), from calc
b - a = -1*(m*k) : simplifiedLeft
... = m*((-1)*k): mul_left_comm (-1) m k,
have goal: cong b a m, from exists.intro ((-1)*k) rearrange,
goal),
exact H
end

theorem Mtrans {a b c: int} (m: nat) (H1: cong a b m) (H2: cong b c m): cong a c m :=
begin
have p: cong a c m, from exists.elim H1 (fun (k:int) (Hw1 : a-b = m*k), 
exists.elim H2 (fun (j:int) (Hw2 : b-c = m*j),
have Ha: (a-b) + (b-c) = m*k + m*j, from by rw [Hw1,Hw2],
have Hb: a-c = m*k + m*j, from trans_rel_left eq (eq.symm (simplifyTransum a b c)) Ha,
have goal: cong a c m, from exists.intro (k+j) (calc
a-c = m*k + m*j : Hb 
... = m*(k+j) : eq.symm (mul_add m k j)),
goal )),
exact p 
end

theorem Mmul {x a b: int} (n:int) (H1: cong a b n) : cong (a*x) (b*x) n:=
begin
have p: cong (a*x) (b*x) n, from exists.elim H1 (fun (k:int) (Hw1: a-b = n*k) ,
have H2: (a-b)*x = n*k*x, from by rw [Hw1],
have H3: a*x-b*x = n*k*x, from trans_rel_left eq (eq.symm (sub_mul a b x)) H2,
have H4:a*x-b*x = n*(k*x), from calc
a*x-b*x = n*k*x : H3
... = n*(k*x) : mul_assoc n k x,
have goal: cong (a*x) (b*x) n, from exists.intro (k*x) H4,
goal),
exact p
end 

theorem Msub {a b: int} {n:nat} (x:int) (H1: cong a b n) : cong (a-x) (b-x) n:=
begin
have p: cong (a-x) (b-x) n, from exists.elim H1 (fun (k:int) (Hw1: a-b = n*k) ,
have H2: (a-b) + (-x + x) = n*k + 0, from by rw [Hw1, add_left_neg x],
have H3:(a-b) + (-x + x)=  n*k, from calc 
(a-b) + (-x + x) = n*k + 0: H2
... = n*k : (add_zero (n*k)),
have goal: (a-x) - (b-x) = n*k, from trans_rel_left eq (eq.symm (SwapSums a b x)) H3,
have q: cong (a-x) (b-x) n, from exists.intro k goal,
q),
exact p
end 

theorem MinsertLeft {a b c: int} {n:int} (H1: cong a b n) (H2: a = c): cong c b n:=
begin
have goal: cong c b n, from exists.elim H1 (fun (k:int) (Hw1: a-b = n*k) ,
have Z1: c-a = 0, from sub_eq_zero_of_eq (eq.symm H2),
have L1: (a-b) + (c-a) = n*k + 0, from by rw [Hw1,Z1],
have L2: (a-b) + (c-a) = n*k, from by rw [L1,add_zero],
have L3: c - b = n*k, from trans_rel_left eq (sub_eq_sub_add_sub c b a) L2,
have p: cong c b n, from exists.intro k L3,
p),
exact goal
end

theorem MinsertRight {a b c: int} {n:int} (H1: cong a b n) (H2: b = c): cong a c n:=
begin
have goal: cong b a n, from Msymmetric H1,
have p: cong c a n, from MinsertLeft goal H2,
have q: cong a c n, from Msymmetric p,
exact q
end

theorem Madd {a b: int} {n:nat} (x: int) (H1: cong a b n) : cong (a+x) (b+x) n:=
begin
have start: cong (a - (-x)) (b - (-x)) n, from Msub (-x) (H1),
have L: cong (a+x) (b - (-x)) n, from MinsertLeft start (sub_neg_eq_add a x),
have R: cong (a + x) (b + x) n, from MinsertRight L (sub_neg_eq_add b x),
exact R
end

theorem Mcancel {p:nat} {a b x} (H1: is_prime p) (H2: cong (x*a) (x*b) p): (cong a b p) ∨ (cong x 0 p)  :=
begin
have L1: cong (x*a - x*b) (x*b - x*b) p, from Msub (x*b) H2,
have L2: cong (x*a - x*b) 0 p, from MinsertRight L1 (add_neg_self (x*b)),
have L3: cong (x*(a-b)) 0 p, from MinsertLeft L2 (eq.symm(mul_sub x a b)),
have goal: cong x 0 p ∨ cong (a-b) 0 p, from (H1 x (a-b)) L3,
have goal2: (cong a b p) ∨ (cong x 0 p), from or.cases_on goal
(assume ass: cong x 0 p,
have g2: (cong a b p) ∨ (cong x 0 p), from or.intro_right (cong a b p) ass,
g2) 
(assume ass: cong (a-b) 0 p,
have J1: cong (a-b + b) (0+b) p, from Madd b ass,
have J2: cong (a-b +b) b p, from MinsertRight J1 (zero_add b),
have J3: cong a b p, from MinsertLeft J2 (sub_add_cancel a b),
have J4: (cong a b p) ∨ (cong x 0 p), from or.intro_left (cong x 0 p) J3,
J4),
exact goal2
end 

theorem MDsum {a b c d n: int} (H1: cong a b n) (H2: cong c d n): cong (a+c) (b+d) n :=
begin
have  H: cong (a+c) (b+d) n, from sorry,
exact H
end

theorem basicInequality {a b : int} (H1: cong a 0 b) (h2: a > 0): a ≥ b :=
begin
have H: a ≥ b , from sorry,
exact H
end

-- Division algorithm

theorem DivAlgo (a : int) (b : int): ∃ q r : int, a = b*q + r ∧ 0 ≤ r ∧ b > r :=
begin 
have Q: ∃ q r: int, a = b*q + r ∧ 0 ≤ r ∧ b > r, 
    from exists.elim (Efloor a b) (fun (x:int) (H: x*b ≤ a ∧ ∀  y: int, y*b ≤ a → y≤x),
have Hl: x*b ≤ a, from and.elim_left H, 
have Hr: ∀  y: int, y*b ≤ a → y≤x, from and.elim_right H,
have L1: 0 = b*x - b*x, from eq.symm (sub_eq_zero_of_eq (eq.refl (b*x))), 
have G1: a = b*x + (a-x*b), from calc 
     a = 0 + a: eq.symm (zero_add a)
    ... = b*x - b*x + a: by rw [L1] 
    ... = b*x - x*b + a: by rw [mul_comm]
    ... = b*x + a - x*b: sub_add_eq_add_sub (b*x) (x*b) a
    ... = b*x + (a - x*b): add_sub_assoc (b*x) a (x*b),
have G2: 0 ≤ (a - x*b), from sub_nonneg_of_le Hl,
have Trich: b ≤ (a - x*b) ∨ b > (a - x*b), from le_or_gt b (a - x*b),
have G3: b > (a - x*b), from or.cases_on Trich
(assume ass: b ≤ (a - x*b),
have  L2: a ≥ b + x*b, from add_le_of_le_sub_right ass,
have L3:  b + (x*b) = 1*b + (x*b), from by rw [one_mul],
have L4: (x+1)*b = (1+x)*b, from by rw [add_comm],
have C: (x+1)*b ≤ a, from calc
 a ≥ b + (x*b) : L2
 ... ≥ 1*b + (x*b): le_of_eq (eq.symm L3)
 ... ≥ (1+x)*b : le_of_eq (add_mul 1 x b)
 ... ≥ (x+1)*b : le_of_eq L4,
 have F: x+1 ≤ x, from Hr (x+1) C,
 have T: x+1 > x, from int.lt_add_one_of_le (le_of_eq (eq.refl x)),
 have will: b > (a - x*b), from absurd F (not_le_of_gt T),
 will)
 (assume ass: b > (a - x*b),
 ass),
    have final: ∃ q r: int, a = b*q + r ∧ 0 ≤ r ∧ b > r, 
        from exists.intro x (exists.intro (a - x*b) (and.intro G1 (and.intro G2 G3))),
    final),
    exact Q
end

--Lemma for proving that Z is a principal ideal domain later on

lemma LDEsimp {a b p :int} (W1: LDE a b p ∧ p > 0 ∧ (∀ (q: int), LDE a b q → q ≥ p)) : cong a 0 p:=
begin
exact exists.elim W1.1
        (fun (x : int) (W2: ∃ y:int, a*x + b*y  = p),
            exists.elim W2
            (fun (y : int) (W3: a*x + b*y = p),
                have App: ∃ m n: int, a = p*m + n ∧ 0 ≤ n ∧ p > n, from DivAlgo a p,
                exists.elim (App)
                (fun (m : int) (D1: ∃ n: int, a = p*m + n ∧ 0 ≤ n ∧ p > n),
                    exists.elim D1
                    (fun (n : int) (D: a = p*m + n ∧ (0 ≤ n ∧ p > n)),
                    
                        have Ntest: 0 ≤ n, from and.elim_left (and.elim_right D),
                        have UB: p > n, from and.elim_right (and.elim_right D),

                        have A1: a = p*m + n, from and.elim_left D,
                        have A2: a = (a*x + b*y)*m + n, from eq.subst (eq.symm W3) A1,
                        have A3: n = a - (a*x + b*y)*m, from eq_sub_of_add_eq' (eq.symm A2),
                        have A: a*(1-x*m) + b*(-(y*m))  = n, from eq.symm (calc
                            n = a - (a*x + b*y)*m : A3
                            ... = a - (a*x*m + b*y*m) : by rw [add_mul (a*x) (b*y) m]
                            ... = a - a*x*m - b*y*m : sub_add_eq_sub_sub a (a*x*m) (b*y*m)
                            ... = a*1 - a*x*m - b*y*m : by rw [mul_one]
                            ... = a*1 - a*(x*m) - b*y*m : by rw [mul_assoc]
                            ... = a*(1 - x*m) - (b*y*m) : by rw [eq.symm (mul_sub a 1 (x*m))]
                            ... = a*(1-x*m) + -(b*y*m) : by rw [sub_eq_add_neg] 
                            ... = a*(1-x*m) + -(b*(y*m)) : by rw [mul_assoc] 
                            ... = a*(1-x*m) + b*(-(y*m)) : by rw [neg_mul_eq_mul_neg]
                        ),
                        have Z1: n = 0, from or.by_cases (lt_or_eq_of_le Ntest)
                        (assume H1: n > 0,
                        have C0: LDE a b n, from exists.intro (1-x*m) (exists.intro (-(y*m)) A),
                        have C1: ∀ q: int, LDE a b q → q ≥ p, from  W1.2.2,
                        have C2: n ≥ p, from C1 n C0,
                        have C4: ¬ n < p, from not_lt_of_ge C2,
                        have E: n = 0, from absurd UB C4,
                        E)
                        (assume H: 0 = n,
                        eq.symm H),
                        have P1: a = (p*m) + 0, from eq.subst Z1 A1,
                        have P2: a = (p*m), from calc a = (p*m) + 0 : P1 ... = (p*m) : by rw [add_zero],
                        have P3: a - 0 = p*m, from eq.trans (sub_zero a) P2,
                        have P4: cong a 0 p, from exists.intro m P3,
                        P4
                    )
                )
            )
        )
end

lemma LDEcomm {a b p: int} (H: LDE a b p) : LDE b a p :=
begin
have H1: ∃ x y: int, a*x + b*y = p, from H,
have H2: LDE b a p, from exists.elim (H1) (
    (fun (x : int) (W1: ∃ y: int, a*x + b*y = p),
    exists.elim (W1) (
    (fun (y : int) (W1: a*x + b*y = p),
    have W3: b*y + a*x = p, from eq.symm (calc
    p = a*x + b*y : eq.symm W1
    ... = b*y + a*x : add_comm (a*x) (b*y)
    ),
    exists.intro y (exists.intro x W3)
    )
))),
exact H2
end

lemma PisGCD {j b p: int} (W2: p > 0) (W11: LDE j b p) (y: int): cong j 0 y ∧ cong b 0 y → p ≥ y :=
begin
have goal: cong j 0 y ∧ cong b 0 y → p ≥ y, from
        (assume P: cong j 0 y ∧ cong b 0 y,
        have r: cong b 0 y, from P.2,
        have l: cong j 0 y, from P.1,
        have F: cong p 0 y, from exists.elim (W11) (fun (x : int) (F1: ∃ w:int, j*x + b*w  = p),
            exists.elim F1 (fun (w : int) (F2: j*x + b*w = p),

            have r2: cong (b*w) (0*w) y, from Mmul y r,
            have r3: cong (b*w) 0 y, from MinsertRight r2 (zero_mul w),

            have l2: cong (j*x) (0*x) y, from Mmul y l,
            have l3: cong (j*x) 0 y, from MinsertRight l2 (zero_mul x),
            have c: cong (j*x + b*w) 0 y, from MDsum l3 r3,
            have c2 : cong p 0 y, from MinsertLeft c F2,
            c2
    )),
    have en: p ≥ y, from basicInequality F W2,
    en),
    exact goal
end

theorem IntegersFormPID (j : int) (b : int): ∃ g:int, LDE j b g ∧ gcd j b g :=
begin
have H1: ∃ g:int, LDE j b g ∧ gcd j b g, from exists.elim (ELDE j b) 
    (fun (p:int) (W1: LDE j b p ∧ p > 0 ∧  (∀ q: int,  LDE j b q → q ≥ p)), 
    have Ha: cong j 0 p, from LDEsimp W1,
    have W11: LDE j b p, from W1.1,
    have W12: LDE b j p, from LDEcomm W11,
    have W2: p > 0, from W1.2.1,
    have W6: (∀ q: int, LDE b j q → q ≥ p), from (λ q H, (W1.2.2 q) (LDEcomm H)),
    have W7: LDE b j p ∧ p > 0 ∧  (∀ q: int, LDE b j q → q ≥ p), from ⟨W12,W2,W6⟩,
    have Hb: cong b 0 p, from LDEsimp W7,

    have pre: (∀ y:int, cong j 0 y ∧ cong b 0 y → p ≥ y), from PisGCD W2 W11,
    have goal: gcd j b p, from ⟨ W2, Ha, Hb, pre⟩,
    exists.intro p (and.intro W11 goal)
    ),
exact H1
end
