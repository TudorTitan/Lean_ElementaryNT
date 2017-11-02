constants a b c: int
constants  x y z m: nat
constant modus_ponens {p q : Prop} : implies p q → p → q

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

axiom WOP {k: nat} (p:nat → Prop) (H: p k): ∃ n: nat, p n ∧ (∀ y:nat, p y → y ≥ x)

--

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

lemma LDEsimp {a b p :int} (W1: (LDE a b p ∧ p > 0) ∧ (∀ (q: int), LDE a b q → q ≥ p)) : cong a 0 p:=
begin
exact exists.elim (and.elim_left (and.elim_left W1))
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
                        have C1: ∀ q: int, LDE a b q → q ≥ p, from  (and.elim_right W1),
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


--WIP


lemma LDEcomm (a: int) (b: int) (p: int) : LDE a b p ↔ LDE b a p :=
begin
have H:LDE a b p ↔ LDE b a p, from sorry,
exact H
end

theorem IntegersFormPID (a : int) (b : int): ∃ g:int, LDE a b g ∧ gcd a b g :=
begin
have H1: ∃ g:int, LDE a b g ∧ gcd a b g, from exists.elim (ELDE a b) 
    (fun (p:int) (W1: (LDE a b p ∧ p > 0) ∧  (∀ q: int, LDE a b q → q ≥ p)), 
    have H: cong a 0 p, from LDEsimp W1,
    have W11: LDE a b p, from (and.elim_left (and.elim_left W1)),
    have W12: LDE b a p, from iff.elim_left (LDEcomm a b p) W11,
    have W2: p > 0, from and.elim_right (and.elim_left W1),
    have W31: LDE a b p → LDE b a p, from iff.elim_left (LDEcomm a b p),
    have W3: (∀ q: int, LDE b a q → q ≥ p), from iff_subst (LDEcomm a b p) (and.elim_right (and.elim_right W1)),
    have W2: (LDE b a p ∧ p > 0) ∧  (∀ q: int, LDE b a q → q ≥ p), from iff_subst (LDEcomm a b p) W1,
    have Hb: cong b 0 p, from LDEsimp W1,
    )
end

