constants a b c: int
constants  x y z m: nat
constant modus_ponens {p q : Prop} : implies p q → p → q

def cong (a:int) (b: int) (m: nat): Prop := ∃ x: int, a-b = m*x

def is_prime (p:nat): Prop := ∀ x y: int, cong (x*y) 0 p → cong x 0 p ∨ cong y 0 p

axiom floor (a: int) (b:int): ∃ x:int, (x*b ≤ a ∧ ∀  y: int, y*b ≤ a → y≤x)

-- The division algorithm is essentially encoded in above definition 
-- We aim to construct number theory without the use of WOP via this method 

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

theorem Msymmetric {a b : int} {m: nat} (H1: cong a b m): cong b a m :=
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

theorem Mmul {x a b: int} (n:nat) (H1: cong a b n) : cong (a*x) (b*x) n:=
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

theorem MinsertLeft {a b c: int} {n:nat} (H1: cong a b n) (H2: a = c): cong c b n:=
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

theorem MinsertRight {a b c: int} {n:nat} (H1: cong a b n) (H2: b = c): cong a c n:=
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
have goal: cong x 0 p ∨ cong (a-b) 0 p, from modus_ponens (H1 x (a-b)) L3,
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
