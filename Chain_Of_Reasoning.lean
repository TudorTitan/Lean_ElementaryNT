theorem DivAlgo {q r: int} (a : int) (b : int): ∃ q r: int, a = b*q + r ∧ 0 ≤ r ∧ b > r :=
begin 
have Q: ∃ q r: int, a = b*q + r ∧ 0 ≤ r ∧ b > r, 
    from exists.elim (floor a b) (fun (x:int) (H: x*b ≤ a ∧ ∀  y: int, y*b ≤ a → y≤x),
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
