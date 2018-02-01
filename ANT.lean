-- Needed for sheaves temporarily
import analysis.topology.topological_space

-- Auxiliary lemmas

lemma exists_and_commute {α : Type} {p q r: α → Prop} : 
(∃! a : α, r a ∧ p a ∧ q a) → ∃! a : α, r a ∧ q a ∧ p a :=
    λ ⟨a, ⟨b, c ⟩⟩, 
    begin 
        existsi a,
        simp at *,
        exact ⟨b.symm.2, b.symm.1.1 ,b.symm.1.2 ,λ y g h, c y g h⟩ 
    end

-- Categories and functors

structure Category (type : Type) :=
(obj : type → Prop)
(mor : type  → type → (type → type) → Prop)
(associativity : ∀ a b c, ∀ f g : type → type, mor a b f → mor b c g → mor a c (g ∘ f))
(identity: ∀ a, obj a → mor a a id)

structure Functor {a b : Type} (C1: Category a) (C2: Category b) : Type :=
(obj_map: a → b)
(mor_map: (a → a) → (b → b))
(respect_obj: ∀ x, C1.obj x → C2.obj (obj_map x))
(respect_id : mor_map id = id)
(respect_mor: ∀ x y z, C1.mor x y z →  C2.mor (obj_map x) (obj_map y) (mor_map z))
(respect_composition: ∀ f g: a → a, mor_map (f ∘ g) = mor_map f ∘ mor_map g)

structure Contravariant_Functor {a b : Type} (C1: Category a) (C2: Category b) : Type :=
(obj_map: a → b)
(mor_map: (a → a) → (b → b))
(respect_obj: ∀ x, C1.obj x → C2.obj (obj_map x))
(respect_id : mor_map id = id)
(swap_mor: ∀ x y z, C1.mor x y z →  C2.mor (obj_map y) (obj_map x) (mor_map z))
(respect_composition: ∀ f g: a → a, mor_map (f ∘ g) = mor_map g ∘ mor_map f)

-- Notions of isomorphims

definition isomorphism {a: Type} (x : Category a) (f: a → a) (b c: a)
    := ∃ g : a → a, f ∘ g = id ∧ g ∘ f = id ∧ x.mor b c f ∧ x.mor c b g

definition isomorphic {a: Type} (x : Category a) (b c : a) 
    := ∃ f : a → a, isomorphism x f b c

-- Category description of groups, groupoids and monoids

structure Groupoid (a: Type) extends x : Category a :=
(isomorphisms: ∀ f: a → a, ∃ b c: a, x.obj b ∧ x.obj c ∧ isomorphism x f b c)

structure Monoid (a: Type) extends x : Category a :=
(singleton : a)
(monoid : ∀ c : a, obj c ↔ c = singleton)

structure Group (a: Type) extends Monoid a :=
(isomorphisms: ∀ f: a → a, ∃ b c: a, x.obj b ∧ x.obj c ∧ isomorphism x f b c)

-- Initial, terminal and zero objects

definition initial_object {t: Type} (c : Category t) (a: t) 
    := c.obj a ∧ ∀ b : t, c.obj b → ∃! f : t → t, c.mor a b f

definition terminal_object {t: Type} (c : Category t) (a: t) 
    := c.obj a ∧ ∀ b : t, c.obj b → ∃! f : t → t, c.mor b a f

definition zero_object {t: Type} (c : Category t) (a: t)
    := c.obj a ∧ initial_object c a ∧ terminal_object c a

-- Lemmas for uniqueness of zero, terminal and initial objects up to isomorphism

lemma unique_initial {t: Type } : ∀ c : Category t, ∀ a b: t, initial_object c a ∧ initial_object c b → isomorphic c a b :=
begin
intros,
unfold isomorphic,
unfold initial_object at a_1,
cases a_1,
intros,

apply exists.elim ((right.2 a) left.1),
intros,

apply exists.elim ((left.2 b) right.1),
intros,

existsi (a_3),
existsi (a_1),

have H: c.mor b b (a_3∘a_1), from c.associativity b a b a_1 a_3 a_2.1 a_4.1,
apply exists.elim ((right.2 b) right.1),
intros,
have H2: a_3∘a_1 = a_5, from a_6.2 (a_3∘a_1) H,
have I1: id = a_5, from a_6.2 id ((c.identity b) right.1),
subst I1,

have HH: c.mor a a (a_1∘a_3), from c.associativity a b a a_3 a_1 a_4.1 a_2.1,
apply exists.elim ((left.2 a) left.1),
intros,
have H3: a_1∘a_3 = a_5, from a_7.2 (a_1∘a_3) HH,
have I2: id = a_5, from a_7.2 id ((c.identity a) left.1),
subst I2,

rw [H2, H3],
simp,

exact and.intro a_4.1 a_2.1
end

lemma unique_terminal {t: Type } : ∀ c : Category t, ∀ a b: t, terminal_object c a ∧ terminal_object c b → isomorphic c a b :=
begin
intros,
unfold isomorphic,
unfold terminal_object at a_1,
cases a_1,
intros,

apply exists.elim ((right.2 a) left.1),
intros,

apply exists.elim ((left.2 b) right.1),
intros,

existsi (a_1),
existsi (a_3),

have H: c.mor a a (a_3∘a_1), from c.associativity a b a a_1 a_3 a_2.1 a_4.1,
apply exists.elim ((left.2 a) left.1),
intros,
have H2: a_3∘a_1 = a_5, from a_6.2 (a_3∘a_1) H,
have I1: id = a_5, from a_6.2 id ((c.identity a) left.1),
subst I1,

have HH: c.mor b b (a_1∘a_3), from c.associativity b a b a_3 a_1 a_4.1 a_2.1,
apply exists.elim ((right.2 b) right.1),
intros,
have H3: a_1∘a_3 = a_5, from a_7.2 (a_1∘a_3) HH,
have I2: id = a_5, from a_7.2 id ((c.identity b) right.1),
subst I2,

rw [H2, H3],
simp,

exact ⟨a_2.1, a_4.1⟩ 
end

lemma unique_zero {t: Type } : ∀ c : Category t, ∀ a b: t, zero_object c a ∧ zero_object c b → isomorphic c a b :=
begin
intros,
unfold isomorphic,
unfold zero_object at a_1,

apply unique_initial,
exact and.intro a_1.1.2.1 a_1.2.2.1
end

-- Natural transformations

structure Natural_Transformation {T S : Type} {A : Category T} {B: Category S} (U V: Functor A B) :=
(obj_assign : T → (S → S))
(commutes : ∀ a b f, A.mor a b f → (obj_assign a) ∘ (U.mor_map f) = (V.mor_map f) ∘ (obj_assign b) )
(existence : ∀ a, B.mor (U.obj_map a) (V.obj_map a) (obj_assign a))

-- Monomorphisms and epimorphisms

definition monomorphism {t : Type} {A : Category t} (a b : t) (f : t → t)
    := A.mor a b f ∧ (∀ m g h, A.mor m a g ∧ A.mor m a h ∧ (f ∘ g) = (f ∘ h) → g = h) 

definition epimorphism {t : Type} {A : Category t} (a b : t) (f : t → t)
    := A.mor a b f ∧ (∀ m g h, A.mor b m g ∧ A.mor b m h ∧ (g ∘ f) = (h ∘ f) → g = h) 

-- Composition lemmas for epimorphisms and monomorphisms



-- Products and Coproducts

definition product {t : Type} {A : Category t} (a b : t) (p : t) (f g: t → t)
    := A.obj a ∧ A.obj b ∧ A.obj p ∧ A.mor p a f ∧ A.mor p b g ∧ 
    (∀ k m n, A.obj k ∧ A.mor k a m ∧ A.mor k b n → ∃! u, A.mor k p u ∧ g ∘ u = n ∧ f ∘ u = m ) 

definition coproduct {t : Type} {A : Category t} (a b : t) (p : t) (f g: t → t)
    := A.obj a ∧ A.obj b ∧ A.obj p ∧ A.mor a p f ∧ A.mor b p g ∧ 
    (∀ k m n, A.obj k ∧ A.mor a k m ∧ A.mor b k n → ∃! u, A.mor p k u ∧ u ∘ g = n ∧ u ∘ f = m) 

-- Proof of associativity, commutativity and uniqueness up to isomorphism of product and coproduct

lemma product_commutes {t : Type} {A : Category t} (a b : t) (p : t) (f g: t → t) : @product t A a b p f g → @product t A b a p g f :=
begin
intros,
unfold product at a_1,
unfold product,
have H: (∀ k m n, A.obj k ∧ A.mor k b m ∧ A.mor k a n → ∃! u, A.mor k p u ∧ f ∘ u = n ∧ g ∘ u = m ),
    from ( begin
        intros,
        let X := a_1.2.2.2.2.2 k n m,
        let X2 := X (⟨a_2.1, a_2.2.2, a_2.2.1⟩),
        apply exists_and_commute,
        exact X2
    end ),
exact ⟨a_1.2.1, a_1.1, a_1.2.2.1, a_1.2.2.2.2.1, a_1.2.2.2.1, H⟩ 
end

lemma coproduct_commutes {t : Type} {A : Category t} (a b : t) (p : t) (f g: t → t) : @coproduct t A a b p f g → @coproduct t A b a p g f :=
begin
intros,
unfold coproduct at a_1,
unfold coproduct,
have H: (∀ k m n, A.obj k ∧ A.mor b k m ∧ A.mor a k n → ∃! u, A.mor p k u ∧ u ∘ f = n ∧ u ∘ g = m ),
    from ( begin
        intros,
        let X := a_1.2.2.2.2.2 k n m,
        let X2 := X (⟨a_2.1, a_2.2.2, a_2.2.1⟩),
        apply exists_and_commute,
        exact X2
    end ),
exact ⟨a_1.2.1, a_1.1, a_1.2.2.1, a_1.2.2.2.2.1, a_1.2.2.2.1, H⟩ 
end

-- Equalizers and co-equalizers

definition equalizer {t : Type} {A : Category t} (f g h: t → t) (a b c: t)
    := A.obj a ∧ A.obj b ∧ A.obj c ∧ A.mor b c g  ∧ A.mor b c h  ∧ A.mor a b f 
    ∧ g ∘ f = h ∘ f ∧ (∀ x m, A.mor x b m ∧ g ∘ m = h ∘ m → ∃! u, A.mor x a u 
    ∧ f ∘ u = m) 

definition coequalizer {t : Type} {A : Category t} (f g h: t → t) (a b c: t)
    := A.obj a ∧ A.obj b ∧ A.obj c ∧ A.mor a b g  ∧ A.mor a b h  ∧ A.mor b c f 
    ∧ f ∘ g = f ∘ h ∧ (∀ x m, A.mor b x m ∧ m ∘ g = m ∘ h → ∃! u, A.mor c x u 
    ∧ u ∘ f = m) 

-- Kernels and cokernels



-- Experimental sheaf description

definition inc {A : Type} (a b: set A) (c: set A → set A) {x : Category (set A)} 
    := x.mor a b c ↔ c = id ∧ a ⊂ b 

definition open_category {a: Type} (t : topological_space a) : Category (set a) :=
{
    obj := t.is_open,
    mor := λ A B: set a, λ C: set a → set a, C = id ∧ A ⊆ B,
    associativity := λ a b c, λ f g , begin
        intros h1 h2,
        split,
        rw [h1.1, h2.1], 
        apply id.def,
        exact λ x hx, (h2.2 (h1.2 hx))
    end,
    identity := λ a, begin
        split,
        simp,
        exact λ x hx, hx
    end
}

definition open_Cover {a : Type} (T: topological_space a) (t: set a) (s : set (set a))
    := ⋃₀ s = t ∧ ∀ b ∈ s, T.is_open b

structure Presheaf {a b: Type} (t : topological_space a) (c : Category b) extends Contravariant_Functor (open_category t) c

structure Sheaf {a b: Type} (t : topological_space a) (c : Category b) extends Presheaf t c :=
(sheaf_axiom := ∀ g s, open_Cover t g s → ∀ x y, ∀ f h, c.mor (obj_map y) (obj_map (x ∩ y)) f
 → c.mor (obj_map x) (obj_map (x ∩ y)) h → f (obj_map y) = h (obj_map x) → ∃ n:b, n = (obj_map g) →
   ∀ l ∈ s, ∀ e, c.mor n (obj_map l) e → e n = obj_map l)