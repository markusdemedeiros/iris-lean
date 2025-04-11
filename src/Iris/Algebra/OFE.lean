/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Iris

/-- Ordered family of equivalences -/
class OFE (α : Type _) where
  Equiv : α → α → Prop
  Dist : Nat → α → α → Prop
  dist_eqv : Equivalence (Dist n)
  equiv_dist : Equiv x y ↔ ∀ n, Dist n x y
  dist_lt : Dist n x y → m < n → Dist m x y

open OFE

scoped infix:40 " ≡ " => OFE.Equiv
scoped notation:40 x " ≡{" n "}≡ " y:41 => OFE.Dist n x y

namespace OFE

theorem Dist.lt [OFE α] {m n} {x y : α} : x ≡{n}≡ y → m < n → x ≡{m}≡ y := dist_lt

theorem Dist.le [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (Nat.lt_of_le_of_ne h' hm)

@[simp] theorem Dist.rfl [OFE α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
theorem Dist.symm [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3
theorem Dist.of_eq [OFE α] {x y : α} : x = y → x ≡{n}≡ y := (· ▸ .rfl)

theorem equiv_eqv [ofe : OFE α] : Equivalence ofe.Equiv := by
  constructor
  · rintro x; rw [ofe.equiv_dist]; rintro n; exact Dist.rfl
  · rintro x y; simp [ofe.equiv_dist]; rintro h n; exact Dist.symm (h n)
  · rintro x y z; simp [ofe.equiv_dist]; rintro h₁ h₂ n; exact Dist.trans (h₁ n) (h₂ n)

@[simp] theorem Equiv.rfl [OFE α] {x : α} : x ≡ x := equiv_eqv.1 _
theorem Equiv.symm [OFE α] {x : α} : x ≡ y → y ≡ x := equiv_eqv.2
theorem Equiv.trans [OFE α] {x : α} : x ≡ y → y ≡ z → x ≡ z := equiv_eqv.3
theorem Equiv.dist [OFE α] {x : α} : x ≡ y → x ≡{n}≡ y := (equiv_dist.1 · _)
theorem Equiv.of_eq [OFE α] {x y : α} : x = y → x ≡ y := (· ▸ .rfl)

instance [OFE α] : Trans OFE.Equiv OFE.Equiv (OFE.Equiv : α → α → Prop) where
  trans := Equiv.trans

instance [OFE α] {n : Nat} : Trans (OFE.Dist n) (OFE.Dist n) (OFE.Dist n : α → α → Prop) where
  trans := Dist.trans

/-- A function `f : α → β` is non-expansive if it preserves `n`-equivalence. -/
class NonExpansive [OFE α] [OFE β] (f : α → β) : Prop where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFE α] : NonExpansive (@id α) := ⟨fun _ _ _ h => h⟩

/-- A non-expansive function preserves equivalence. -/
theorem NonExpansive.eqv [OFE α] [OFE β] {f : α → β} [NonExpansive f]
    ⦃x₁ x₂⦄ (h : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  equiv_dist.2 fun _ => ne (equiv_dist.1 h _)

/-- A function `f : α → β → γ` is non-expansive if it preserves `n`-equivalence in each argument. -/
class NonExpansive₂ [OFE α] [OFE β] [OFE γ] (f : α → β → γ) : Prop where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

theorem NonExpansive₂.eqv [OFE α] [OFE β] [OFE γ] {f : α → β → γ} [NonExpansive₂ f]
    ⦃x₁ x₂⦄ (hx : x₁ ≡ x₂) ⦃y₁ y₂⦄ (hy : y₁ ≡ y₂) : f x₁ y₁ ≡ f x₂ y₂ :=
  equiv_dist.2 fun _ => ne hx.dist hy.dist

/-- `DistLater n x y` means that `x` and `y` are `m`-equivalent for all `m < n`. -/
def DistLater [OFE α] (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

@[simp] theorem DistLater.rfl [OFE α] {n} {x : α} : DistLater n x x := fun _ _ => .rfl
theorem DistLater.symm [OFE α] {n} {x : α} (h : DistLater n x y) : DistLater n y x :=
  fun _ hm => (h _ hm).symm
theorem DistLater.trans [OFE α] {n} {x : α} (h1 : DistLater n x y) (h2 : DistLater n y z) :
    DistLater n x z := fun _ hm => (h1 _ hm).trans (h2 _ hm)

/-- `DistLater n`-equivalence is an equivalence relation. -/
theorem distLater_eqv [OFE α] {n} : Equivalence (α := α) (DistLater n) where
  refl _ := DistLater.rfl
  symm h := h.symm
  trans h1 := h1.trans

/-- `n`-equivalence implies `DistLater n`-equivalence. -/
theorem Dist.distLater [OFE α] {n} {x y : α} (h : x ≡{n}≡ y) : DistLater n x y :=
  fun _ => dist_lt h

/-- `DistLater n`-equivalence implies `m`-equivalence for all `m < n`. -/
theorem DistLater.dist_lt [OFE α] {m n} {x y : α} (h : DistLater n x y) (hm : m < n) : x ≡{m}≡ y :=
  h _ hm

/-- `DistLater 0`-equivalence is trivial. -/
@[simp] theorem distLater_zero [OFE α] {x y : α} : DistLater 0 x y := nofun

/-- `DistLater n`-equivalence is equivalent to `(n + 1)`-equivalence. -/
theorem distLater_succ [OFE α] {n} {x y : α} : DistLater n.succ x y ↔ x ≡{n}≡ y :=
  ⟨(·.dist_lt (Nat.lt_succ_self _)), fun h1 _ h2 => h1.le (Nat.le_of_lt_succ h2)⟩

/-- A function `f : α → β` is contractive if it sends `DistLater n`-equivalent inputs to `n`-equivalent outputs. -/
class Contractive [OFE α] [OFE β] (f : α → β) : Prop where
  distLater_dist : DistLater n x y → f x ≡{n}≡ f y

@[simp] theorem Contractive.zero [OFE α] [OFE β] (f : α → β) [Contractive f] {x y} :
    f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

/-- A contractive function is non-expansive. -/
instance [OFE α] [OFE β] (f : α → β) [Contractive f] : NonExpansive f where
  ne := fun _ _ _ h => Contractive.distLater_dist (Dist.distLater h)

/-- A contractive function preserves equivalence. -/
theorem Contractive.eqv [OFE α] [OFE β] (f : α → β) [Contractive f] ⦃x y : α⦄ (h : x ≡ y) :
    f x ≡ f y := NonExpansive.eqv h

/-- Constant functions are contractive. -/
instance [OFE α] [OFE β] {x : β} : Contractive (fun _ : α => x) where
  distLater_dist := fun _ => Dist.rfl

/-- The discrete OFE obtained from an equivalence relation `Equiv` -/
def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : OFE α where
  Equiv := Equiv
  Dist _ := Equiv
  dist_eqv := equiv_eqv
  equiv_dist := (forall_const _).symm
  dist_lt h _ := h

/-- A discrete element in an OFE -/
def DiscreteE {α : Type _} [OFE α] (x : α) : Prop :=
  ∀ {y : α}, x ≡{0}≡ y → x ≡ y

/-- A discrete OFE is one where equivalence is implied by `0`-equivalence. -/
class Discrete (α : Type _) [OFE α] : Prop where
  discrete_0 {x y : α} : x ≡{0}≡ y → x ≡ y

/-- For discrete OFEs, `n`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete_n [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{n}≡ y) : x ≡ y :=
  Discrete.discrete_0 (OFE.Dist.le h (Nat.zero_le _))

class Leibniz (α : Type _) [OFE α] : Prop where
  leibniz {x y : α} : x ≡ y ↔ x = y


/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is non-expansive. -/
@[ext] structure Hom (α β : Type _) [OFE α] [OFE β] where
  f : α → β
  ne : NonExpansive f

@[inherit_doc]
infixr:25 " -n> " => Hom

instance [OFE α] [OFE β] : CoeFun (α -n> β) (fun _ => α → β) := ⟨Hom.f⟩
instance [OFE α] [OFE β] (f : α -n> β) : NonExpansive f := f.ne

/-- The identity morphism on an OFE. -/
protected def Hom.id [OFE α] : α -n> α where
  f := id
  ne.ne _ _ _ := id

/-- The composition of two morphisms between OFEs. -/
protected def Hom.comp [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  f := g.f ∘ f.f
  ne.1 _ _ _ h := g.ne.1 (f.ne.1 h)

@[simp] theorem Hom.id_apply [OFE α] {x} : (Hom.id : α -n> α) x = x := rfl
@[simp] theorem Hom.comp_apply [OFE α] [OFE β] [OFE γ] {g : β -n> γ} {f : α -n> β} {x} :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem Hom.id_comp [OFE α] [OFE β] {f : α -n> β} : Hom.id.comp f = f := rfl
@[simp] theorem Hom.comp_id [OFE α] [OFE β] {f : α -n> β} : f.comp Hom.id = f := rfl

theorem Hom.comp_assoc [OFE α] [OFE β] [OFE γ] [OFE δ]
    (h : γ -n> δ) (g : β -n> γ) (f : α -n> β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem InvImage.equivalence {α : Sort u} {β : Sort v}
    {r : β → β → Prop} {f : α → β} (H : Equivalence r) : Equivalence (InvImage r f) where
  refl _ := H.refl _
  symm := H.symm
  trans := H.trans

instance : OFE Unit where
  Equiv _ _ := True
  Dist _ _ _ := True
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  equiv_dist := by simp
  dist_lt _ _ := ⟨⟩

instance [OFE α] : OFE (ULift α) where
  Equiv x y := x.down ≡ y.down
  Dist n x y := x.down ≡{n}≡ y.down
  dist_eqv := InvImage.equivalence dist_eqv
  equiv_dist := equiv_dist
  dist_lt := dist_lt

def uliftUpHom [OFE α] : α -n> ULift α where
  f := .up
  ne.1 _ _ _ := id

def uliftDownHom [OFE α] : ULift α -n> α where
  f := ULift.down
  ne.1 _ _ _ := id

def _root_.Option.Forall₂ (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem _root_.Option.Forall₂.equivalence {R : α → α → Prop}
    (H : Equivalence R) : Equivalence (Option.Forall₂ R) where
  refl | none => trivial | some _ => H.1 _
  symm {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply H.2
  trans {x y z} := by cases x <;> cases y <;> cases z <;> simp [Option.Forall₂]; apply H.3

instance [OFE α] : OFE (Option α) where
  Equiv := Option.Forall₂ Equiv
  Dist n := Option.Forall₂ (Dist n)
  dist_eqv := Option.Forall₂.equivalence dist_eqv
  equiv_dist {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply equiv_dist
  dist_lt {_ x y _} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply dist_lt

theorem OFE.eqv_of_some_eqv_some [OFE α] {x y : α} (h : some x ≡ some y) : x ≡ y := h
theorem OFE.some_eqv_some_of_eqv [OFE α] {x y : α} (h : x ≡ y) : some x ≡ some y := h

theorem OFE.equiv_some [OFE α] {o : Option α} {y : α} (e : o ≡ some y) :
    ∃ z, o = some z ∧ z ≡ y := by
  unfold OFE.Equiv instOption Option.Forall₂ at e
  match o with
  | .none => dsimp at e
  | .some x => dsimp at e; exact ⟨x, rfl, e⟩

theorem OFE.equiv_none [OFE α] {o : Option α} (e : o ≡ none): o = none :=
  match o with
  | none => rfl
  | some _ => e.elim

theorem OFE.dist_some_right [OFE α] {n mx y} (h : mx ≡{n}≡ some y) :
    ∃ z : α, mx = some z ∧ y ≡{n}≡ z :=
  suffices hh : ∀ mx my y, mx ≡{n}≡ my → my = some y → ∃ t, mx = some t ∧ t ≡{n}≡ y from
    (hh mx (some y) _ h rfl).elim (fun t h => ⟨t, h.left, h.right.symm⟩)
  fun mx _ y e1 e2 =>
    match mx with
    | some t => ⟨t, rfl, (e2 ▸ e1 : some t ≡{n}≡ some y)⟩
    | none => False.elim (e2 ▸ e1 : none ≡{n}≡ some y)

instance [OFE α] [Leibniz α] : Leibniz (Option α) where
  leibniz {x y} :=
    suffices h: x ≡ y → x = y from ⟨h, Equiv.of_eq⟩
    match x, y with
    | none, none => fun _ => rfl
    | some _, some _ => fun h => congrArg some (Leibniz.leibniz.mp h)
    | none, some _ => fun h => h.elim
    | some _, none => fun h => h.elim

instance [OFE α] [OFE β] : OFE (α -n> β) where
  Equiv f g := ∀ x, f x ≡ g x
  Dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  equiv_dist {_ _} := by simp [equiv_dist]; apply forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2

instance [OFE α] [OFE β] : OFE (α × β) where
  Equiv a b := a.1 ≡ b.1 ∧ a.2 ≡ b.2
  Dist n a b := a.1 ≡{n}≡ b.1 ∧ a.2 ≡{n}≡ b.2
  dist_eqv := {
    refl _ := ⟨dist_eqv.refl _, dist_eqv.refl _⟩
    symm h := ⟨dist_eqv.symm h.1, dist_eqv.symm h.2⟩
    trans h1 h2 := ⟨dist_eqv.trans h1.1 h2.1, dist_eqv.trans h1.2 h2.2⟩
  }
  equiv_dist {_ _} := by simp [equiv_dist, forall_and]
  dist_lt h1 h2 := ⟨dist_lt h1.1 h2, dist_lt h1.2 h2⟩

/-- An isomorphism between two OFEs is a pair of morphisms whose composition is equivalent to the identity morphism. -/
@[ext] structure Iso (α β : Type _) [OFE α] [OFE β] where
  hom : α -n> β
  inv : β -n> α
  hom_inv : hom (inv x) ≡ x
  inv_hom : inv (hom x) ≡ x

attribute [simp] Iso.hom_inv Iso.inv_hom

instance [OFE α] [OFE β] : CoeFun (Iso α β) (fun _ => α -n> β) := ⟨Iso.hom⟩
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.hom := iso.hom.ne
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.inv := iso.inv.ne

@[simp] theorem Iso.hom_inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.hom (iso.inv x) ≡{n}≡ x :=
  OFE.equiv_dist.mp (Iso.hom_inv iso) _

@[simp] theorem Iso.inv_hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.inv (iso.hom x) ≡{n}≡ x :=
  OFE.equiv_dist.mp (Iso.inv_hom iso) _

/-- OFE isomorphisms preserve equivalence. -/
theorem Iso.hom_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x ≡ y ↔ iso.hom x ≡ iso.hom y :=
  ⟨fun h => NonExpansive.eqv h,
  fun h => Equiv.trans (Equiv.symm iso.inv_hom) <| Equiv.trans (NonExpansive.eqv h) (iso.inv_hom)⟩

/-- The inverse of an OFE isomorphism preserves equivalence. -/
theorem Iso.inv_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x ≡ y ↔ iso.inv x ≡ iso.inv y :=
  ⟨fun h => NonExpansive.eqv h,
  fun h => Equiv.trans (Equiv.symm iso.hom_inv) <| Equiv.trans (NonExpansive.eqv h) (iso.hom_inv)⟩

/-- OFE isomorphisms preserve `n`-equivalence. -/
theorem Iso.hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.hom x ≡{n}≡ iso.hom y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.inv_hom_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.inv_hom_dist)⟩

/-- The inverse of an OFE isomorphism preserves `n`-equivalence. -/
theorem Iso.inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.inv x ≡{n}≡ iso.inv y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.hom_inv_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.hom_inv_dist)⟩

/-- The identity OFE isomorphism -/
def Iso.id [OFE α] : Iso α α where
  hom := Hom.id
  inv := Hom.id
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

@[simp] theorem Iso.id_apply [OFE α] {x} : ((Iso.id : Iso α α) : α -n> α) x = x := rfl

/-- The inverse of an OFE isomorphism -/
def Iso.symm [OFE α] [OFE β] (iso : Iso α β) : Iso β α where
  hom := iso.inv
  inv := iso.hom
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

/-- Composition of OFE isomorphisms -/
def Iso.comp [OFE α] [OFE β] [OFE γ] (iso1 : Iso β γ) (iso2 : Iso α β) : Iso α γ where
  hom := iso1.hom.comp iso2.hom
  inv := iso2.inv.comp iso1.inv
  hom_inv := by
    intro x; simp
    exact .trans (NonExpansive.eqv <| .trans iso2.hom_inv .rfl) iso1.hom_inv
  inv_hom := by
    intro x; simp
    exact .trans (NonExpansive.eqv <| .trans iso1.inv_hom .rfl) iso2.inv_hom

end OFE

/-- A chain in an OFE is a `Nat`-indexed sequence of elements that is upward-closed in terms of `n`-equivalence. -/
structure Chain (α : Type _) [OFE α] where
  chain : Nat → α
  cauchy : n ≤ i → chain i ≡{n}≡ chain n

instance [OFE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.chain⟩

namespace Chain

/-- The constant chain. -/
def const [OFE α] (a : α) : Chain α where
  chain := fun _ => a
  cauchy _ := OFE.Dist.rfl

@[simp] theorem const_apply [OFE α] {a : α} {n} : const a n = a := rfl

/-- Mapping a chain through a non-expansive function. -/
def map [OFE α] [OFE β] (f : α -n> β) (c : Chain α) : Chain β where
  chain n := f (c n)
  cauchy h := f.ne.1 (c.cauchy h)

@[simp] theorem map_apply [OFE α] [OFE β] {f : α -n> β} {c : Chain α} {n} :
    map f c n = f (c n) := rfl

@[simp] theorem map_id [OFE α] {c : Chain α} : map (Hom.id : α -n> α) c = c := by
  simp [map]

theorem map_comp [OFE α] [OFE β] [OFE γ] {f : α -n> β} {g : β -n> γ} {c : Chain α} :
    map (g.comp f) c = map g (map f c) := by
  simp [map]

end Chain

/-- Complete ordered family of equivalences -/
class IsCOFE (α : Type _) [OFE α] where
  compl : Chain α → α
  conv_compl {c : Chain α} : compl c ≡{n}≡ c n

/-- Complete ordered family of equivalences -/
class abbrev COFE (α : Type _) := OFE α, IsCOFE α

namespace COFE
export IsCOFE (compl conv_compl)

theorem conv_compl' [COFE α] {c : Chain α} {n i} (h : n ≤ i) : compl c ≡{n}≡ c i :=
  conv_compl.trans (c.cauchy h).symm

/-- Chain maps commute with completion. -/
theorem compl_map [COFE α] [COFE β] (f : α -n> β) (c : Chain α) :
    compl (Chain.map f c) ≡ f (compl c) := by
  refine OFE.equiv_dist.mpr (fun n => ?_)
  exact Dist.trans conv_compl (NonExpansive.ne (Dist.symm conv_compl))

/-- Constant chains complete to their constant value -/
@[simp] theorem compl_const [COFE α] (a : α) : compl (Chain.const a) ≡ a :=
  OFE.equiv_dist.mpr (fun _ => conv_compl)

/-- Completion of discrete COFEs is the constant value. -/
@[simp] theorem discrete_cofe_compl [COFE α] [OFE.Discrete α] (c : Chain α) : compl c ≡ c 0 :=
  Discrete.discrete_0 conv_compl

/-- The discrete COFE obtained from an equivalence relation `Equiv` -/
def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : COFE α :=
  let _ := OFE.ofDiscrete Equiv equiv_eqv
  { compl := fun c => c 0
    conv_compl := fun {_ c} => equiv_eqv.2 (c.cauchy (Nat.zero_le _)) }

instance [COFE α] : COFE (ULift α) where
  compl c := ⟨compl (c.map uliftDownHom)⟩
  conv_compl := conv_compl

instance : COFE Unit where
  compl _ := ()
  conv_compl := ⟨⟩


abbrev OFunctorPre := (α : Type _) → (β : Type _) -> [OFE α] → [OFE β] → Type _

class OFunctor (F : ∀ α β [OFE α] [OFE β], Type _) where
  -- EXPERIMENT: Replacing COFE in this definition with OFE
  -- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/OFunctor.20definition
  -- cofe [COFE α] [COFE β] : OFE (F α β)
  cofe [OFE α] [OFE β] : OFE (F α β)
  map [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [OFE α] [OFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [OFE α₁] [OFE α₂] [OFE α₃] [OFE β₁] [OFE β₂] [OFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)

class OFunctorContractive (F : ∀ α β [OFE α] [OFE β], Type _) extends OFunctor F where
  map_contractive [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [instance] OFunctor.cofe

end COFE

section Leibniz

structure LeibnizO (T : Type _) where
  car : T

theorem Eq_Equivalence {T : Type _} : Equivalence (@Eq T) :=
  ⟨ congrFun rfl, (Eq.symm ·), (· ▸ ·)⟩

instance : COFE (LeibnizO T) := COFE.ofDiscrete _ Eq_Equivalence

end Leibniz

/-
/- A dependent function `F` has types ranging in OFE -/
class IsOFEFun (F : α → Type _) where
  ofe {x : α} : OFE (F x)

attribute [instance] IsOFEFun.ofe
-/

/- Type alias for a discrete function -/
structure discrete_fun {α : Type} (F : α → Type _) : Type _ where
  car : (x : α) → F x

/-- Non-dependent discrete function -/
notation:25 x:26 " -d> " y:25 => @discrete_fun x (fun _ => y)

-- instance {α β : Type _} [O : OFE β] : IsOFEFun (fun (_ : α) => β) := ⟨ O ⟩

instance {α : Type _} {β : α -> Type _} : CoeFun (discrete_fun β) (fun _ => ((x : α) -> β x)) :=
  ⟨ fun f => f.car ⟩

section DiscreteFunCOFE

variable {α : Type _} (β : α -> Type _)

abbrev OFEFun (β : α → Type _) := ∀ a, OFE (β a)
abbrev IsCOFEFun (β : α -> Type _) [OFEFun β] := ∀ x : α, IsCOFE (β x)

@[simp]
def discrete_fun.equiv [OFEFun β] (f g : discrete_fun β): Prop := ∀ (x : α), f x ≡ g x

@[simp]
def discrete_fun.dst [OFEFun β] (n : Nat) (f g : discrete_fun β) : Prop := ∀ (x : α), f x ≡{n}≡ g x

theorem discrete_fun.dst_Equiv [OFEFun β] n : Equivalence (@discrete_fun.dst α β _ n) :=
  ⟨ by simp,
    by simp; exact fun H x => Dist.symm (H x) ,
    by simp; exact fun H1 H2 x => Dist.trans (H1 x) (H2 x) ⟩

instance discrete_fun.OFE [OFEFun β] : OFE (discrete_fun β) where
  Equiv := discrete_fun.equiv β
  Dist := discrete_fun.dst β
  dist_eqv {n} := discrete_fun.dst_Equiv β n
  equiv_dist :=
    ⟨ fun H _ x => Equiv.dist (H x),
      fun H _ => equiv_dist.mpr (H · _) ⟩
  dist_lt := by simp; exact fun H Hn x => Dist.lt (H x) Hn

def discrete_fun.chain [OFEFun β] (c : Chain (discrete_fun β)) (x : α) : Chain (β x) where
  chain n := c n x
  cauchy H := c.cauchy H x

instance discrete_fun.IsCOFE [OFEFun β] [IsCOFEFun β] : IsCOFE (discrete_fun β) where
  compl c := ⟨ fun x => IsCOFE.compl (discrete_fun.chain β c x) ⟩
  conv_compl _ := IsCOFE.conv_compl

end DiscreteFunCOFE


section DiscreteFunOF

variable {α : Type _} {β₁ β₂ β₃ : α -> Type _} -- [IsOFEFun β₁] [IsOFEFun β₂] [IsOFEFun β₃]

def discrete_fun.map (f : ∀ x, β₁ x → β₂ x) (g : discrete_fun β₁) : discrete_fun β₂ :=
  ⟨ fun x => f x (g x) ⟩

theorem  discrete_fun.map.ext [OFEFun β₂] (f₁ f₂ : ∀ x, β₁ x → β₂ x) (g : discrete_fun β₁) :
    (∀ x, f₁ x (g x) ≡ f₂ x (g x)) → map f₁ g ≡ map f₂ g := by
  simp only [map]; exact id

theorem discrete_fun.map.id (g : discrete_fun β₁) :
    map (fun _ => id) g = g := by simp [map]

theorem discrete_fun.map.comp (f₁ : ∀ x, β₁ x → β₂ x) (f₂: ∀ x, β₂ x → β₃  x) (g : discrete_fun β₁) :
    map (fun x => f₂ x ∘ f₁ x) g = map f₂ (map f₁ g) := by simp [map]

-- Can this be stated as NonExpansive or is using the same n everywhere important?
theorem discrete_fun.map.ne [OFEFun β₁] [OFEFun β₂] (f : ∀ x, β₁ x → β₂ x)
    (H : ∀ x, NonExpansive (f x)) : NonExpansive (discrete_fun.map f) :=
  ⟨ fun _ _ _ Hx x => by apply (H x).ne; apply Hx ⟩

abbrev discrete_fun_OF {C} (F : C → COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => discrete_fun (fun (c : C) => (F c) A B)

-- Works
-- variable {α₁ β₁ C : Type _} (F : C → Type _ → Type _ → Type _) [∀ A B, IsOFEFun fun c => F c A B]
-- #synth OFE (discrete_fun_OF F α₁ β₁)

instance discrete_fun_OFunctor {C} (F : C → COFE.OFunctorPre) [HOF : ∀ c, COFE.OFunctor (F c)] :
    COFE.OFunctor (discrete_fun_OF F) where
  cofe {α β _ _} := discrete_fun.OFE (fun c => F c α β)
  map f₁ f₂ :=
    ⟨ discrete_fun.map (fun c => COFE.OFunctor.map (F := (F c)) f₁ f₂),
      by
        apply discrete_fun.map.ne
        exact fun c => ((HOF c).map f₁ f₂).ne ⟩
  map_ne := by
    intros _ _ _ _ _ _ _ _
    constructor
    intros n x1 x2 Hx y1 y2 Hy z c
    simp
    sorry
  map_id := by
    intros
    simp [discrete_fun.map]
    sorry
  map_comp := sorry

end DiscreteFunOF



/- Wrapper around the Option type, so that the OFE doesn't get inferred
   for eg. partial values -/
structure OptionO (α : Type _ )where
  car : Option α


section Option

variable [OFE α]

instance OptionO_OFE : OFE (OptionO α) where
  Equiv f g :=
    match (f, g) with
    | ⟨ ⟨ some f' ⟩, ⟨ some g' ⟩ ⟩ => f' ≡ g'
    | ⟨ ⟨ none ⟩, ⟨ none ⟩ ⟩ => True
    | _ => False
  Dist n f g :=
    match (f, g) with
    | ⟨ ⟨ some f' ⟩, ⟨ some g' ⟩ ⟩ => f' ≡{n}≡ g'
    | ⟨ ⟨ none ⟩, ⟨ none ⟩ ⟩ => True
    | _ => False
  dist_eqv :=
    ⟨ (by
        intro x
        cases x; rename_i x
        cases x <;> simp),
      (by
        intro x y
        cases x; rename_i x
        cases y; rename_i y
        cases x <;> cases y <;> simp
        intro H
        apply H.symm),
      (by
        intro x y z
        cases x; rename_i x
        cases y; rename_i y
        cases z; rename_i z
        cases x <;> cases y <;> cases z <;> simp
        intro H1 H2
        apply Dist.trans H1 H2)⟩
  equiv_dist := sorry
  dist_lt := sorry

instance OptionO_COFE [IsCOFE α] : IsCOFE (OptionO α) where
  compl := sorry
  conv_compl := sorry

end Option


def OptionOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => OptionO (F A B)

section OptionOF

variable (F : COFE.OFunctorPre) [COFE.OFunctor F]

-- instance [COFE.OFunctor F] : OFE (OptionOF F α₁ β₁) := by
--   unfold OptionOF
--   infer_instance

instance OptionO_OFunctor : COFE.OFunctor (OptionOF F) where
  cofe := OptionO_OFE
  map f g := sorry -- TC problems?
  map_ne := sorry
  map_id := sorry
  map_comp := sorry

instance [COFE.OFunctorContractive F] : COFE.OFunctorContractive (OptionOF F) where
  map_contractive := sorry

end OptionOF
