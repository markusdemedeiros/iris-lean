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

@[simp, refl] theorem Dist.rfl [OFE α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
@[symm] theorem Dist.symm [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3
theorem Dist.of_eq [OFE α] {x y : α} : x = y → x ≡{n}≡ y := (· ▸ .rfl)

theorem equiv_eqv [ofe : OFE α] : Equivalence ofe.Equiv := by
  constructor
  · rintro x; rw [ofe.equiv_dist]; rintro n; exact Dist.rfl
  · rintro x y; simp [ofe.equiv_dist]; rintro h n; exact Dist.symm (h n)
  · rintro x y z; simp [ofe.equiv_dist]; rintro h₁ h₂ n; exact Dist.trans (h₁ n) (h₂ n)

@[simp, refl] theorem Equiv.rfl [OFE α] {x : α} : x ≡ x := equiv_eqv.1 _
@[symm] theorem Equiv.symm [OFE α] {x : α} : x ≡ y → y ≡ x := equiv_eqv.2
theorem Equiv.trans [OFE α] {x : α} : x ≡ y → y ≡ z → x ≡ z := equiv_eqv.3
theorem Equiv.dist [OFE α] {x : α} : x ≡ y → x ≡{n}≡ y := (equiv_dist.1 · _)
theorem Equiv.of_eq [OFE α] {x y : α} : x = y → x ≡ y := (· ▸ .rfl)

instance [OFE α] : Trans OFE.Equiv OFE.Equiv (OFE.Equiv : α → α → Prop) where
  trans := Equiv.trans

instance [OFE α] {n : Nat} : Trans (OFE.Dist n) (OFE.Dist n) (OFE.Dist n : α → α → Prop) where
  trans := Dist.trans

/-- A function `f : α → β` is non-expansive if it preserves `n`-equivalence. -/
class NonExpansive [OFE α] [OFE β] (f : α → β) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFE α] : NonExpansive (@id α) := ⟨fun _ _ _ h => h⟩

/-- A non-expansive function preserves equivalence. -/
theorem NonExpansive.eqv [OFE α] [OFE β] {f : α → β} [NonExpansive f]
    ⦃x₁ x₂⦄ (h : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  equiv_dist.2 fun _ => ne (equiv_dist.1 h _)

/-- A function `f : α → β → γ` is non-expansive if it preserves `n`-equivalence in each argument. -/
class NonExpansive₂ [OFE α] [OFE β] [OFE γ] (f : α → β → γ) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

theorem NonExpansive₂.eqv [OFE α] [OFE β] [OFE γ] {f : α → β → γ} [NonExpansive₂ f]
    ⦃x₁ x₂⦄ (hx : x₁ ≡ x₂) ⦃y₁ y₂⦄ (hy : y₁ ≡ y₂) : f x₁ y₁ ≡ f x₂ y₂ :=
  equiv_dist.2 fun _ => ne hx.dist hy.dist

/-- `DistLater n x y` means that `x` and `y` are `m`-equivalent for all `m < n`. -/
def DistLater [OFE α] (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

@[simp, refl] theorem DistLater.rfl [OFE α] {n} {x : α} : DistLater n x x := fun _ _ => .rfl
@[symm] theorem DistLater.symm [OFE α] {n} {x : α} (h : DistLater n x y) : DistLater n y x :=
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

/-- A function `f : α → β` is contractive if it sends `DistLater n`-equivalent inputs to
`n`-equivalent outputs. -/
class Contractive [OFE α] [OFE β] (f : α → β) where
  distLater_dist : DistLater n x y → f x ≡{n}≡ f y

@[simp] theorem Contractive.zero [OFE α] [OFE β] (f : α → β) [Contractive f] {x y} :
    f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

/-- A contractive function is non-expansive. -/
instance ne_of_contractive [OFE α] [OFE β] (f : α → β) [Contractive f] : NonExpansive f where
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
class DiscreteE {α : Type _} [OFE α] (x : α) : Prop where
  discrete : x ≡{0}≡ y → x ≡ y

/-- A discrete OFE is one where equivalence is implied by `0`-equivalence. -/
class Discrete (α : Type _) [OFE α] where
  discrete_0 {x y : α} : x ≡{0}≡ y → x ≡ y
export OFE.Discrete (discrete_0)

/-- For discrete OFEs, `n`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{n}≡ y) : x ≡ y :=
  discrete_0 (h.le (Nat.zero_le _))
export OFE.Discrete (discrete)

/-- For discrete OFEs, `n`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete_n [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{0}≡ y) : x ≡{n}≡ y :=
  (discrete h).dist
export OFE.Discrete (discrete_n)

class Leibniz (α : Type _) [OFE α] where
  eq_of_eqv {x y : α} : x ≡ y → x = y
export OFE.Leibniz (eq_of_eqv)

@[simp] theorem Leibniz.leibniz [OFE α] [Leibniz α] {x y : α} : x ≡ y ↔ x = y :=
  ⟨eq_of_eqv, .of_eq⟩
export OFE.Leibniz (leibniz)

/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is
non-expansive. -/
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

@[ext] structure ContractiveHom (α β : Type _) [OFE α] [OFE β] extends Hom α β where
  [contractive : Contractive f]
  ne := ne_of_contractive f

infixr:25 " -c> " => ContractiveHom

instance [OFE α] [OFE β] : CoeFun (α -c> β) (fun _ => α → β) := ⟨fun x => x.toHom.f⟩
instance [OFE α] [OFE β] (f : α -c> β) : Contractive f := f.contractive

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

instance [OFE α] [OFE.Discrete α] : OFE.Discrete (Option α) where
  discrete_0 {mx my} e :=
    match mx, my with
    | none,   none   => e
    | none,   some _ => e
    | some _, none   => e
    | some x, some y => show x ≡ y from discrete_0 e

@[simp] theorem some_eqv_some [OFE α] {x y : α} : (some x ≡ some y) ↔ x ≡ y := .rfl
@[simp] theorem not_some_eqv_none [OFE α] {x : α} : ¬some x ≡ none := id
@[simp] theorem not_none_eqv_some [OFE α] {x : α} : ¬none ≡ some x := id

@[simp] theorem some_dist_some [OFE α] {n} {x y : α} : (some x ≡{n}≡ some y) ↔ x ≡{n}≡ y := .rfl
@[simp] theorem not_some_dist_none [OFE α] {n} {x : α} : ¬some x ≡{n}≡ none := id
@[simp] theorem not_none_dist_some [OFE α] {n} {x : α} : ¬none ≡{n}≡ some x := id

theorem equiv_some [OFE α] {o : Option α} {y : α} (e : o ≡ some y) :
    ∃ z, o = some z ∧ z ≡ y := by
  let .some x := o
  exact ⟨x, rfl, e⟩

theorem equiv_none [OFE α] {o : Option α} : o ≡ none ↔ o = none :=
  ⟨fun _ => let .none := o; rfl, (· ▸ .rfl)⟩

theorem dist_some [OFE α] {n mx y} (h : mx ≡{n}≡ some y) :
    ∃ z : α, mx = some z ∧ y ≡{n}≡ z :=
  suffices hh : ∀ mx my y, mx ≡{n}≡ my → my = some y → ∃ t, mx = some t ∧ t ≡{n}≡ y from
    (hh mx (some y) _ h rfl).elim (fun t h => ⟨t, h.left, h.right.symm⟩)
  fun mx _ y e1 e2 =>
    match mx with
    | some t => ⟨t, rfl, (e2 ▸ e1 : some t ≡{n}≡ some y)⟩
    | none => False.elim (e2 ▸ e1 : none ≡{n}≡ some y)

instance [OFE α] [Leibniz α] : Leibniz (Option α) where
  eq_of_eqv {x y} H :=
    match x, y, H with
    | none, none, _ => rfl
    | some _, some _, h => congrArg some (Leibniz.eq_of_eqv h)

instance [OFE α] [Discrete α] : Discrete (Option α) where
  discrete_0 {x y} H :=
    match x, y with
    | none, none => H
    | some _, some _ => some_eqv_some.mpr (discrete_0 H)

instance OFE.Option.some.ne [OFE α] : OFE.NonExpansive (some : α → Option α) := ⟨fun _ _ _ => id⟩

theorem Option.some_is_discrete [OFE α] {a : α} (Ha : DiscreteE a) : DiscreteE (some a) := by
  constructor
  intro y H; cases y
  · exact H
  · exact Ha.discrete H

theorem Option.none_is_discrete [OFE α] : DiscreteE (none : Option α) := by
  constructor
  intro y; cases y <;> simp

abbrev OFEFun {α : Type _} (β : α → Type _) := ∀ a, OFE (β a)

instance [OFEFun (β : α → _)] : OFE ((x : α) → β x) where
  Equiv f g := ∀ x, f x ≡ g x
  Dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  equiv_dist {_ _} := by simp [equiv_dist]; apply forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2

instance [OFE α] [OFE β] : OFE (α -n> β) where
  Equiv f g := f.f ≡ g.f
  Dist n f g := f.f ≡{n}≡ g.f
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  equiv_dist := equiv_dist
  dist_lt := dist_lt

instance [OFE α] [OFE β] : OFE (α -c> β) where
  Equiv f g := Equiv f.toHom g.toHom
  Dist n f g := Dist n f.toHom g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  equiv_dist := equiv_dist
  dist_lt := dist_lt

def applyHom [OFEFun (β : α → _)] (x : α) : ((x : α) → β x) -n> β x where
  f f := f x
  ne.1 _ _ _ H := H x

def mapCodHom [OFEFun (β₁ : α → _)] [OFEFun β₂]
    (F : ∀ x, β₁ x -n> β₂ x) : ((x : α) → β₁ x) -n> ((x : α) → β₂ x) where
  f f x := F x (f x)
  ne.1 _ _ _ H x := (F x).ne.1 (H x)

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

theorem equiv_fst [OFE α] [OFE β] {x y : α × β} (h : x ≡ y) : x.fst ≡ y.fst := h.left
theorem equiv_snd [OFE α] [OFE β] {x y : α × β} (h : x ≡ y) : x.snd ≡ y.snd := h.right
theorem equiv_prod_ext [OFE α] [OFE β] {x₁ x₂ : α} {y₁ y₂ : β}
    (ex : x₁ ≡ x₂) (ey : y₁ ≡ y₂) : (x₁, y₁) ≡ (x₂, y₂) := ⟨ex, ey⟩

theorem dist_fst {n} [OFE α] [OFE β] {x y : α × β} (h : x ≡{n}≡ y) : x.fst ≡{n}≡ y.fst := h.left
theorem dist_snd {n} [OFE α] [OFE β] {x y : α × β} (h : x ≡{n}≡ y) : x.snd ≡{n}≡ y.snd := h.right
theorem dist_prod_ext {n} [OFE α] [OFE β] {x₁ x₂ : α} {y₁ y₂ : β}
    (ex : x₁ ≡{n}≡ x₂) (ey : y₁ ≡{n}≡ y₂) : (x₁, y₁) ≡{n}≡ (x₂, y₂) := ⟨ex, ey⟩

theorem prod.is_discrete [OFE α] [OFE β] {a : α} {b : β} (Ha : DiscreteE a) (Hb : DiscreteE b) :
    DiscreteE (a, b) := by
  constructor
  intro y H; refine ⟨Ha.discrete H.1, Hb.discrete H.2⟩

instance [OFE α] [OFE β] [Discrete α] [Discrete β] : Discrete (α × β) where
  discrete_0 H := by
    constructor
    · apply Discrete.discrete_0
      apply H.1
    · apply Discrete.discrete_0
      apply H.2

/-- An isomorphism between two OFEs is a pair of morphisms whose composition is equivalent to the
identity morphism. -/
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

/-- A chain in an OFE is a `Nat`-indexed sequence of elements that is upward-closed in terms of
`n`-equivalence. -/
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

/-- If a chain of Option is ever none, is the constant none chain. -/
theorem chain_none_const [OFE V] {c : Chain (Option V)} (H : c n = none) :
    c = Chain.const none := by
  rcases c with ⟨c, Hc⟩
  congr 1; refine funext (fun k => ?_)
  rcases Nat.le_or_ge n k with (Hnk|Hnk)
  · suffices c k ≡{n}≡ c n by cases _ : c k <;> simp_all
    exact Hc Hnk
  · suffices c k ≡{k}≡ c n by cases _ : c k <;> simp_all
    exact (Hc Hnk).symm

/-- If a chain of Option is ever some, it is the lift a chain by some. -/
def chain_option_some [OFE V] {c : Chain (Option V)} (H : c n = some v) :
    ∃ c' : Chain V, c = Chain.map ⟨some, OFE.Option.some.ne⟩ c' := by
  have HVc (k) : ∃ v', c k = some v' := by
    rcases h : c.chain k with (_|v')
    · simp [chain_none_const h] at H
    · exists v'
  let c' : Chain V :=
    ⟨fun n => Classical.choose <| HVc n,
     by
       intro n i Hni
       have HR := c.cauchy Hni
       rw [Classical.choose_spec (HVc n), Classical.choose_spec (HVc i)] at HR
       exact HR ⟩
  exists c'
  rcases hcc : c with ⟨cc, Hcc⟩
  simp only [Chain.map, Chain.mk.injEq]
  refine funext (fun i => ?_)
  simp only [c']
  have Hchoose := Classical.choose_spec (HVc i)
  rw [← Hchoose]
  simp [hcc]

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

abbrev IsCOFEFun {α : Type _} (β : α → Type _) [OFEFun β] := ∀ x : α, IsCOFE (β x)

instance {α : Type _} (β : α → Type _) [∀ x, COFE (β x)] : COFE ((x : α) → β x) where
  compl c x := compl (c.map (applyHom x))
  conv_compl _ := IsCOFE.conv_compl

abbrev OFunctorPre := ∀ α β [OFE α] [OFE β], Type _

class OFunctor (F : OFunctorPre) where
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

class OFunctorContractive (F : OFunctorPre) extends OFunctor F where
  map_contractive [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [instance] OFunctor.cofe

abbrev constOF (B : Type) : OFunctorPre := fun _ _ _ _ => B

instance oFunctorConstOF [OFE B] : OFunctor (constOF B) where
  cofe := _
  map _ _ := ⟨id, id_ne⟩
  map_ne := by intros; constructor; simp [NonExpansive₂]
  map_id := by simp
  map_comp := by simp

instance OFunctor.constOF_contractive [OFE B] : OFunctorContractive (constOF B) where
  map_contractive.1 := by simp [map]

end COFE

/- Leibniz OFE structure on a type -/
@[ext] structure LeibnizO (α : Type _) where
  car : α

-- Move?
theorem Eq_Equivalence {α : Type _} : Equivalence (@Eq α) :=
  ⟨congrFun rfl, (Eq.symm ·), (· ▸ ·)⟩

instance : COFE (LeibnizO α) := COFE.ofDiscrete _ Eq_Equivalence

instance : Leibniz (LeibnizO α) := ⟨(·)⟩

instance {α : Type _} : OFE.Discrete (LeibnizO α) := ⟨congrArg id⟩
instance {α : Type _} : OFE.Leibniz (LeibnizO α) := ⟨congrArg id⟩

theorem LeibnizO.eqv_inj {x y : α} (H : LeibnizO.mk x ≡ LeibnizO.mk y) : x = y :=
  show (LeibnizO.mk x).car = (LeibnizO.mk y).car from H ▸ rfl

theorem LeibnizO.dist_inj {x y : α} {n} (H : LeibnizO.mk x ≡{n}≡ LeibnizO.mk y) : x = y :=
  LeibnizO.eqv_inj <| discrete H

section DiscreteFunOF
open COFE

abbrev DiscreteFunOF {C : Type _} (F : C → OFunctorPre) : OFunctorPre :=
  fun A B _ _ => (c : C) → F c A B

instance oFunctor_discreteFunOF {C} (F : C → OFunctorPre) [∀ c, OFunctor (F c)] :
    OFunctor (DiscreteFunOF F) where
  cofe := _
  map f₁ f₂ := mapCodHom fun c => OFunctor.map f₁ f₂
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := by apply OFunctor.map_ne.ne Hx Hy
  map_id _ _ := by apply OFunctor.map_id
  map_comp _ _ _ _ _ _ := by apply OFunctor.map_comp

end DiscreteFunOF

section Option
variable [OFE α]

def optionChain (c : Chain (Option α)) (x : α) : Chain α := by
  refine ⟨fun n => (c n).getD x, fun {n i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist, Option.Forall₂]

instance isCOFE_option [IsCOFE α] : IsCOFE (Option α) where
  compl c := (c 0).map fun x => IsCOFE.compl (optionChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    rcases c.chain 0 with _|x' <;> rcases e : c.chain n with _|y' <;> simp [Dist, Option.Forall₂]
    refine fun _ => OFE.dist_eqv.trans IsCOFE.conv_compl ?_
    simp [optionChain, e]

def optionMap {α β : Type _} [OFE α] [OFE β] (f : α -n> β) : Option α -n> Option β := by
  refine ⟨Option.map f, ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all [Dist, Option.Forall₂]
  exact f.ne.ne H

end Option

section OptionOF
open COFE

abbrev OptionOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => Option (F A B)

variable (F : OFunctorPre)

instance oFunctorOption [OFunctor F] : OFunctor (OptionOF F) where
  cofe := _
  map f g := optionMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy z := by
    cases z <;> simp [optionMap, Dist, Option.Forall₂]
    apply OFunctor.map_ne.ne Hx Hy
  map_id z := by
    cases z <;> simp [optionMap, Dist, Equiv, Option.Forall₂]
    apply OFunctor.map_id
  map_comp _ _ _ _ z := by
    cases z <;> simp [optionMap, Dist, Equiv, Option.Forall₂]
    apply OFunctor.map_comp

instance [OFunctorContractive F] : OFunctorContractive (OptionOF F) where
  map_contractive.1 H z := by
    have := (OFunctorContractive.map_contractive (F := F)).distLater_dist H
    cases z <;> simp_all [optionMap, Dist, Equiv, Option.Forall₂, Function.uncurry, OFunctor.map]

end OptionOF

section Fixpoint

def LimitPreserving [COFE α] (P : α → Prop) : Prop :=
  ∀ (c : Chain α), (∀ n, P (c n)) → P (COFE.compl c)

theorem LimitPreserving.const [COFE α] {P : Prop} : LimitPreserving fun (_ : α) => P := by
  simp [LimitPreserving]

theorem LimitPreserving.discrete [COFE α] {P : α → Prop} :
    (∀ {x y : α}, x ≡{0}≡ y → (P x → P y)) → LimitPreserving P :=
  fun Hdisc _ H => Hdisc COFE.conv_compl.symm (H _)

theorem LimitPreserving.and [COFE α] {P Q : α → Prop}  (HP : LimitPreserving P)
    (HQ : LimitPreserving Q) : LimitPreserving fun a => P a ∧ Q a :=
  fun _ HPQ => ⟨HP _ (fun n => (HPQ n).left), HQ _ (fun n => (HPQ n).right)⟩

theorem LimitPreserving.forall [COFE α] (P : β → α → Prop) (Hlim : ∀ y, LimitPreserving (P y)) :
    LimitPreserving (∀ y, P y ·) :=
  fun c H y => Hlim y c (H · y)

theorem LimitPreserving.impl [COFE α] (P1 P2 : α → Prop)
    (HP1 : ∀ {x y : α}, x ≡{0}≡ y → P1 x → P1 y)
    (Hcompl : LimitPreserving P2) :
    LimitPreserving (fun x => P1 x → P2 x) :=
  fun _ Hc HP1c => Hcompl _ <| fun n => Hc _ (HP1 (COFE.conv_compl' (Nat.zero_le n)) HP1c)

theorem LimitPreserving.equiv [COFE α] [COFE β] (f g : α -n> β) :
    LimitPreserving (fun x => f x ≡ g x) := by
  intro c Hfg
  refine equiv_dist.mpr fun n => ?_
  apply (COFE.compl_map ..).symm.dist.trans
  apply (COFE.conv_compl' (Nat.le_refl n)).trans
  apply (Hfg _).dist.trans
  exact g.ne.ne COFE.conv_compl.symm

def Fixpoint.chain [OFE α] [Inhabited α] (f : α → α) [Contractive f] : Chain α where
  chain n := Nat.repeat f (n + 1) default
  cauchy {n} := by
    induction n with simp [Nat.repeat] | succ n IH
    rintro (_|i) <;> simp
    intro H
    apply Contractive.distLater_dist
    intro _ Hm
    exact (IH H).le (Nat.le_of_lt_succ Hm)

/-- Fixpoints inside of a COFE -/
def fixpoint [COFE α] [Inhabited α] (f : α → α) [Contractive f] : α :=
  COFE.compl <| Fixpoint.chain f

nonrec abbrev OFE.ContractiveHom.fixpoint [COFE α] [Inhabited α] (f : α -c> α) : α := fixpoint f.f

theorem fixpoint_unfold [COFE α] [Inhabited α] (f : α -c> α) :
    fixpoint f ≡ f (fixpoint f) := by
  refine equiv_dist.mpr fun n => ?_
  apply COFE.conv_compl.trans
  refine .trans ?_ (NonExpansive.ne COFE.conv_compl.symm)
  induction n with
  | zero => exact Contractive.zero f.f
  | succ _ IH => exact (Contractive.succ f.f IH.symm).symm

theorem fixpoint_unique [COFE α] [Inhabited α] {f : α -c> α} {x : α} (H : x ≡ f x) :
    x ≡ fixpoint f := by
  refine equiv_dist.mpr fun n => ?_
  induction n with refine H.dist.trans <| .trans ?_ (fixpoint_unfold f).dist.symm
  | zero => exact Contractive.zero f.f
  | succ _ IH => exact Contractive.succ f.f IH

instance OFE.ContractiveHom.fixpoint_ne [COFE α] [Inhabited α] :
    NonExpansive (ContractiveHom.fixpoint (α := α)) where
  ne n f1 f2 H := by
    apply COFE.conv_compl.trans
    refine .trans ?_ COFE.conv_compl.symm
    induction n with
    | zero => exact H _
    | succ _ IH => exact (H _).trans <| Contractive.succ _ <| IH <| Dist.lt H (Nat.lt_add_one _)

@[elab_as_elim]
theorem OFE.ContractiveHom.fixpoint_ind [COFE α] [Inhabited α] (f : α -c> α)
    (P : α → Prop) (HProper : ∀ A B : α, A ≡ B → P A → P B) (x : α) (Hbase : P x)
    (Hind : ∀ x, P x → P (f x)) (Hlim : LimitPreserving P) :
    P f.fixpoint := by
  let chain : Chain α := by
    refine ⟨fun i => Nat.repeat f (i + 1) x, fun {n i} H => ?_⟩
    induction n generalizing i with
    | zero => simp [Nat.repeat]
    | succ _ IH =>
      cases i <;> simp at H
      exact Contractive.succ _ <| IH H
  refine HProper _ _ (fixpoint_unique (x := COFE.compl chain) ?_) ?_
  · refine equiv_dist.mpr fun n => ?_
    apply COFE.conv_compl.trans
    refine .trans ?_ (f.ne.ne COFE.conv_compl).symm
    induction n
    · exact Contractive.zero f.f
    · rename_i IH; apply Contractive.succ _ IH
  · apply Hlim; intro n
    induction n with
    | zero => exact Hind (Nat.repeat f.f 0 x) Hbase
    | succ _ IH => apply Hind (Nat.repeat f.f _ x) IH

end Fixpoint

section Later

structure Later (A : Type u) : Type (u+1) where
  next :: car : A

instance isOFE_later [OFE A] : OFE (Later A) where
  Equiv x y := x.car ≡ y.car
  Dist n x y := DistLater n x.car y.car
  dist_eqv := ⟨fun _ => .rfl, .symm, .trans⟩
  equiv_dist := by
    simp only [equiv_dist, DistLater]
    exact ⟨by simp +contextual, fun H n => H (Nat.succ n) n (by simp)⟩
  dist_lt Hxy Hmn _ Hkm := Hxy _ (Nat.lt_trans Hkm Hmn)

instance NextContractive {A : Type} [OFE A] : Contractive (@Later.next A) where
  distLater_dist := id

def laterChain [OFE A] (c : Chain (Later A)) : Chain A where
  chain n := (c (Nat.succ n)).car
  cauchy Hle := c.cauchy (Nat.succ_le_succ Hle) _ (Nat.lt_succ_self _)

instance isCOFE_later [OFE A] [IsCOFE A] : IsCOFE (Later A) where
  compl c := Later.next (IsCOFE.compl (laterChain c))
  conv_compl {n} c := by
    rcases n with _|n' <;> simp [Dist, DistLater]
    intros m Hlt
    exact (IsCOFE.conv_compl (n := n') (c := laterChain c)).le (Nat.le_of_lt_succ Hlt)

def laterMap [OFE A] [OFE B] (f : A -n> B)  : Later A -n> Later B := by
  refine ⟨fun x => Later.next (f x.car), ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all only [Dist, DistLater]
  intros m Hlt; exact f.ne.ne (H m Hlt)

end Later

section LaterOF
open COFE

abbrev LaterOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => Later (F A B)

variable (F : OFunctorPre)

instance oFunctorLater [OFunctor F] : OFunctor (LaterOF F) where
  cofe := _
  map f g := laterMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := (OFunctor.map_ne.ne Hx Hy _).lt
  map_id _ := OFunctor.map_id _
  map_comp _ _ _ _ _ := OFunctor.map_comp ..

instance [OFunctorContractive F] : OFunctorContractive (LaterOF F) where
  map_contractive.1 H z m := Dist.lt <| by
    have := (OFunctorContractive.map_contractive (F := F)).distLater_dist H
    simp_all only [Dist, DistLater, Function.uncurry, OFunctor.map, laterMap]

end LaterOF

section subtype

instance [OFE α] {P : α → Prop} : OFE { x : α // P x } where
  Equiv := (·.val ≡ ·.val)
  Dist n := (·.val ≡{n}≡ ·.val)
  dist_eqv := {
    refl x := dist_eqv.refl x.val
    symm H := H.symm
    trans H1 H2 := H1.trans H2
  }
  equiv_dist := equiv_dist
  dist_lt := dist_lt

end subtype
