/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.uPred

import Init.Data.Vector

namespace Iris

structure gFunctor : Type _ where
  F : Type _ -> Type _ -> Type _
  functor : RFunctorContractive F

attribute [instance] gFunctor.functor

def gFunctor.ap (F : gFunctor) (A : Type _) [COFE A] : Type _ := F.F A A


-- gFunctors: thin wrapper around Array to make working with it less painful

abbrev gFunctors : Type _ := Array gFunctor

abbrev gFunctors.len (FF : gFunctors) := FF.size

abbrev gid (FF : gFunctors) : Type _ := Fin (FF.len)

def gFunctors.lookup (FF : gFunctors) (n : gid FF) : gFunctor := FF[n]

-- Why does Iris use positive here?
abbrev gname :=  { n : Nat // 0 < n }
def gnameO := LeibnizO gname

def gFunctors.nil : gFunctors := #[]

def gFunctors.singleton (F : gFunctor) : gFunctors := #[F]

def gFunctors.app (FF₁ FF₂ : gFunctors) := FF₁ ++ FF₂

class subG (FF₁ FF₂ : gFunctors) : Prop where
  in_subG : ∀ i : gid FF₁, ∃ j : gid FF₂, FF₁.lookup i = FF₂.lookup j

theorem subG_split_L (FF₁ FF₂ FF₃ : gFunctors) (H : subG (FF₁.app FF₂) FF₃) : (subG FF₁ FF₃) := sorry

theorem subG_comm (FF₁ FF₂ FF₃ : gFunctors) (H : subG (FF₁.app FF₂) FF₃) : subG (FF₂.app FF₁) FF₃ := sorry

theorem subG_split_R (FF₁ FF₂ FF₃ : gFunctors) (H : subG (FF₁.app FF₂) FF₃) : (subG FF₁ FF₃) := sorry

theorem subG_refl (FF : gFunctors) : subG FF FF := sorry

theorem subG_aop_R (FF₁ FF₂ FF₃ : gFunctors) (H : subG FF₁ FF₂) : (subG FF₁ (FF₂.app FF₃)) := sorry


-- TODO: Using this instaed of gmap, find the right type
section gen_map

structure gen_map (K V : Type _) : Type _ where
  m : K → V

instance [CMRA V] : UCMRA (gen_map K V) := sorry

end gen_map



section iProp

variable (iPrePropO : gFunctors -> Type _)
variable [∀ g, COFE (iPrePropO g)]

def iResUR (FF : gFunctors) : Type _ :=
  @discrete_funU (gid FF) (fun i => gen_map gname ((FF.lookup i).ap (iPrePropO FF)))

-- variable (FF0 : gFunctors)
-- #check iResUR iPrePropO FF0
-- #synth UCMRA (iResUR iPrePropO FF0)

instance (FF : gFunctors) : UCMRA (iResUR iPrePropO FF) := by
  -- FIXME why doesn't this synth?
  apply discrete_funU_ucmra


-- Need uPred oFunctor to finish definintion of iProp


end iProp

end Iris
