/-
# Logic.Function.Basic - Stub

函数基础理论
-/

import FormalMath.MathlibStub

namespace Function

/-- A function is surjective if every element in the codomain is the image of some element in the domain. -/
def Surjective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

/-- A function is injective if it maps distinct elements to distinct elements. -/
def Injective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂

end Function
