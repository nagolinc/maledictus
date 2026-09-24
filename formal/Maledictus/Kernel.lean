namespace Maledictus

inductive ExitEffect where
  | returned : String → ExitEffect
  | raised : String → ExitEffect
  | unknown : String → ExitEffect
deriving DecidableEq

def effectAllowed (allowed : List String) : ExitEffect → Bool
  | .returned _ => true
  | .raised exceptionType => allowed.contains exceptionType
  | .unknown _ => false

def checkExitEffects (effects : List ExitEffect) (allowed : List String) : Bool :=
  !effects.isEmpty && effects.all (effectAllowed allowed)

theorem accepted_effect_is_allowed
    (effects : List ExitEffect)
    (allowed : List String)
    (accepted : checkExitEffects effects allowed = true)
    (effect : ExitEffect)
    (member : effect ∈ effects) :
    effectAllowed allowed effect = true := by
  simp [checkExitEffects] at accepted
  exact accepted.2 effect member

theorem accepted_graph_is_nonempty
    (effects : List ExitEffect)
    (allowed : List String)
    (accepted : checkExitEffects effects allowed = true) :
    effects ≠ [] := by
  simp [checkExitEffects] at accepted
  exact accepted.1

end Maledictus
