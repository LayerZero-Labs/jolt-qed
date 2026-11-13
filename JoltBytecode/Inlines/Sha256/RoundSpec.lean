import JoltBytecode.Inlines.Sha256.Spec

/-!
# SHA-256 rounds over a 16-word window

`Spec.rounds` reads the message schedule word `w[n]` of round `n` through the recurrence
`Spec.messageWord`. Jolt's rows instead keep a window of 16 words and, from round 16 on,
overwrite word `n mod 16` with `w[n]` before round `n` uses it. `roundsR` is that form of the
rounds, and `roundsR_eq` proves it equal to `Spec.rounds`: after `n` rounds, the window holds
the last 16 schedule words computed (`window`).
-/

set_option autoImplicit false

namespace JoltSpec.Sha256.Spec

/-- Working variable `c` of a state (`a = 0`, ..., `h = 7`).
Example: `State.get s 4 = s.e`. -/
def State.get (s : State) : Nat → Word
  | 0 => s.a
  | 1 => s.b
  | 2 => s.c
  | 3 => s.d
  | 4 => s.e
  | 5 => s.f
  | 6 => s.g
  | _ => s.h

/-- A round shifts the working variables other than `a` and `e`.
Example: `(step s k w).get 5 = s.get 4`. -/
theorem step_get (s : State) (k w : Word) (c : Nat) (hc : c < 8) (h0 : c ≠ 0) (h4 : c ≠ 4) :
    (step s k w).get c = s.get (c - 1) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | c <;> first | omega | rfl

/-- The schedule index held in window slot `k < 16` at the start of round `n`: the last index
`t ≡ k (mod 16)` below `n`, or `k` itself while `n ≤ 16`.
Example: `windowIndex 20 3 = 19` and `windowIndex 20 5 = 5`. -/
def windowIndex (n k : Nat) : Nat := k + 16 * ((n - 1 - k) / 16)

/-- The window at the start of round `n`, indexed mod 16.
Example: `window input 0 j = input[j % 16]`. -/
def window (input : Vector Word 16) (n : Nat) (j : Nat) : Word :=
  messageWord input (windowIndex n (j % 16))

/-- The schedule update of round `n ≥ 16`: slot `n mod 16` gets
`w[n - 16] + σ0(w[n - 15]) + w[n - 7] + σ1(w[n - 2])`, read from the window.
Example: `windowStep 16 w 0 = w 16 + small0 (w 17) + w 25 + small1 (w 30)`. -/
def windowStep (n : Nat) (w : Nat → Word) (j : Nat) : Word :=
  if j % 16 = n % 16 then w n + small0 (w (n + 1)) + w (n + 9) + small1 (w (n + 14)) else w j

/-- One round over a state and a window: update the window from round 16 on, then run `step`
with the window word of round `n`.
Example: `(roundR 0 (s, w)).1 = step s (K[0]!).toBitVec (w 0)`. -/
def roundR (n : Nat) (p : State × (Nat → Word)) : State × (Nat → Word) :=
  let w' := if 16 ≤ n then windowStep n p.2 else p.2
  (step p.1 (K[n]!).toBitVec (w' n), w')

/-- The first `n` rounds over a state and a window, from the block words as the window.
Example: `roundsR input s 0 = (s, fun j => input[j % 16])`. -/
def roundsR (input : Vector Word 16) (initial : State) : Nat → State × (Nat → Word)
  | 0 => (initial, fun j => input[j % 16])
  | n + 1 => roundR n (roundsR input initial n)

/-- The schedule below 16 is the block. -/
theorem messageWord_of_lt (input : Vector Word 16) (t : Nat) (h : t < 16) :
    messageWord input t = input[t] := by
  rw [messageWord]
  simp only [h, ↓reduceDIte]

/-- The schedule from 16 on is the recurrence. -/
theorem messageWord_of_ge (input : Vector Word 16) (t : Nat) (h : 16 ≤ t) :
    messageWord input t = messageWord input (t - 16) + small0 (messageWord input (t - 15)) +
      messageWord input (t - 7) + small1 (messageWord input (t - 2)) := by
  rw [messageWord]
  simp only [show ¬ t < 16 by omega, ↓reduceDIte]

/-- Window slot `n + k` at round `n ≥ 16` holds `w[n - 16 + k]`. -/
private theorem window_ahead (input : Vector Word 16) (n k : Nat) (hn : 16 ≤ n) (hk : k < 16) :
    window input n (n + k) = messageWord input (n - 16 + k) := by
  unfold window windowIndex
  congr 1
  omega

/-- **The window form of the rounds is the reference.** After `n` rounds the state is
`Spec.rounds` and the window holds the last 16 schedule words.
Example: for `n = 0` both sides are the initial state and the block. -/
theorem roundsR_eq (input : Vector Word 16) (initial : State) (n : Nat) :
    roundsR input initial n = (rounds input initial n, window input n) := by
  induction n with
  | zero =>
    refine Prod.ext rfl (funext fun j => ?_)
    show input[j % 16] = messageWord input (windowIndex 0 (j % 16))
    have : windowIndex 0 (j % 16) = j % 16 := by unfold windowIndex; omega
    rw [this, messageWord_of_lt _ _ (by omega)]
  | succ n ih =>
    simp only [roundsR, ih, roundR, rounds]
    by_cases hn : 16 ≤ n
    · simp only [hn, ↓reduceIte]
      have hw : windowStep n (window input n) n = messageWord input n := by
        simp only [windowStep, ↓reduceIte]
        rw [show window input n n = window input n (n + 0) from rfl,
          window_ahead _ _ _ hn (by decide), window_ahead _ _ _ hn (by decide),
          window_ahead _ _ _ hn (by decide), window_ahead _ _ _ hn (by decide),
          messageWord_of_ge _ _ hn, show n - 16 + 0 = n - 16 by omega,
          show n - 16 + 1 = n - 15 by omega, show n - 16 + 9 = n - 7 by omega,
          show n - 16 + 14 = n - 2 by omega]
      refine Prod.ext (by rw [hw]) (funext fun j => ?_)
      show windowStep n (window input n) j = window input (n + 1) j
      by_cases hj : j % 16 = n % 16
      · have : window input (n + 1) j = messageWord input n := by
          unfold window windowIndex; congr 1; omega
        rw [this, ← hw]
        simp only [windowStep, hj, ↓reduceIte]
      · simp only [windowStep, hj, ↓reduceIte]
        unfold window windowIndex
        congr 1
        omega
    · simp only [hn, ↓reduceIte]
      have hw : window input n n = messageWord input n := by
        unfold window windowIndex; congr 1; omega
      refine Prod.ext (by rw [hw]) (funext fun j => ?_)
      show window input n j = window input (n + 1) j
      unfold window
      rw [show windowIndex (n + 1) (j % 16) = windowIndex n (j % 16) by
        unfold windowIndex; omega]

end JoltSpec.Sha256.Spec
