import Karatsuba.Basic

open IO

namespace Bench

def mkNumberWithDigits (digits : Nat) : Nat :=
  10 ^ digits - 1

def usage : String :=
  "Usage: lake exe bench <digits> [digits2]\n" ++
  "  - If [digits2] is omitted, both numbers use <digits>.\n" ++
  "  - digits must be positive natural numbers."

@[noinline]
def force {α} (a : α) : IO α := pure a

def benchmarkOne (f : Nat → Nat → Nat) (x y : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoMsNow
  let result ← force <| f x y
  let stop ← IO.monoMsNow
  pure (result, stop - start)

end Bench

open Bench

def main (args : List String) : IO UInt32 := do
  let (d1, d2) ←
    match args with
    | [a] =>
      match a.toNat? with
      | some n => pure (n, n)
      | none =>
        IO.eprintln usage
        return 1
    | [a, b] =>
      match a.toNat?, b.toNat? with
      | some n1, some n2 => pure (n1, n2)
      | _, _ =>
        IO.eprintln usage
        return 1
    | _ =>
      IO.eprintln usage
      return 1
  let x := mkNumberWithDigits d1
  let y := mkNumberWithDigits d2
  let b : Base := ⟨10, by decide⟩
  IO.println s!"Benchmarking with x digits={d1}, y digits={d2}"
  let (kRes, kMs) ← benchmarkOne (karatsuba (b := b)) x y
  IO.println s!"karatsuba:    {kMs} ms"
  let (pRes, pMs) ← benchmarkOne (· * ·) x y
  IO.println s!"baseline: {pMs} ms"
  pure 0
