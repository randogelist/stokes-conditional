# Integration proof repairs

## Force-exponent disjointness

Source: `NSEForcingRegularityClasses.lean`, originating in
`NSE_FORCING_REGULARITY_CLASSES_LEAN_v0_1_4`.

Declaration: `REGULAR_AND_IRREGULAR_FORCE_CLASSES_DISJOINT`.

The first Linux CI build exposed a proof failure: after unfolding the exponent
classes, `linarith` had no hypotheses because the goal was still a negation.
The repaired proof introduces the conjunction and applies `not_lt_of_ge` to
the incompatible bounds. Its theorem statement and definitions are unchanged.

```lean
  simp only [L2CriticalRegularExponent, L2IrregularButLHExponent]
  rintro ⟨hregular, _, hrough⟩
  exact (not_lt_of_ge hregular) hrough
```

The original archive remains byte-identical. `active_source_origins.json`
records both SHA-256 values and the complete old/new text. Verification checks
each original member's hash, requires the old text to occur exactly once,
replays the edit, and compares the reconstructed bytes with the active file.
The other 58 active modules retain their original bytes.

This repair does not assert a physical Navier–Stokes regularity result.
