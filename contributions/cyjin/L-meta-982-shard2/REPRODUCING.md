# L-meta-982: certificate for shard 2 of 31

Signature: **cyjin**.

The certificate addresses only the third conjunct: the edge function of the
seven-vertex graph with edges `01, 02, 03, 04, 12, 35, 46` requires at least ten
AND/OR/NOT gates of fan-in at most two. It makes no claim about the other thirty
conjuncts or P versus NP in general.

**Verified:** on 2026-11-23 UTC, the project's `check-lean.mjs` checker returned
exit status 0 and `ACCEPTED (check)` for
`PEqualNP.Outside.L_meta_982_shard2`. It rechecked 1,350 constants in the Lean
kernel and reported only the allowed axioms `propext`, `Quot.sound`, and
`Classical.choice`. This acceptance covers the exact third conjunct. The
separately preserved checker log is the acceptance receipt; this certificate
does not record an upstream PR or acceptance of all 31 conjuncts.

## Files and scope

- `generate_certificate.py` discovers the restriction proof and writes the Lean
  certificate. Its SHA-256 is recorded in `certificate_manifest.json`.
- `gate_elimination_certificate.json` records all 189 visited restricted truth
  tables, with the seven proof nodes actually used by the certificate.
- `lean/PEqualNP/Outside/L_meta_982_shard2.lean`, relative to the repository root,
  is the canonical certificate module and imports `PEqualNP.Defs`.
  The authoritative theorem name is
  `PEqualNP.Outside.L_meta_982_shard2`.
- `assigned_task.json` preserves the public desk task record with the private
  lease removed. Its third conjunct is the exact theorem statement.
- The separate local SAT experiments returned **UNKNOWN** on their time limits.
  They are not part of the mathematical certificate and do not establish
  UNSAT; see the experiment notes below.

The acceptance status is supported by the preserved checker log. The Python
trace and static audit are supporting reproducibility materials.

## Proof structure

Start with the majority function on inputs 0, 1, and 2, whose lower bound is four
gates. Its no-three-gate result follows from the upstream finite truth-table
search, evaluated using `decide +kernel`. The proof samples the eight rows where
inputs 3 through 6 are false; every circuit for the seven-input function must
satisfy those rows as well.

The restriction tree then establishes successive bounds:

| Function stage | Operation used to obtain the smaller function | Bound |
|---|---|---:|
| Majority of inputs 0, 1, 2 | Exhaustive search through three gates | 4 |
| The two restrictions at input 6 | Set input 4 to false; save one gate | 5 |
| The common restriction at input 3 | Restrict input 6; save two gates in one branch | 7 |
| The two restrictions at input 5 | Set input 3 to false; save one gate | 8 |
| The assigned edge function | Restrict input 5; save two gates in one branch | 10 |

The one- and two-gate elimination lemmas cover the exact project model,
including zero-input and unary gates, repeated inputs, NOT gates, input outputs,
and missing or forward references evaluating to false. The certificate retains
their proofs rather than assuming these rules as axioms.

## Sources and environment

The only copied proof bodies are:

1. `lean/PEqualNP/Outside/L_meta_468.lean`, lines 7–507 and 590–988, the generic
   circuit simplification and elimination machinery. The unrelated hardwiring
   and graph arguments are omitted.
2. `lean/PEqualNP/MetaComplexity/Helpers/TableSearch.lean`, its complete namespace
   body, relocated under the certificate's own auxiliary namespace.

Source-file hashes are recorded in `certificate_manifest.json`. The project
pins Lean `v4.36.0` and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

The generator uses only Python's standard library. Pass the upstream checkout
and the sanitized task record explicitly; it needs no private lease or account
credentials. From this directory:

```bash
python3 generate_certificate.py --repo /path/to/pequalnp-proofs \
  --task assigned_task.json --artifacts .
```

By default it writes the module inside that checkout. Use
`--lean-output /path/to/output.lean` to write elsewhere. The `--artifacts`
directory receives the trace and manifest. The portable generator reproduces
the canonical module deterministically. The current program, trace, module,
and source-proof hashes are recorded in `certificate_manifest.json`.

From `pequalnp-proofs/lean`, build the specified project imports and check the
exact certificate:

```bash
lake build PEqualNP.Defs
lake env lean PEqualNP/Outside/L_meta_982_shard2.lean
```

The project's authoritative checker additionally rechecks the theorem and its
project dependencies, rejects disallowed axioms, and compares the theorem
against the recorded statement. Extract the third conjunct from the sanitized
task, then run the checker from the repository root:

```bash
cd /path/to/pequalnp-proofs
PNP_CERT_DIR=/path/to/meta982-shard2
python3 - "$PNP_CERT_DIR/assigned_task.json" "$PNP_CERT_DIR/statement.lean" <<'PY'
import json
from pathlib import Path
import sys

task = json.loads(Path(sys.argv[1]).read_text())
assert task['gap']['id'] == 'L-meta-982'
assert (task['shard'], task['shards']) == (2, 31)
conjuncts = task['gap']['statement'].split(') ∧ (')
assert len(conjuncts) == 31
Path(sys.argv[2]).write_text(conjuncts[2] + '\n')
PY
node tools/check-lean.mjs \
  lean/PEqualNP/Outside/L_meta_982_shard2.lean \
  "$PNP_CERT_DIR/statement.lean" check
```

The checker accepts only on exit status 0 and prints an acceptance receipt and
dependency manifest. The preserved receipt records this successful check of
the exact third-conjunct statement.

Temporary local development files are excluded from the minimal certificate
bundle. Some development checks used the narrower import
`PEqualNP.Defs.MetaComplexity`; those checks do not replace the final check of
the full-import candidate.

## Independent audit

A separate read-only audit confirmed the exact third-conjunct statement,
helper-source equality, all eight restriction identities on all 128 inputs,
all six dependency witnesses, all eight nonconstancy witness pairs, and the
bound arithmetic. It found no `sorry`, new axiom, `native_decide`, or unsafe
shortcut. The audit complements rather than replaces Lean kernel checking.

The eight finite restriction equalities were also checked separately by Lean
with the same `maxRecDepth 4096` options used by the candidate. That check
returned exit status 0 in 16.39 seconds. The increased recursion limit changes
an elaboration resource limit only; it adds no logical assumption.

## SAT attempts

The SAT encoding is complete for circuits of at most nine gates: it normalizes
missing wires to false, includes all three gate operations, permits repeated
operands and constant-valued gates, prunes gates outside the output cone, and
pads with identity AND gates. Its normal-form restrictions are documented in
the program. Independent validation compared 312 small truth-table/budget
instances against direct enumeration and independently replayed a ten-gate
upper-bound circuit on all 128 target inputs.

The recorded local runs were CaDiCaL 1.9.5 with 120-second and 300-second limits.
Neither completed, so both statuses remain UNKNOWN. The gate-elimination Lean
certificate is a separate proof route and does not relabel either SAT timeout
as an UNSAT result.
