#!/usr/bin/env python3
"""Find and emit the gate-elimination certificate for L-meta-982 shard 2.

This program handles the assigned third conjunct only. Its truth-table dynamic
program is proof discovery; the emitted Lean theorem is the soundness check.
The only leaf used in the resulting certificate is the majority-of-three
lower bound, independently established by kernel-reduced exhaustive search.
All one-/two-gate elimination steps are proved from the project circuit model.
"""
from __future__ import annotations

import argparse
import functools
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
N = 7
EDGES = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]
ROWS = 1 << N
MASK = (1 << ROWS) - 1


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def graph_table():
    return sum(int(any((x >> u) & (x >> v) & 1 for u, v in EDGES)) << x
               for x in range(ROWS))


def restrict(table, var, val):
    return sum(((table >> ((x & ~(1 << var)) | (val << var))) & 1) << x
               for x in range(ROWS))


def support(table):
    return [i for i in range(N) if restrict(table, i, 0) != restrict(table, i, 1)]


def nonconstant(table):
    return table not in (0, MASK)


def majority_table(indices):
    return sum(int(sum((x >> i) & 1 for i in indices) >= 2) << x
               for x in range(ROWS))


trace = {}


@functools.lru_cache(None)
def derive(table):
    variables = support(table)
    best, why = 0, ['trivial']
    if len(variables) == 3 and table == majority_table(variables):
        best, why = 4, ['majority3', variables]
    for i in variables:
        ts = [restrict(table, i, b) for b in range(2)]
        bs = [derive(t) for t in ts]
        for b in range(2):
            if nonconstant(ts[b]) and 1 + bs[b] > best:
                best, why = 1 + bs[b], ['one', i, b, str(ts[b])]
        if all(map(nonconstant, ts)) and 2 + min(bs) > best:
            best, why = 2 + min(bs), ['two', i, str(ts[0]), str(ts[1])]
    trace[str(table)] = {'lower': best, 'why': why, 'support': variables}
    return best


def dependency_witness(table, var):
    a, b = restrict(table, var, 0), restrict(table, var, 1)
    return next(x for x in range(ROWS) if ((a ^ b) >> x) & 1)


def nonconstant_witness(table):
    return (next(x for x in range(ROWS) if not ((table >> x) & 1)),
            next(x for x in range(ROWS) if (table >> x) & 1))


def proof_dep(table, var):
    return f'by exact ⟨point {dependency_witness(table, var)}, by decide⟩'


def proof_nc(table):
    x, y = nonconstant_witness(table)
    return f'by exact ⟨point {x}, point {y}, by decide⟩'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=ROOT / 'pequalnp-proofs',
                        help='Checkout containing the pinned upstream proof sources')
    parser.add_argument('--task', type=Path, default=HERE / 'assigned_task.json',
                        help='Public desk task record, with no lease required')
    parser.add_argument('--lean-output', type=Path,
                        help='Output Lean file; defaults to the repository shard module')
    parser.add_argument('--artifacts', type=Path, default=HERE,
                        help='Directory for the trace and manifest')
    args = parser.parse_args()
    repo = args.repo.resolve()
    target = (args.lean_output.resolve() if args.lean_output else
              repo / 'lean/PEqualNP/Outside/L_meta_982_shard2.lean')
    artifacts = args.artifacts.resolve()
    artifacts.mkdir(parents=True, exist_ok=True)
    target.parent.mkdir(parents=True, exist_ok=True)
    desk = json.loads(args.task.read_text())
    assert desk['gap']['id'] == 'L-meta-982'
    assert (desk['shard'], desk['shards']) == (2, 31)
    conjunct = desk['gap']['statement'].split(') ∧ (')[2]
    assert 'HasCircuitSize 7' in conjunct and '→ 10 ≤ t' in conjunct
    table = graph_table()
    lower = derive(table)
    assert lower == 10
    reachable = set()
    def walk(t):
        if t in reachable:
            return
        reachable.add(t)
        why = trace[t]['why']
        if why[0] == 'one':
            walk(why[3])
        if why[0] == 'two':
            walk(why[2]); walk(why[3])
    walk(str(table))
    assert len(reachable) == 7
    assert all(trace[t]['why'][0] != 'trivial' for t in reachable)
    full_trace = {'gap': 'L-meta-982', 'shard': 2, 'shards': 31,
                  'n': N, 'edges': EDGES, 'table': str(table), 'lower': lower,
                  'visited_states': len(trace),
                  'certificate_nodes': {t: trace[t] for t in sorted(reachable)},
                  'trace': trace}
    trace_path = artifacts / 'gate_elimination_certificate.json'
    trace_path.write_text(json.dumps(full_trace, indent=2) + '\n')

    # The private elimination library is copied from the upstream verified file;
    # its unrelated prefix-hardwiring theorem and all graph-specific material
    # are omitted. TableSearch is also copied, with its namespace relocated.
    source_elim = repo / 'lean/PEqualNP/Outside/L_meta_468.lean'
    source_search = repo / 'lean/PEqualNP/MetaComplexity/Helpers/TableSearch.lean'
    elim = source_elim.read_text().splitlines(keepends=True)
    elim = ''.join(elim[6:507] + elim[589:988])
    search = source_search.read_text()
    search = search[search.index('namespace PEqualNP.MetaComplexity.Helpers.TableSearch'):]
    search = search.replace('PEqualNP.MetaComplexity.Helpers.TableSearch', 'TableSearch')
    parts = ['import PEqualNP.Defs\n\n',
             '/-! Local certificate for L-meta-982, shard 2 of 31. Signature: cyjin.\n',
             'This file proves the exact third conjunct only. The remaining thirty\n',
             'conjuncts are outside this certificate. Helper proofs are copied from\n',
             'upstream L_meta_468 and MetaComplexity/Helpers/TableSearch. -/\n\n',
             'namespace PEqualNP.Outside.L_meta_982_shard2_aux\n\n',
             'open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\n\n',
             elim, '\n', search, '\n',
             'private def point (r : ℕ) : Fin 7 → Bool := fun i => r.testBit i.val\n\n']

    # Keep concrete functions small, so finite side conditions are transparent
    # kernel reductions rather than a new trusted truth-table interpreter.
    maj = '(x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)'
    expressions = {
        0: ' || '.join(f'(x {u} && x {v})' for u, v in EDGES),
        1: f'{maj} || (x 0 && x 3) || (x 0 && x 4) || (x 4 && x 6)',
        2: f'{maj} || x 3 || (x 0 && x 4) || (x 4 && x 6)',
        3: f'{maj} || (x 0 && x 4) || (x 4 && x 6)',
        4: f'{maj} || (x 0 && x 4)',
        5: f'{maj} || x 4',
        6: maj,
    }
    tables = {0: table}
    tables[1], tables[2] = [restrict(table, 5, b) for b in range(2)]
    tables[3] = restrict(tables[1], 3, 0)
    assert tables[3] == restrict(tables[2], 3, 0)
    tables[4], tables[5] = [restrict(tables[3], 6, b) for b in range(2)]
    tables[6] = restrict(tables[4], 4, 0)
    assert tables[6] == restrict(tables[5], 4, 0) == majority_table([0, 1, 2])
    assert set(map(str, tables.values())) == reachable
    for i, expression in expressions.items():
        parts.append(f'private def f{i} (x : Fin 7 → Bool) : Bool := {expression}\n\n')

    parts.append('''private lemma majority_search :
    TableSearch.reach (2 ^ 8 - 1) (fun t => t % 2 ^ 8 == 232) 3
      [170, 204, 240, 0, 0, 0, 0] = false := by
  decide +kernel

private lemma lower_f6 {s : ℕ} (h : HasCircuitSize 7 f6 s) : 4 ≤ s := by
  have no_three : ¬ HasCircuitSize 7 f6 3 := by
    apply TableSearch.lower_of_search 7 8 f6 [170, 204, 240, 0, 0, 0, 0]
      232 3 (by norm_num) _ majority_search
    have key : ∀ p, p < 8 →
        (List.ofFn (point p)) = [170, 204, 240, 0, 0, 0, 0].map
          (fun t : ℕ => t.testBit p) ∧ f6 (point p) = Nat.testBit 232 p := by decide
    exact fun p hp => ⟨point p, key p hp⟩
  by_contra hs
  apply no_three
  obtain ⟨C, hok, hsz, hev⟩ := h
  exact ⟨C, hok, by omega, hev⟩

''')

    for i, var, child, bound in [(4, 4, 6, 5), (5, 4, 6, 5)]:
        parts.append(f'''set_option maxRecDepth 4096 in
private lemma lower_f{i} {{s : ℕ}} (h : HasCircuitSize 7 f{i} s) : {bound} ≤ s := by
  obtain ⟨hs, hc⟩ := elim_one_var ({var} : Fin 7) false h
    ({proof_dep(tables[i], var)})
    ({proof_nc(restrict(tables[i], var, 0))})
  have he : (fun x => f{i} (Function.update x {var} false)) = f{child} := by decide
  rw [he] at hc
  have hb := lower_f{child} hc
  omega

''')
    def two_step(i, var, child0, child1, bound):
        return f'''set_option maxRecDepth 4096 in
private lemma lower_f{i} {{s : ℕ}} (h : HasCircuitSize 7 f{i} s) : {bound} ≤ s := by
  obtain ⟨hs, hc⟩ := elim_two_var ({var} : Fin 7) h
    ({proof_dep(tables[i], var)})
    ({proof_nc(restrict(tables[i], var, 0))})
    ({proof_nc(restrict(tables[i], var, 1))})
  have he0 : (fun x => f{i} (Function.update x {var} false)) = f{child0} := by decide
  have he1 : (fun x => f{i} (Function.update x {var} true)) = f{child1} := by decide
  rcases hc with hc | hc
  · rw [he0] at hc
    have hb := lower_f{child0} hc
    omega
  · rw [he1] at hc
    have hb := lower_f{child1} hc
    omega

'''
    parts.append(two_step(3, 6, 4, 5, 7))
    for i in [1, 2]:
        parts.append(f'''set_option maxRecDepth 4096 in
private lemma lower_f{i} {{s : ℕ}} (h : HasCircuitSize 7 f{i} s) : 8 ≤ s := by
  obtain ⟨hs, hc⟩ := elim_one_var (3 : Fin 7) false h
    ({proof_dep(tables[i], 3)})
    ({proof_nc(tables[3])})
  have he : (fun x => f{i} (Function.update x 3 false)) = f3 := by decide
  rw [he] at hc
  have hb := lower_f3 hc
  omega

''')
    parts.append(two_step(0, 5, 1, 2, 10))
    parts.append('end PEqualNP.Outside.L_meta_982_shard2_aux\n\n')
    parts.append('theorem PEqualNP.Outside.L_meta_982_shard2 :\n    ' + conjunct + ' := by\n')
    parts.append('  intro t h\n  exact PEqualNP.Outside.L_meta_982_shard2_aux.lower_f0 h\n')
    target.write_text(''.join(parts))
    manifest = {'gap': 'L-meta-982', 'shard': 2, 'shards': 31,
                'claim': 'Exact third conjunct only; Lean checking is required.',
                'derived_lower_bound': lower, 'visited_states': len(trace),
                'certificate_nodes': len(reachable),
                'program_sha256': sha(__file__),
                'trace_sha256': sha(trace_path),
                'lean_sha256': sha(target),
                'upstream_sources': {str(p.relative_to(repo)): sha(p)
                                     for p in [source_elim, source_search]}}
    (artifacts / 'certificate_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    main()
