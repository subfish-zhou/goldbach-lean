#!/usr/bin/env python3
"""Stage the max of two lower bounds; check one strict witness per row.

No Lean process or canonical source write is performed. Numeric formulas,
parameters and precision are retained. The isolated candidate needs compilation.
"""

import argparse
import difflib
import importlib.util
import json
import re
from pathlib import Path

from audit_completed_batch import sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    run, output = args.run.resolve(), args.output_dir.resolve()
    assert not output.exists()
    repo = Path(__file__).resolve().parents[2]
    manifest = {r['module']: r for r in json.loads((run / 'source-manifest.json').read_text())}
    source = run / 'src'
    originals, changes = {}, {}

    def read(name):
        path = source / (name + '.lean')
        assert sha(path) == manifest[name]['source_sha256']
        text = path.read_text()
        originals[name] = text
        return text

    text = read('W08KernelMatrix')
    marker = 'theorem paidCells_le_kernel'
    helper = '''/-- Both terms bound the same E-kernel cell. Their maximum is one bound. -/
abbrev cellEnvelope (S a b : ℝ) : ℝ :=
  max (Wu04Bypass.cell S a b) (RemainingHf.paidCell S a b)

def envelopeCells (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9, z k * cellEnvelope S (cellLeft (S - 2) k) (upperNode k)

theorem cellEnvelope_paid {S a b : ℝ} (hS : 3 ≤ S)
    (ha : S - 2 ≤ a) (hab : a ≤ b) :
    cellEnvelope S a b ≤ ∫ t in a..b, log ((t + 1) / (S - 1)) / t :=
  max_le (Wu04Bypass.cell_le_integral hS ha hab)
    (RemainingHf.paidCell_paid hS ha hab)

'''
    assert text.count(marker) == 1
    text = text.replace(marker, helper + marker, 1)
    # Replace consumers, preserving the original formulas in the helper itself.
    before, body = text.split(marker, 1)
    body = re.sub(r'\bRemainingHf\.paidCells\b', 'envelopeCells', body)
    body = re.sub(r'\bRemainingHf\.paidCell\b', 'cellEnvelope', body)
    body = body.replace('RemainingHf.paidCell_paid', 'cellEnvelope_paid')
    old = '''  exact (le_add_of_nonneg_left (mul_nonneg hp hl)).trans
    (RemainingHf.paidCells_le hz hS hcell)'''
    new = '''  have he := paidCells_le_kernel hz hS hcell
  unfold eProfile
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using
    he.trans (le_add_of_nonneg_left (mul_nonneg hp hl))'''
    assert body.count(old) == 1
    body = body.replace(old, new)
    changes['W08KernelMatrix'] = before + marker + body

    retired = []
    for name in ['W08Entries0', 'W08EntriesRest']:
        text = read(name)
        lines = []
        for line in text.splitlines(keepends=True):
            match = re.match(r'theorem (entry([0-8])([0-8])) :', line)
            if match and match[3] != '0':
                retired.append(match[1])
                continue
            lines.append(line)
        text = ''.join(lines)
        assert text.count('elementaryMatrix paidMatrix') == 1
        changes[name] = text.replace('elementaryMatrix paidMatrix', 'elementaryMatrix paidMatrix cellEnvelope', 1)
    assert len(retired) == len(set(retired)) == 72

    text = read('W08Envelope')
    start, end = text.index('theorem paidMatrix_row0'), text.index('theorem elementaryCell_nonneg')
    retired.extend('paidMatrix_row' + str(i) for i in range(9))
    retired.append('elementaryMatrix_lt_paidMatrix')
    text = text[:start] + '''/-- A strict witness in column zero suffices for the actual positive vector. -/
theorem elementaryMatrix_lt_paidMatrix_col0 (i : Fin 9) :
    Wu04Bypass.elementaryMatrix i 0 < paidMatrix i 0 := by
  fin_cases i
  · exact entry00
  · exact entry10
  · exact entry20
  · exact entry30
  · exact entry40
  · exact entry50
  · exact entry60
  · exact entry70
  · exact entry80

theorem elementaryMatrix_le_paidMatrix (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k ≤ paidMatrix i k := by
  unfold Wu04Bypass.elementaryMatrix paidMatrix
  split_ifs
  · exact div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)
  · exact le_max_left _ _

''' + text[end:]
    start, end = text.index('theorem paidMatrix_pos'), text.index('/-- This increment')
    text = text[:start] + '''theorem paidMatrix_nonneg (i k : Fin 9) : 0 ≤ paidMatrix i k :=
  (elementaryMatrix_nonneg i k).trans (elementaryMatrix_le_paidMatrix i k)

''' + text[end:]
    retired.append('paidMatrix_pos')
    old = '''theorem eGainMatrix_pos (i k : Fin 9) : 0 < eGainMatrix i k :=
  sub_pos.mpr (elementaryMatrix_lt_paidMatrix i k)'''
    new = '''theorem eGainMatrix_nonneg (i k : Fin 9) : 0 ≤ eGainMatrix i k :=
  sub_nonneg.mpr (elementaryMatrix_le_paidMatrix i k)'''
    assert old in text
    text = text.replace(old, new)
    retired.append('eGainMatrix_pos')
    text = text.replace('(hpos : ∃ k, 0 < z k)', '(hpos : 0 < z 0)')
    old = '''  · obtain ⟨k, hk⟩ := hpos
    exact ⟨k, Finset.mem_univ k,
      mul_lt_mul_of_pos_right (elementaryMatrix_lt_paidMatrix i k) hk⟩'''
    new = '''  · exact ⟨0, Finset.mem_univ 0,
      mul_lt_mul_of_pos_right (elementaryMatrix_lt_paidMatrix_col0 i) hpos⟩'''
    assert old in text
    text = text.replace(old, new)
    # Only the legacy frozen-vector consumer needs strictness. Keep that
    # witness outside the final theorem's nonnegative matrix-credit route.
    start, end = text.index('/-- A strict witness'), text.index('theorem elementaryMatrix_le_paidMatrix')
    strict_column = text[start:end]
    text = text[:start] + text[end:]
    start, end = text.index('theorem apply_strict'), text.index('theorem apply_gain_eq')
    strict_apply = text[start:end]
    text = text[:start] + text[end:]
    assert text.startswith('import W08EntriesRest\n')
    changes['W08Envelope'] = text.replace('import W08EntriesRest\n', 'import W08KernelMatrix\n', 1)
    text = read('W08FrozenConsumer')
    old = '⟨0, Wu04Bypass.new_vector_positive 0⟩'
    assert old in text
    text = text.replace(old, '(Wu04Bypass.new_vector_positive 0)')
    assert text.count('theorem v8_apply_strict') == 1
    text = text.replace('theorem v8_apply_strict', strict_column + strict_apply + 'theorem v8_apply_strict', 1)
    changes['W08FrozenConsumer'] = text.replace('import W08Envelope\n', 'import W08Envelope\nimport W08EntriesRest\n', 1)

    text = read('W17JointSplit')
    start, end = text.index('theorem paidCell_le_eRemainder'), text.index('theorem rationalJ_le_jRemainder')
    old_helper = text[start:end]
    envelope_helper = old_helper.replace('theorem paidCell_le_eRemainder', 'theorem envelopeCell_le_eRemainder').replace('RemainingHf.paidCell S', 'W08.cellEnvelope S')
    raw_helper = '''theorem paidCell_le_eRemainder {S : ℝ} (hS : 3 ≤ S)
    (hc : S - 2 ≤ upperNode 0) (k : Fin 9) :
    RemainingHf.paidCell S (FirstFeedbackIntegrals.cellLeft (S - 2) k) (upperNode k) ≤
      W06.eRemainder (nodeBasis k) S :=
  (le_max_right _ _).trans (envelopeCell_le_eRemainder hS hc k)

'''
    text = text[:start] + envelope_helper + raw_helper + text[end:]
    assert text.count('have hE := paidCell_le_eRemainder') == 2
    changes['W17JointSplit'] = text.replace('have hE := paidCell_le_eRemainder', 'have hE := envelopeCell_le_eRemainder')

    replacements = {'elementaryMatrix_lt_paidMatrix': 'elementaryMatrix_lt_paidMatrix_col0', 'paidMatrix_pos': 'paidMatrix_nonneg', 'eGainMatrix_pos': 'eGainMatrix_nonneg'}
    retired_checks = set(retired) - set(replacements)
    for name in ['W08Root', 'W08Audit', 'W17ParentFullTypes']:
        text = read(name)
        lines = []
        for line in text.splitlines(keepends=True):
            if line.lstrip().startswith(('#check', '#print axioms')) and any(re.search(r'\b' + re.escape(n) + r'\b', line) for n in retired_checks):
                continue
            for old, new in replacements.items():
                line = re.sub(r'\b' + old + r'\b', new, line)
            lines.append(line)
        changes[name] = ''.join(lines)

    old_remaining = []
    for name, row in manifest.items():
        text = changes.get(name)
        if text is None:
            path = source / Path(*name.split('.')).with_suffix('.lean')
            text = path.read_text()
        for n in retired:
            if re.search(r'\b' + re.escape(n) + r'\b', text):
                old_remaining.append(dict(module=name, retired_basename=n))
    assert not old_remaining, old_remaining
    spec = importlib.util.spec_from_file_location('counter', repo / 'scripts/check.py')
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    output.mkdir(parents=True)
    rows, patch = [], []
    for name, text in changes.items():
        destination = output / 'src' / (name + '.lean')
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
        row = dict(module=name, before_sha256=manifest[name]['source_sha256'], after_sha256=sha(destination), source_code_lines_removed=counter.count_code_lines(originals[name]) - counter.count_code_lines(text))
        rows.append(row)
        patch.extend(difflib.unified_diff(originals[name].splitlines(keepends=True), text.splitlines(keepends=True), fromfile='before/' + name + '.lean', tofile='after/' + name + '.lean'))
    result = dict(status='UNCOMPILED_W08_MAX_ENVELOPE_DRAFT_NOT_INSTALLED_OR_ACCEPTED', baseline_run=str(run), baseline_manifest_sha256=sha(run / 'source-manifest.json'), preparer_sha256=sha(Path(__file__)), files=rows, removed_entry_comparison_declarations=72, remaining_entry_comparison_declarations=9, retired_internal_declarations=retired, formula_change='max of two certified bounds for the same kernel cell; never add their credits', strict_witness='column zero; the actual vector has a positive zeroth coordinate', source_code_lines_removed=sum(r['source_code_lines_removed'] for r in rows), numeric_input_formulas_or_parameters_modified=False, required=['Compile changed modules under the exclusive lock after the active batch', 'Review all remaining pointwise and weighted consumers and diagnostics', 'Retained public types and numerical definitions, literal 1.8938 and standard axioms', 'Actual downstream compilation and kernel validation; no performance improvement claimed yet'])
    (output / 'candidate.diff').write_text(''.join(patch))
    (output / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'remaining_entry_comparison_declarations', 'source_code_lines_removed']}))


if __name__ == '__main__':
    main()
