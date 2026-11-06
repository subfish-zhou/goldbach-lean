#!/usr/bin/env python3
"""Prepare an uncompiled generalization of the two Pan character-square proofs.

The base is the frozen shared-proof batch, not the installed tree. No part of
that batch is edited. This candidate is deliberately not included in its build
or in accepted savings. Its new common proof is derived from the Type I proof;
the coefficient function becomes an arbitrary real sequence, without adding
hypotheses. Both old public theorem statements remain byte-for-byte explicit.
"""

import argparse
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def proof_region(source, name):
    start = source.index("theorem " + name + " ")
    body = source.index(":= by\n", start) + len(":= by\n")
    end = source.index("/-! ## 7.", body)
    return body, end


def reindex_region(source):
    start = source.index("/-- Reindex an `ℕ` range sum")
    end = source.index("/-- **Per-modulus character square-sum bound**:", start)
    return start, end


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    base, output = args.base.resolve(), args.output_dir.resolve()
    if output == base or base in output.parents:
        parser.error("output must be separate from the frozen batch")
    repo = Path(__file__).resolve().parents[2]
    module = "AnalyticNumberTheory.LargeSieve.RealCharacterSquareSum"
    first_rel = Path("AnalyticNumberTheory/Sieve/PanV1SquareMean.lean")
    third_rel = Path("AnalyticNumberTheory/Sieve/PanV3SquareMean.lean")
    first = (base / "src" / first_rel).read_text()
    third = (base / "src" / third_rel).read_text()
    manifest = {r["module"]: r for r in json.loads((base / "source-manifest.json").read_text())}
    for relative, text in [(first_rel, first), (third_rel, third)]:
        name = str(relative.with_suffix("")).replace("/", ".")
        assert digest(text.encode()) == manifest[name]["source_sha256"], name
    body_start, body_end = proof_region(first, "panTypeICharSqSum_le_additiveSieve")
    helper_start, helper_end = reindex_region(first)
    helper = first[helper_start:helper_end]
    body = first[body_start:body_end]
    # This witness is never used by either original proof; both applications
    # perform the additive comparison on the integer interval directly.
    unused_start = body.index("  have hcr :")
    unused_end = body.index("  -- characterSieveModulus_le", unused_start)
    assert body.count("hcr") == 1
    body = body[:unused_start] + body[unused_end:]
    character_sum = "(∑ n ∈ Finset.range (m + 1), (f n : ℂ) * χ (n : ZMod q))"
    square_sum = f"(∑ χ : DirichletCharacter ℂ q, ‖{character_sum}‖ ^ 2)"
    body = body.replace("    unfold panTypeIV1CharSum\n", "")
    body = body.replace("panTypeIV1CharSum q m u χ", character_sum)
    body = body.replace("panTypeICharSqSum q m u", square_sum)
    body = body.replace("vaughanFirst n.toNat u", "f n.toNat")
    body = body.replace("vaughanFirst n u", "f n")
    # The old proof's explanatory comments mention its original coefficient;
    # omit them to keep the common theorem independent of either application.
    body = "\n".join(line for line in body.splitlines() if not line.lstrip().startswith("--")) + "\n"
    assert "panTypeI" not in body and "vaughanFirst" not in body
    common = f'''import AnalyticNumberTheory.LargeSieve.Multiplicative

/-! UNCOMPILED candidate: one coefficient-parametric proof for both Pan cases. -/
namespace AnalyticNumberTheory.LargeSieve
open Finset Real
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

{helper}/-- The per-modulus estimate depends only on the real coefficient sequence. -/
theorem realCoefficientCharacterSqSum_le (q m : ℕ) (hq : 0 < q) (f : ℕ → ℝ) :
    {square_sum} ≤
      ((q.totient : ℝ) / (q : ℝ)) *
        largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (f n) ^ 2) := by
{body}
end AnalyticNumberTheory.LargeSieve
'''
    candidates = {Path(*module.split(".")).with_suffix(".lean"): ("", common)}
    for relative, source, prefix, coefficient in [
        (first_rel, first, "panTypeI", "vaughanFirst n u"),
        (third_rel, third, "panTypeII", "vaughanThird n u v"),
    ]:
        name = prefix + "CharSqSum_le_additiveSieve"
        start, end = proof_region(source, name)
        char_sum = "panTypeIV1CharSum" if prefix == "panTypeI" else "panTypeIIV3CharSum"
        replacement = (
            f"  simpa only [{prefix}CharSqSum, {char_sum}] using\n"
            f"    realCoefficientCharacterSqSum_le q m hq (fun n => {coefficient})\n\n"
        )
        result = source[:start] + replacement + source[end:]
        start, end = reindex_region(result)
        result = result[:start] + result[end:]
        result = f"import {module}\n" + result
        candidates[relative] = (source, result)
    spec = importlib.util.spec_from_file_location("counter", repo / "scripts/check.py")
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    records, patches = [], []
    for relative, (before, after) in candidates.items():
        destination = output / "src" / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(after)
        records.append({
            "module": str(relative.with_suffix("")).replace("/", "."),
            "before_sha256": digest(before.encode()) if before else None,
            "after_sha256": digest(after.encode()),
            "effective_lines_saved": counter.count_code_lines(before) - counter.count_code_lines(after),
            "physical_lines_saved": len(before.splitlines()) - len(after.splitlines()),
            "bytes_saved": len(before.encode()) - len(after.encode()),
        })
        patches.extend(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True),
            fromfile="a/" + str(relative) if before else "/dev/null",
            tofile="b/" + str(relative),
        ))
    (output / "candidate.diff").write_text("".join(patches))
    report = {
        "status": "UNCOMPILED_NOT_INSTALLED_NOT_PART_OF_RUNNING_BATCH",
        "patch_root": "Wu source directory (src/)",
        "base_manifest_sha256": digest((base / "source-manifest.json").read_bytes()),
        "modules": records,
        "projected_incremental_savings": {
            key: sum(r[key] for r in records)
            for key in ["effective_lines_saved", "physical_lines_saved", "bytes_saved"]
        },
        "required_checks": [
            "Compile the common module and both applications under the Lean lock.",
            "Compare every retained public type with the frozen batch.",
            "Check both retired private reindex helpers' actual incoming uses.",
            "Check the new import graph for cycles and source/object consistency.",
            "Validate affected downstream sources before installation.",
            "Check standard axioms and replay the final kernel after the affected build.",
        ],
    }
    (output / "candidate.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["projected_incremental_savings"]))


if __name__ == "__main__":
    main()
