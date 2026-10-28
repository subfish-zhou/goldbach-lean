# LiuPan unused-proof removal

The accepted 1+1.8938 development retains its original precision. Nine files remove 383 unused theorems/lemmas, saving 10,924 effective lines. Definitions, instances, attributes and retained source text are unchanged.

See [validation.json](validation.json) for the full build, literal/axiom, kernel and measurement evidence, and [the phase description](../../docs/WU_LIUPAN_PRUNING.md). `audit.py` and `manifest.json` independently reconstruct the nine edited files from the fixed Git baseline; their result is explicitly static evidence.

```sh
python3 research/wu-liupan-pruning-audit/audit.py --repo .
```

The raw timeout/resume history and failed initial checker attempt are preserved in the local adoption archive, with copy manifests here. No historical complete inherited environment is asserted. Standalone kernel checks explicitly select the pinned `LEAN_SYSROOT`.

The later [structural phase](../wu-structural-compression-audit/README.md) supersedes the current-tree totals; this 383-lemma record remains immutable historical evidence.
