# Provenance, and what differs from the audited archive

This repository is a **published slice** of an audited Lean package.  The slice
is not a rewrite: the Lean sources are the audited bytes.  This file records
exactly where they came from, what was changed, and how to check the claim.

## The archive it comes from

| Field | Value |
|---|---|
| Archive | `20261020_pphi2_clean_finite_lattice.zip` |
| SHA-256 | `39b6ff887baaff0dca9b7edd1a0ab4451f20a256a8e0700a4615638f7c1937db` |
| Registry | `proof_graph/deliverables.yaml` in the AImath project (records the same hash) |
| Contents | 118 entries, self-manifested by an internal `SHA256SUMS` |
| Upstream | `mrdouglasny/GaussianField` at commit `d63a28568a75d99f6cb27af1f888a49a69855a66` |

The archive's own audit logs — build, axiom firewall, interface gate, upstream
source correspondence — are shipped here unchanged under `audit/`.  They are
the evidence for the footprint claim; this repository does not re-derive them
in prose.

## Delta against the archive

Checked mechanically at export time, against the archive's own per-file hashes:

| Bucket | Count |
|---|---|
| archive entries | 118 |
| present here, **byte-identical** | 103 |
| present here, changed (all listed below) | 5 |
| excluded (all listed below) | 10 |

The five changed files are `README.md`, `LICENSE`, and the three audit
scripts; every Lean module, every audit log and the build configuration are
byte-for-byte the audited ones.

### Rewritten or upgraded (2)

| Path | Why |
|---|---|
| `README.md` | rewritten for a public audience.  The archive's original README is preserved **byte-identically** at `ARCHIVE_README.md` in the `docs` directory. |
| `LICENSE` | the archive shipped the short Apache-2.0 boilerplate notice (774 bytes) that refers to the full text by URL; this repository carries the canonical full text (11357 bytes) so that license detection and redistribution are unambiguous.  The license is the same: Apache-2.0. |

Note on the archived README: it is kept verbatim for provenance, including a
usage example that names the original build machine's checkout path.  Use the
top-level `README.md` for the portable command; the archived text is a record,
not an instruction.

### Made portable (3)

These three scripts carried absolute paths to the build machine's toolchain and
interpreter.  The logic is untouched; only the three path bindings changed, and
each now falls back to the same elan location as before.

| Path | Change |
|---|---|
| `audit/run_finite_lattice_checks.sh` | `LAKE` / `LEAN` / `PYTHON` from the environment, elan default as fallback; the upstream checkout is now a required argument instead of a hard-coded path |
| `audit/run_firewall.sh` | same treatment for `LAKE` / `LEAN` / `PYTHON` |
| `audit/run_interface_gate.py` | `LAKE` resolved from `$LAKE`, then `PATH`, then the elan default |

### Replaced (1, counted among the excluded)

| Path | Why |
|---|---|
| `SHA256SUMS` | it describes the archive's file set, which is not this file set.  `MANIFEST.sha256` covers every published file and is what `verify.py` checks. |

### Excluded (10)

| Path | Why |
|---|---|
| `SHA256SUMS` | superseded by `MANIFEST.sha256` (see above). |
| `audit/upstream_full/*` (5 files) | an axiom/`sorry` census of the **upstream** repository.  It depends on a private baseline checkout and is about a different package; nothing claimed here depends on it. |
| `audit/upstream_candidate/*` (4 files) | the declaration-selection step feeding that census, same reason. |

### Added (8)

`.gitattributes`, `.gitignore`, `MANIFEST.sha256`, `NOTICE`, `PROVENANCE.md`
(this file), `verify.py`, and `docs/` (the archived README and the companion
manuscript).

## Byte-stability across `git`

`.gitattributes` sets `* -text`, so git performs **no end-of-line conversion**.
This is deliberate: the published bytes must equal the audited bytes, and a
silent CRLF/LF rewrite would change them without changing a single visible
character.  With `-text`, `MANIFEST.sha256` is checkable on a fresh clone as
well as in a working tree.

## The numbers in the README

They are functions of the sources, not transcriptions:

```bash
python verify.py --count    # modules, lines, declarations, theorem-level count
```

The archived numbers that cannot be recomputed from prose — 64 declarations in
the axiom report, 27 interface certificates, 8878 build jobs — are read by that
command from `audit/finite_lattice_all_declarations_interface.lean`,
`audit/*_interface.lean` and `audit/finite_lattice_build.log` respectively, so
the README figures are reproducible from this repository alone.
