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
| present here, **byte-identical** | 102 |
| present here, changed (all listed below) | 6 |
| excluded (all listed below) | 10 |
| present here, **not in the archive** (all listed below) | 2 |

The six changed files are `README.md`, `LICENSE`, the three audit scripts, and
the library root `AImathPPhi2Clean.lean`; apart from the root, every Lean module,
every audit log and the build configuration are byte-for-byte the audited ones.
The two files that are not in the archive are the post-pin extension, described
under *Post-pin extension* below.

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

## Post-pin extension

This repository publishes one step taken **after** the archive was pinned: the
physical sampling convention and the UV-uniform second-moment bound.  It lives
outside the audited archive, so it is kept in a separate bucket with its own
evidence, and the paper it accompanies reports it in a separate section.

| Path | What it is | SHA-256 |
|---|---|---|
| `AImathPPhi2Clean/PhysicalLatticeGaussianBound.lean` | the eigenvalue floor `m² ≤ λ_k`, the sampled covariance bound, the numbered form | `098adab81139f267196f6cd057f59c1cd32036112eb1f62116ee044268d79a09` |
| `AImathPPhi2Clean/PhysicalLatticeSampling.lean` | physical lattice points, Riemann weights, the pushforward measure, the spacing-uniform bound | `956db2c6924cbfaf27c102794170924ca4950d743d50663fa86c198ea19e8e88` |

Both files are the working tree's bytes, copied unchanged.  The library root is
the one substantive change: the archive's root plus two `import` lines.  The
working tree imports a third module as well (work in progress, not published
here), so the published root is the tree's root **minus that one line** — and
that is why it reproduces, byte-for-byte, the root hash recorded by the evidence
run:

```
AImathPPhi2Clean.lean   7f1aeda871be56abbcada56d3e99b78164335765674f0d4cd0ec8de2f37cfd1e
```

The evidence is shipped, not summarised.  Both files are in the `docs`
directory, next to the manuscript:

| File | What it is |
|---|---|
| `extension_evidence.log` | a transcript of one run on the build host: toolchain and Mathlib pins, the two module hashes, the root's imports and hash, `lake build` (8880 jobs = the archive's 8878 + one job per module), and the axiom footprint of each of the 14 declarations the two modules introduce |
| `ext_axioms.lean` | the `#print axioms` query of that run; regenerating it from the two modules reproduces it byte-for-byte |

`python verify.py --ext` checks the part that a published repository can check:
each module still hashes to what the transcript pinned, the root still imports
both and still hashes to the root the run built, every declaration of the two
modules has a report, and every reported footprint is inside the archive's
allowlist.  It does **not** re-run the build (that needs Mathlib; see the README)
and it cannot tell you that the statements are the intended ones — that is what
the manuscript's §11 is for.

A caveat, stated because the transcript is a transcript: Lean's line wrapping
inside the axiom lists is removed (one line per declaration) and the build's
warning output is dropped.  No value that the repository or the manuscript prints
comes from the removed text.

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
python verify.py --ext      # the post-pin extension: hashes, coverage, axioms
```

The archived numbers that cannot be recomputed from prose — 64 declarations in
the axiom report, 27 interface certificates, 8878 build jobs — are read by that
command from `audit/finite_lattice_all_declarations_interface.lean`,
`audit/*_interface.lean` and `audit/finite_lattice_build.log` respectively, so
the README figures are reproducible from this repository alone.
