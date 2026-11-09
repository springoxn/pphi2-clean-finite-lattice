# Audit of the dimensional-bridge article

This report accompanies the publication snapshot of the article. It records
checks actually executed; it is not a live status source for the parent project.

## Mathematical review

Two independent read-only reviews examined the public Lean source and the
manuscript. The final review found no substantive flaw in the common paper
proof: normalization, fixed-mode covariance, atom regularity, compactness,
tightness and uniqueness were checked as written. This is review evidence,
not a machine proof of the arbitrary-dimensional theorem.

The article separates the two native Lean instances from the arbitrary-dimension
paper synthesis. It states the two-dimensional weight exactly, explains its
equivalent topology, and separates physical coefficients from stored weighted
coordinates and positive from negative Fourier sign conventions.

## Findings and repairs

1. **Refuted earlier guide bound.** The old dispersion bound omitted `L^-4`.
   At `L=1/10`, `N=100`, and mode `(1,0,0,0)`, the dispersion gap exceeds
   the old alleged upper bound. The corrected bound follows algebraically from
   `pi*k/N = pi*a*k/L`. The finite counterexample and both numerical bounds are
   recomputed by the audit. The article records the error explicitly; the public
   guide is corrected in this publication. No Lean source is changed.
2. **Module attribution repaired.** Real-coordinate encoding belongs to
   the main four-dimensional probe/moment module. The real-carrier module
   proves closed support and compact real slices. The component table now
   reflects this division.
3. **Two-dimensional evidence completed.** A new joint query and independent
   typed examples were run on the server's isolated release checkout. The
   resulting transcript now covers both final native theorems. Its provenance
   record binds every release source/configuration hash and exact dependencies.
4. **Layout repaired.** The first compiled draft had overfull identifier lines.
   Breakable identifiers and a prose axiom list removed those overflows. The
   final TeX log contains no overfull boxes, unresolved references or missing
   character warnings. Harmless underfull table-cell warnings remain.
5. **Audit anchor errors repaired.** The first audit used a wrong theorem-token
   spelling and assumed the PDF title retained mixed case. Those checks were
   corrected against the actual TeX and rendered title. They remain strict
   about the content rather than accepting arbitrary text.

## Executed checks

- Tectonic compilation using cached resources, with final PDF output.
- Source environment balance, unique labels, resolved references and citation keys.
- Exact SymPy volume prefactors and the dispersion-to-variance scale identity.
- Independent finite precision-matrix inversion versus Fourier variance,
  including `N=1`, even `N=2`, and small physical volume.
- A negative control demonstrating failure of the old guide's missing scale factor.
- Joint Lean contract: both native theorem signatures, axiom queries, and
  independently typed convergence examples; command exit code zero.
- Source hashes and module census compared with the public release checkout.
- PDF text extraction, all three table captions, evidence phrases, nonblank pages,
  missing-glyph/replacement checks, and page-margin geometry.
- Mutation controls: removed main-theorem anchor and altered Lean transcript
  both cause nonzero checker exits; intact controls succeed.
- Representative PDF pages rendered and visually inspected for equations,
  headings, table layout, references and clipping.

The machine-readable result is in `result.json`. The frozen TeX log is
`tex.log`; the executed joint Lean output is `bridge_contract.log`.

## Limits

The symbolic checks are finite and do not verify compactness, measure extension,
or weak convergence for all parameters. Those statements are proved in the
paper, with two fixed instances independently certified by Lean. The PDF audit
is an artifact-layer guard, not a proof checker. Query and log hashes establish
consistency, not a cryptographic signature from an independent authority.
The current publication includes no arbitrary-dimensional Lean theorem,
interacting four-dimensional result, or infinite-volume construction.
