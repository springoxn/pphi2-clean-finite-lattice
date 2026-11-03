# Figure provenance

One asset here is **generated from source in this paper's own directory**, so
it reproduces rather than copies; the other is a **byte-identical copy** of a
rendered artefact of the project's tooling. No third-party artwork is used, and
no image was cropped or recompressed.

| Asset | Source path (workspace root) | sha256 | Pixels (W x H) | How produced |
|---|---|---|---|---|
| `weak_limit_spine.png` | generated here: `figures/generate_spine.py` | `36600f4bf506b12ea430e4de24be5cb568b220b03b6468ce73b9277dc2205fe7` | 3240 x 2002 | Drawn by the vendored generator (matplotlib, 450 dpi, 7.2 x 4.45 in) from the eight-step layout of `sec:main`. The generator writes `figures/generated/` and copies the PNG over this file, so figure and caption cannot drift apart. Consumed by `figures/fig_spine.tex`. |
| `lean_atlas_en_portrait.png` | `frontend/lean_nodes/dist/figures/lean_atlas_en_portrait.png` | `89fef234080850693e1cd042d367c01865c457c38ea59cb1be4fbe1d537982aa` | 2111 x 3277 | Output of the project's `frontend/lean_nodes` graph-render pipeline: the node/edge graph is rendered to vector SVG and rasterised, so each PNG in `dist/figures/` has a matching `.svg` sibling and is registered in `dist/figures/figures_manifest.json`. This is the English, portrait-orientation variant. Consumed by `figures/fig_atlas.tex`. |

## 2026-11-03: regenerated

The copy this file used to record was byte-identical to the sibling draft's
artwork, and it carried a printed footer --- *the physical-lattice total-carrier
lift has a separate named input and is not used here* --- that this paper had
since refuted: `lem:lift-representative` proves that lift total and Borel. The
caption disclosed the contradiction, but a reader should not have to read a
caption to unlearn a figure.

The generator now lives beside the figure (`figures/generate_spine.py`, vendored
from the sibling draft whose provenance this file documents), the footer states
the boundary `sec:main` actually draws, and the figure writes `m` where the text
writes `m` instead of making the caption translate `M`.

## Hashes and dimensions

The sha256 values above were computed with a real command, not transcribed:

```powershell
Get-FileHash -Algorithm SHA256 `
  E:\study\AImath\paper\PPHI2_FIXED_VOLUME_COMPLETE\figures\weak_limit_spine.png, `
  E:\study\AImath\paper\PPHI2_FIXED_VOLUME_COMPLETE\figures\lean_atlas_en_portrait.png
```

Run from the workspace root; an equivalent relative form is

```powershell
Get-FileHash -Algorithm SHA256 .\weak_limit_spine.png, .\lean_atlas_en_portrait.png
```

executed with the working directory set to this `figures/` directory.

Pixel dimensions were read from the PNG headers with

```powershell
Add-Type -AssemblyName System.Drawing
foreach ($f in @('weak_limit_spine.png','lean_atlas_en_portrait.png')) {
  $i = [System.Drawing.Image]::FromFile((Resolve-Path $f)); "$f $($i.Width)x$($i.Height)"; $i.Dispose()
}
```

## Verification

The copies can be re-checked against their sources at any time. Both source paths
are inside the repository, so a clone can carry them:

```powershell
Get-FileHash -Algorithm SHA256 `
  E:\study\AImath\paper\PPHI2_FIXED_VOLUME_WEAK_LIMIT\figures\weak_limit_spine.png, `
  E:\study\AImath\frontend\lean_nodes\dist\figures\lean_atlas_en_portrait.png
```

The two hashes must equal the table above. If a source is re-rendered, re-run
the commands and update this file rather than leaving the table stale.

The first recorded source of the spine figure,
`.scratch/github-sync-inspect/docs/weak_limit_paper/figures/weak_limit_spine.png`,
is byte-identical to the in-repo copy cited above, but lives under `.scratch/`,
which `.gitignore` excludes: the 2026-11-03 audit flagged a provenance chain that
lived outside the repository, and the durable copy is cited instead so that the
record survives a clone.
