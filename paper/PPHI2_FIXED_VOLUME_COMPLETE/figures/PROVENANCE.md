# Figure provenance

Assets in this directory are **copies of rendered artefacts produced by the
project's own tooling**. No image was edited, cropped, recompressed or
re-rendered for this paper: each file below is byte-identical to its source.
Nothing here was drawn from a third-party publication.

| Asset | Source path (workspace root) | sha256 | Pixels (W x H) | How produced |
|---|---|---|---|---|
| `weak_limit_spine.png` | `paper/PPHI2_FIXED_VOLUME_WEAK_LIMIT/figures/weak_limit_spine.png` | `715ac60e83c56954699e799c3cf88669b7fd61e7fea4dbfbd154e449755ab17d` | 3240 x 2002 | Rendered artwork of the project's weakness-limit / spine diagram family, checked in with the sibling weak-limit manuscript's figure set. Consumed by `figures/fig_spine.tex`. |
| `lean_atlas_en_portrait.png` | `frontend/lean_nodes/dist/figures/lean_atlas_en_portrait.png` | `89fef234080850693e1cd042d367c01865c457c38ea59cb1be4fbe1d537982aa` | 2111 x 3277 | Output of the project's `frontend/lean_nodes` graph-render pipeline: the node/edge graph is rendered to vector SVG and rasterised, so each PNG in `dist/figures/` has a matching `.svg` sibling and is registered in `dist/figures/figures_manifest.json`. This is the English, portrait-orientation variant. Consumed by `figures/fig_atlas.tex`. |

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
