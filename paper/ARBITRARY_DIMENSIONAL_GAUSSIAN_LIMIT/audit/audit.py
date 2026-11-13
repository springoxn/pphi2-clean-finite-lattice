#!/usr/bin/env python3
"""Audit source integrity, recorded Lean evidence, and the final PDF."""
from __future__ import annotations
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_SHA = "d1e9ab6b5f0790c2cc87d6dabfb91aee7292c8b8d5702181f8e4b903b90c497b"
ALLOW = {"propext", "Classical.choice", "Quot.sound"}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def check_hash(data, expected):
    if digest(data) != expected:
        raise AssertionError("SHA256 mismatch")

def check_axioms(text):
    if "sorryAx" in text or re.search(r"^error:", text, re.M):
        raise AssertionError("failed Lean transcript")
    reports = re.findall(r"depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if not reports:
        raise AssertionError("missing axiom reports")
    for report in reports:
        actual = {x.strip() for x in report.split(",") if x.strip()}
        if not actual <= ALLOW:
            raise AssertionError("unexpected axioms: " + repr(actual - ALLOW))
    return len(reports)

def main():
    tex = (ROOT / "main.tex").read_text(encoding="utf-8")
    normalized_tex = tex.replace("\\_", "_")
    anchors = ["sharp_actual_raw_gaussian_weak_convergence", "sharp_target_weight",
               "actualTarget_fixedVolume_weak_limit_existsUnique",
               "targetFiniteGaussianLimit_isGaussian", "propext", "Classical.choice", "Quot.sound"]
    for anchor in anchors:
        assert anchor in normalized_tex, "missing article anchor: " + anchor
    lean = ROOT / "lean"
    count = 0
    for line in (lean / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        expected, name = line.split("  ", 1)
        check_hash((lean / name).read_bytes(), expected)
        count += 1
    report_count = 0
    for name in ["sharp-contract.log", "endpoint-contract.log", "parent-sharp-contract.log"]:
        report_count += check_axioms((lean / name).read_text(encoding="utf-8"))
    build = (lean / "build-sharp.log").read_text(encoding="utf-8")
    assert "Build completed successfully" in build and "EXIT=0" in build
    assert "sorryAx" not in build and not re.search(r"^error:", build, re.M)
    generic = [p for p in lean.rglob("*.lean") if "ArbitraryDim" in p.name]
    for path in generic:
        source = path.read_text(encoding="utf-8")
        assert not re.search(r"\bsorry\b|^\s*axiom\s", source, re.M), str(path)
    rejected = 0
    for action in [lambda: check_hash(b"corrupt", digest(b"original")),
                   lambda: check_axioms("'test' depends on axioms: [sorryAx]"),
                   lambda: check_axioms("'test' depends on axioms: [inventedAxiom]")]:
        try:
            action()
        except AssertionError:
            rejected += 1
    assert rejected == 3, "negative controls did not reject corruption"
    archive = ROOT.parents[1] / "deliverables" / "20261112_arbitrary_dim_raw_gaussian.zip"
    if archive.is_file():
        check_hash(archive.read_bytes(), ARCHIVE_SHA)
    import fitz
    pdf = ROOT / "main.pdf"
    doc = fitz.open(pdf)
    assert len(doc) > 0
    text = " ".join(" ".join(page.get_text().split()) for page in doc)
    assert "Gaussian" in text and "Evidence ledger" in text and "References" in text
    assert "\ufffd" not in text, "replacement character in PDF"
    for page in doc:
        for block in page.get_text("dict")["blocks"]:
            for line in block.get("lines", []):
                for span in line["spans"]:
                    x0, y0, x1, y1 = span["bbox"]
                    assert x0 >= -1 and y0 >= -1 and x1 <= page.rect.width + 1 and y1 <= page.rect.height + 1, "text outside PDF page"
    result = {"status": "PASS", "asof": "2026-11-12", "source": "python audit/audit.py",
              "archive_sha256": ARCHIVE_SHA, "verified_file_hashes": count,
              "axiom_reports": report_count, "negative_controls": rejected,
              "generic_source_files": len(generic), "pdf_pages": len(doc),
              "pdf_sha256": digest(pdf.read_bytes())}
    (ROOT / "audit" / "result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, FileNotFoundError) as exc:
        print("AUDIT FAIL: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
