#!/usr/bin/env python3
"""Audit source claims and the compiled PDF; failures exit nonzero."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_SOURCE = {
    "main.tex": ["122409", "\u0073>d/2", "no arbitrary-dimensional Lean convergence theorem"],
    "sections/03-general-theorem.tex": ["Raw-lift convergence in every fixed dimension", "Prokhorov's theorem"],
    "sections/04-formal-endpoints.tex": ["122409", "61206", "61205", "do not assemble a dimension-generic probability measure"],
    "sections/05-evidence.tex": ["not a Lean theorem", "does not re-execute"],
    "sections/06-evidence-ledger.tex": ["Arbitrary-$d$ Lean weak convergence", "Explicitly not established"],
}
REQUIRED_PDF = [
    "dimension-uniform analysis",
    "raw-lift convergence in every fixed dimension",
    "fixed 122409-dimensional raw-lift limit",
    "arbitrary-d lean weak conver",
    "explicitly not established",
]


def source_checks(root=ROOT):
    errors = []
    joined = "\n".join(p.read_text(encoding="utf-8") for p in sorted(root.rglob("*.tex")))
    for rel, phrases in REQUIRED_SOURCE.items():
        path = root / rel
        if not path.is_file():
            errors.append(f"missing source: {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        for phrase in phrases:
            if phrase not in text:
                errors.append(f"{rel}: missing anchor {phrase!r}")
    if "\\label{thm:122409}" not in joined or "\\label{thm:general}" not in joined:
        errors.append("theorem labels are missing")
    if "\\begin{thebibliography}" not in joined or "\\end{thebibliography}" not in joined:
        errors.append("bibliography environment is missing")
    if 61205 <= 122409 / 2:
        errors.append("source energy exponent does not exceed d/2")
    if 61206 <= 122409 / 2:
        errors.append("target exponent does not exceed d/2")
    return errors


def pdf_checks(path):
    try:
        import fitz
    except ImportError as exc:
        return None, [f"PyMuPDF unavailable: {exc}"]
    if not path.is_file():
        return None, [f"missing PDF: {path}"]
    doc = fitz.open(path)
    text_pages = [page.get_text("text") for page in doc]
    text = "\n".join(text_pages)
    errors = []
    if "Periodic Raw Atomic Gaussian Limits Across Dimensions" not in doc.metadata.get("title", ""):
        errors.append("PDF metadata title is missing")
    if len(doc) < 6:
        errors.append(f"unexpectedly short PDF: {len(doc)} pages")
    normalized = re.sub(r"\s+", " ", text).lower()
    for phrase in REQUIRED_PDF:
        if phrase not in normalized:
            errors.append(f"PDF text missing anchor: {phrase!r}")
    if re.search(r"\?\?|Citation .* undefined|Reference .* undefined", text, re.I):
        errors.append("unresolved reference marker in extracted PDF text")
    if any(len(page.strip()) < 100 for page in text_pages):
        errors.append("blank or nearly blank page detected")
    page_bounds_ok = True
    for page in doc:
        rect = page.rect
        for block in page.get_text("blocks"):
            x0, y0, x1, y1 = block[:4]
            if x0 < -1 or y0 < -1 or x1 > rect.width + 1 or y1 > rect.height + 1:
                page_bounds_ok = False
    if not page_bounds_ok:
        errors.append("text block outside page bounds")
    font_records = {f[0]: f[3] for page in doc for f in page.get_fonts(full=True) if f[0] > 0}
    fonts = sorted(set(font_records.values()))
    embedded_fonts = []
    for xref, name in font_records.items():
        extracted = doc.extract_font(xref)
        if extracted and len(extracted[3]) > 0:
            embedded_fonts.append(name)
    if not fonts:
        errors.append("PDF contains no discoverable fonts")
    if not embedded_fonts:
        errors.append("PDF contains no extractable embedded font programs")
    info = {
        "pages": len(doc),
        "title": doc.metadata.get("title", ""),
        "fonts": fonts,
        "embedded_fonts": sorted(set(embedded_fonts)),
        "page_text_chars": [len(t) for t in text_pages],
        "pdf_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }
    return info, errors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", type=Path, default=ROOT / "periodic_gaussian_dimensional_sweep.pdf")
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    source_errors = source_checks()
    if args.self_test:
        if not source_checks(ROOT / "nonexistent"):
            print("FAIL: negative control did not fail", file=sys.stderr)
            return 1
        if source_errors:
            print("FAIL: real source checks failed", file=sys.stderr)
            return 1
        print("PASS: source audit and negative control")
        return 0
    pdf_info, pdf_errors = (None, []) if args.source_only else pdf_checks(args.pdf)
    result = {"source_errors": source_errors, "pdf_errors": pdf_errors, "pdf": pdf_info}
    report = ROOT / "audit" / "result.json"
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    for error in source_errors + pdf_errors:
        print(f"FAIL: {error}", file=sys.stderr)
    if source_errors or pdf_errors:
        return 1
    print(f"PASS: source audit" + (f", PDF pages={pdf_info['pages']}" if pdf_info else ""))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except Exception as exc:
        print(f"AUDIT ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
