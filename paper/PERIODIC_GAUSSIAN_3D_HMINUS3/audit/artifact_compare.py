#!/usr/bin/env python3
"""Built-artifact fidelity test with a deliberately broken merged-PDF control.
Uses the production page-by-page comparison audit; the missing-page mutation
must be rejected. This is appropriate for text-only mathematical papers, unlike
an unconditional requirement for raster images. No Lean proof is re-executed.
"""
from pathlib import Path
import importlib.util,json,sys,tempfile
import fitz
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('h3_build',ROOT/'build.py'); b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
def run():
    previous=ROOT/'inputs'/'20261110_periodic_gaussian_3d_companion.pdf'
    supplement=ROOT/'build'/'main.pdf'
    merged=ROOT/'build'/b.PDF_NAME
    result=b.audit(previous,supplement,merged)
    with tempfile.TemporaryDirectory() as td:
        broken=Path(td)/'missing_page.pdf';doc=fitz.open(merged);doc.delete_page(len(doc)-1);doc.save(broken);doc.close()
        rejected=False
        try:b.audit(previous,supplement,broken)
        except AssertionError:rejected=True
        assert rejected,'negative control failed: missing PDF page accepted'
    result['missing_page_negative_control']='REJECTED AS REQUIRED'
    result['text_only_document']='No raster figures required; all mathematical fonts embedded'
    return result
if __name__=='__main__':
    try:
        r=run();(ROOT/'audit'/'artifact_compare_result.json').write_text(json.dumps(r,indent=2),encoding='utf-8');print('Artifact fidelity and negative control PASS');sys.exit(0)
    except AssertionError as e:print('FAIL',e,file=sys.stderr);sys.exit(1)
    except Exception as e:print('ERROR',repr(e),file=sys.stderr);sys.exit(2)
