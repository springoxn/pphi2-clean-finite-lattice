#!/usr/bin/env python3
"""Source evidence cross-checks and independent symbolic normalization checks."""
from pathlib import Path
import json,re,sys,zipfile
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
def run():
    tex=(ROOT/'main.tex').read_text(encoding='utf-8')
    z=zipfile.ZipFile(ROOT/'inputs'/'20261111_periodic3d_hminus3_endpoint.zip')
    lean='\n'.join(z.read(n).decode() for n in z.namelist() if n.endswith('.lean'))
    names=sorted(set(re.findall(r'\\code\{((?:periodic3D|isCompact_closure_periodic3D)[^}]+)\}',tex)))
    for name in names: assert name in lean,('theorem missing from endpoint overlay',name)
    q=s.symbols('q',integer=True,positive=True)
    assert s.expand((2*q+1)**3-(2*q-1)**3-(24*q**2+2))==0
    b=s.symbols('b',positive=True)
    assert s.simplify(b**-6/b**-4-b**-2)==0
    assert s.simplify((s.sqrt(b**-8)/s.sqrt(b**-6))/s.sqrt(b**-8)-1/s.sqrt(b**-6))==0
    L=s.symbols('L',positive=True)
    assert s.simplify((1/s.sqrt(L))**2*L**4-L**3)==0
    assert 'standalone Mathlib \\code{IsGaussian}' in tex
    assert '24q^2+2' in tex
    return {'archived_declaration_references':names,'shell_count':'PASS','weight_ratio':'PASS','projection_cancellation':'PASS','target_volume_scaling':'PASS','IsGaussian_limitation':'PRESENT','role':'symbolic subset/source evidence cross-check, not Lean re-execution'}
if __name__=='__main__':
    try:
        result=run();(ROOT/'audit'/'source_result.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print(json.dumps(result,indent=2));sys.exit(0)
    except AssertionError as e: print('FAIL',e,file=sys.stderr);sys.exit(1)
    except Exception as e: print('ERROR',repr(e),file=sys.stderr);sys.exit(2)
