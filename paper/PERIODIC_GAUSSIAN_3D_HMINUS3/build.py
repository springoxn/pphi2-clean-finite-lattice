#!/usr/bin/env python3
"""Compile the new supplement, append it to the preserved companion, audit and package.
Run python build.py. Requires Tectonic and PyMuPDF (fitz). Set TECTONIC and
TECTONIC_CACHE_DIR if necessary; the latter may point to an existing offline cache.
No Lean execution is performed by this PDF-production script.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,zipfile
import fitz
ROOT=Path(__file__).resolve().parent
INPUTS=ROOT/'inputs'
OUT=ROOT/'build'
PDF_NAME='20261111_periodic_gaussian_3d_hminus3_complete.pdf'
ZIP_NAME='20261111_periodic_gaussian_3d_hminus3_complete_sources.zip'
EXPECTED={
'20261110_periodic_gaussian_3d_companion.pdf':'377edc8ad4abe346bf46d72e345089e57a678e0e63722f3b6cb7f8db9effcce3',
'20261110_periodic_gaussian_3d_companion_sources.zip':'2c40ff72c240b5f4824681eaf59c39ec893fff31aa0965df00bbcfb5ddf40f2a',
'20261111_periodic3d_hminus3_endpoint.zip':'d1b132e15d9aa34c22c9db1b29238d26d86c367ac299dda5cfee9b42e7a6dba2'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def audit(previous,supplement,merged):
    a,b,c=map(fitz.open,(previous,supplement,merged))
    assert len(c)==len(a)+len(b)
    for i,p in enumerate(a): assert c[i].get_text()==p.get_text(),('previous order/text',i)
    for i,p in enumerate(b): assert c[len(a)+i].get_text()==p.get_text(),('supplement order/text',i)
    text=' '.join(p.get_text() for p in b)
    required=['Source, weights','Uniform H-minus-two energy','The inclusion and the unique target lift','Exact physical projections','Lean theorem map','IsGaussian','Classical.choice']
    for s in required: assert s.lower() in text.lower(),('missing heading/text',s)
    bad=[];fonts={}
    for i,p in enumerate(c):
        assert len(p.get_text().strip())>40,('blank page',i+1)
        assert '\ufffd' not in p.get_text(),('replacement glyph',i+1)
        for block in p.get_text('dict')['blocks']:
            for line in block.get('lines',[]):
                for span in line['spans']:
                    x0,y0,x1,y1=span['bbox']
                    if x0 < -0.5 or y0 < -0.5 or x1>p.rect.width+0.5 or y1>p.rect.height+0.5: bad.append([i+1,span['text'],span['bbox']])
        for f in p.get_fonts(full=True):
            xref=f[0]
            if xref:
                data=c.extract_font(xref)
                assert data[3],('unembedded font',i+1,f)
                fonts[f[3]]=data[1]
    assert not bad,('out of page text',bad)
    renders=ROOT/'audit'/'renders';renders.mkdir(parents=True,exist_ok=True)
    for old in renders.glob('page_*.png'): old.unlink()
    for i in sorted({0,len(a)-1,len(a),len(c)-1}): c[i].get_pixmap(matrix=fitz.Matrix(1.2,1.2)).save(str(renders/f'page_{i+1:02d}.png'))
    return {'previous_pages':len(a),'supplement_pages':len(b),'complete_pages':len(c),'required_text':required,'embedded_fonts':fonts,'page_order_and_text':'PASS','page_bounds':'PASS','replacement_glyphs':'NONE','input_sha256':EXPECTED,'combined_sha256':sha(merged),'supplement_sha256':sha(supplement)}
def main():
    OUT.mkdir(exist_ok=True);(ROOT/'audit').mkdir(exist_ok=True)
    for n,h in EXPECTED.items(): assert sha(INPUTS/n)==h,('input changed',n)
    exe=os.environ.get('TECTONIC') or shutil.which('tectonic')
    fallback=Path('D:/Anaconda/envs/latex/Library/bin/tectonic.exe')
    if not exe and fallback.is_file(): exe=str(fallback)
    if not exe: raise RuntimeError('Install Tectonic or set TECTONIC')
    env=dict(os.environ); env['SOURCE_DATE_EPOCH']='1794355200'
    cache=Path(env.get('TECTONIC_CACHE_DIR',ROOT/'.texcache'))
    seed=ROOT.parent/'PERIODIC_GAUSSIAN_3D_COMPANION'/'.texcache'
    if not cache.exists() and seed.exists(): shutil.copytree(seed,cache)
    env['TECTONIC_CACHE_DIR']=str(cache)
    result=subprocess.run([exe,'--only-cached','--keep-logs','--outdir',str(OUT),'main.tex'],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (ROOT/'audit'/'tectonic_stdout.log').write_bytes(result.stdout)
    if result.returncode: print(result.stdout.decode(errors='replace'));return 1
    log=(OUT/'main.log').read_text(encoding='utf-8')
    assert not re.search(r'Overfull|Missing character|undefined references|undefined control sequence|not loadable',log,re.I),'TeX layout/reference/font warning'
    previous=INPUTS/'20261110_periodic_gaussian_3d_companion.pdf'; supplement=OUT/'main.pdf'
    merged=OUT/PDF_NAME
    doc=fitz.open();doc.insert_pdf(fitz.open(previous));doc.insert_pdf(fitz.open(supplement));doc.set_metadata({'title':'Three-dimensional periodic Gaussian limit: original companion and H-minus-three supplement','author':'Yj Zheng'});doc.save(merged,garbage=4,deflate=True,no_new_id=True);doc.close()
    report=audit(previous,supplement,merged)
    (ROOT/'audit'/'result.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    (ROOT/'audit'/'combined_text.txt').write_text(''.join(p.get_text() for p in fitz.open(merged)),encoding='utf-8')
    for checker in ['verify_sources.py','artifact_compare.py']:
        check=subprocess.run([sys.executable,str(ROOT/'audit'/checker)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (ROOT/'audit'/(checker+'.log')).write_bytes(check.stdout)
        if check.returncode: print(check.stdout.decode(errors='replace'));return check.returncode
    dest=ROOT.parent.parent/'deliverables'
    if not dest.is_dir(): dest=OUT
    shutil.copy2(merged,dest/PDF_NAME) if merged.resolve()!=(dest/PDF_NAME).resolve() else None
    archive=dest/ZIP_NAME
    with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
        for p in [ROOT/'main.tex',ROOT/'build.py',ROOT/'README.md']+sorted(INPUTS.glob('*'))+sorted((ROOT/'audit').glob('*')):
            if p.is_file():z.write(p,p.relative_to(ROOT).as_posix())
        z.write(supplement,'build/supplement.pdf');z.write(merged,'build/'+PDF_NAME)
        for p in sorted((ROOT/'audit'/'renders').glob('*.png')):z.write(p,p.relative_to(ROOT).as_posix())
    assert zipfile.ZipFile(archive).testzip() is None
    print(json.dumps({'pdf':str(dest/PDF_NAME),'pdf_sha256':sha(dest/PDF_NAME),'source_zip':str(archive),'source_zip_sha256':sha(archive),'audit':report},indent=2))
    return 0
if __name__=='__main__':
    try:sys.exit(main())
    except AssertionError as e:print('AUDIT FAIL:',e,file=sys.stderr);sys.exit(1)
    except Exception as e:print('BUILD ERROR:',repr(e),file=sys.stderr);sys.exit(2)
