"""Derive physical-reader checker geometry from its canonical B row selector."""
from pathlib import Path
RULES={
 'run-physical-resources.lisp':[
 ('(+ 4 (fn2-b-upload-windows profile) (fn2-b-run-cursor-rows profile))','(+ (fn2-b-run-loader-row 0 profile) (fn2-b-run-cursor-rows profile))'),
 ('(fn2-run-load-checker-init 0 (+ 4 (fn2-b-upload-windows profile)) fn2-run-loads)','(fn2-run-load-checker-init 0 (fn2-b-run-loader-row 0 profile) fn2-run-loads)')],
 'run-physical-geometry.lisp':[
 ('(uploads :u32)','(upload-hash-rows :u32)'),
 ('(unsigned-byte-p 32 (+ 4 (fn2-b-upload-windows profile)))','(and (<= 4 (fn2-b-run-loader-row 0 profile)) (unsigned-byte-p 32 (fn2-b-run-loader-row 0 profile)))'),
 ('(uploads (fn2-b-upload-windows profile))','(upload-hash-rows (nfix (- (fn2-b-run-loader-row 0 profile) 4)))'),
 ('(prefix (+ 4 (fn2-b-upload-windows profile)))','(prefix (fn2-b-run-loader-row 0 profile))')],
 'run-physical-readiness.lisp':[
 ('fn2-run-load-geometry-uploads','fn2-run-load-geometry-upload-hash-rows')]
}
def project(name,text):
 for before,after in RULES[name]:
  if text.count(before)!=1:raise ValueError((name,before,text.count(before)))
  text=text.replace(before,after)
 return text
if __name__=='__main__':
 for name in RULES:
  p=Path('books')/name;p.write_text(project(name,p.read_text()))
