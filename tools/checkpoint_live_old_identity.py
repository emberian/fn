"""Spell the finite exact-source identity projection for live adoption.

Metadata constructors read actual held source rows; the successful manifest
emit copies these values before continuation. No reader, hash or comparison
is implemented here; this is the repetitive generated source field mapping.
"""
FIELDS=[('slot',':u32'),('gen',':u60'),('unit',':u60'),('epoch',':u60'),('allocation',':u60'),('physical',':bool'),('tag',':u60'),('top',':u8'),('entries',':u60'),('okind',':u8'),('oslot',':u32'),('ogen',':u60'),('filter',':bool'),('funit',':u60'),('fcounter',':u60'),('ufirst',':u60'),('ulast',':u60'),('wire-run',':u60')]+[(f'hash-{i}',':u32') for i in range(8)]

def declarations(prefix):
 return '\n  '.join(f'({prefix}{name} {typ})' for name,typ in FIELDS)

def begin_bindings(kind):
 run={'allocation':'counter','tag':'catalog-tag'}
 overlay={'slot':'slot','gen':'gen','entries':'count','okind':'okind','oslot':'oslot','ogen':'ogen'}
 out=[]
 for name,_ in FIELDS:
  if kind=='run':value=f'(fn2-run-installed-{run.get(name,name)} row fn2-run-installed)'
  elif name in overlay:value=f'(fn2-overlays-{overlay[name]} row fn2-overlays)'
  else:value='0'
  out.append(f'       (old-{name} {value})')
 return '\n'.join(out)

def emit_bindings():
 return '\n'.join(f'        (catalog-old-{name} (fn2-checkpoint-metadata-old-{name} 0 fn2-checkpoint-metadata))' for name,_ in FIELDS)
