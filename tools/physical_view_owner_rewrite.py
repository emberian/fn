"""Project physical decoded-view ownership at the actual delivery boundary."""
import lisp_rewrite as lr
TARGET={'range.lisp':'fn2-range-advance-run','machines-c-read.lisp':'fn2-rd-lookup'}
def project(name,source):
 found=lr.match('(defun '+TARGET[name]+' ?*body)',lr.parse(source).forms)
 if len(found)!=1:raise ValueError('missing actual view constructor')
 f=found[0].node;edits=[]
 if name=='range.lisp':
  m=lr.match('(:entry ?*body)',[f])
  if len(m)!=1 or lr.match('(fn2-run-cursors-physical ?*args)',[m[0].node]):raise ValueError('view already projected')
  assignments='\n'.join('                ('+field+' (fn2-run-cursors-'+field+' c fn2-run-cursors))' for field in ('okind','oslot','ogen'))
  new='''(:entry
       (if (not (and (natp c) (< c (fn2-run-cursors-rows fn2-run-cursors))))
        (mv :bounds fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
        ; Physical decoded octets belong to this verified cursor page, not
        ; the immutable installed root's former producer.
        (let ((fn2-range-sources
               (if (equal (fn2-run-cursors-physical c fn2-run-cursors) 1)
                (fn2-range-sources-put s (state *fn2-range-state-head*)
'''+assignments+''')
                (fn2-range-sources-set-state s *fn2-range-state-head* fn2-range-sources))))
         (mv :ok fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))))'''
  edits.append((m[0].start,m[0].end,new))
 else:
  b=f.items[-1]
  binds=b.items[1].items
  last=[x for x in binds if isinstance(x,lr.Lst) and x.items and getattr(x.items[0],'low','')=='fn2-reads']
  if len(last)!=1:raise ValueError('missing unique READ entry construction')
  if 'physical-entry' in source[f.start:f.end]:raise ValueError('view already projected')
  predicate='''(physical-entry (and (eq code :ok) (< tx (fn2-run-cursors-rows fn2-run-cursors))
                           (equal erow (+ b0 *fn2-read-heads* *fn2-run-reader-entry*))
                           (equal (fn2-run-cursors-physical tx fn2-run-cursors) 1)))
      '''
  edits.append((last[0].start,last[0].start,predicate))
  for key,field,constant in [('ek','okind','kind'),('es','oslot','slot'),('eg','ogen','gen')]:
   m=lr.match('('+key+' *fn2-idc-owner-'+constant+'*)',[last[0]])
   if len(m)!=1:raise ValueError('missing unique READ view owner '+key)
   edits.append((m[0].start,m[0].end,'('+key+' (if physical-entry (fn2-run-cursors-'+field+' tx fn2-run-cursors) *fn2-idc-owner-'+constant+'*))'))
 return lr.write(source,edits)
