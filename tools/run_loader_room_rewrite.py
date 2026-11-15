"""Use the canonical allocator's actual ordinary reservable capacity."""
import lisp_rewrite as lr
def project(source):
 f=lr.match('(defun fn2-run-load-roomp ?*body)',lr.parse(source).forms)
 if len(f)!=1:raise ValueError('missing unique loader room predicate')
 calls=lr.match('(fn2-pool-class-countsi ?class fn2-pool)',[f[0].node])
 if len(calls)!=3:raise ValueError('expected exact alias/nonalias room counters')
 return lr.write(source,[(m.node.items[0].start,m.node.items[0].end,'fn2-pool-reservable-count') for m in calls])
if __name__=='__main__':
 from pathlib import Path
 p=Path('books/run-physical-resources.lisp');p.write_text(project(p.read_text()))
