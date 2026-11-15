"""Replace the private duplicate recipe with the canonical column generator."""
import lisp_rewrite as lr
NAME='fn2-release-replay-settlement-hyps'
def rewrite(text):
 parsed=lr.parse(text);edits=[];removed=[]
 for match in lr.match('(defun '+NAME+' ?*body)',parsed.forms,deep=False):
  node=match.node;removed.append((node.start,node.end));edits.append((node.start,node.end,''))
 for match in lr.match('('+NAME+' ?children)',parsed.forms):
  node=match.node
  if any(a<=node.start and node.end<=b for a,b in removed):continue
  child=match.captures['children']
  edits.append((node.start,node.end,'(fn2-columns-carrier-hyps (pairlis$ '+text[child.start:child.end]+' nil))'))
 return lr.write(text,edits),len(edits)
