#!/usr/bin/env python3
"""Lift the sole actual C promise release body to a private summary-row helper."""
from pathlib import Path
import re
from lisp_rewrite import parse,match,write
NAME='fn2-checkpoint-cbase-release-step'
NEW='fn2-checkpoint-cbase-row-release-step'
def rewrite(s):
 if '(defun '+NEW+' ' in s:return s
 h=match('(defun '+NAME+' ?*body)',parse(s).forms,deep=False)[0]
 text=s[h.start:h.end].replace('(defun '+NAME+' (budget ','(defun '+NEW+' (budget s ',1)
 text=text.replace('(fn2-checkpoint-cbase-identity-p ','(fn2-checkpoint-cbase-row-identity-p s ')
 text=re.sub(r'(\(fn2-checkpoint-summary-[\w-]+) 0 ',r'\1 s ',text)
 text=text.replace('(fn2-checkpoint-summary-retire-begin ','(fn2-checkpoint-summary-row-retire-begin s ')
 text=text.replace('(fn2-checkpoint-summary-retire-row r ','(fn2-checkpoint-summary-row-retire-row s r ')
 inputs='fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoints fn2-extents fn2-ops fn2-alloc-edges'
 wrapper=f'''(defun {NAME} (budget {inputs})
 (declare (xargs :stobjs ({inputs}) :guard (and '''+' '.join('('+x+'-wfp '+x+')' for x in inputs.split())+f''')))
 ({NEW} budget 0 {inputs}))'''
 m=match('(fn2-checkpoint-cbase-holds-preserves '+NAME+' ?*body)',parse(s).forms,deep=False)[0]
 contract=s[m.start:m.end].replace(NAME,NEW,1).replace('(budget fn2-checkpoint-summary','(budget s fn2-checkpoint-summary',1)
 carriers=inputs.split()
 # Actual readonly and output type domains are explicit, alongside WFP.
 contract=contract.replace(':hyps (',':hyps ('+' '.join('('+x+'p '+x+')' for x in carriers)+' ',1)
 return write(s,[(h.start,h.end,text+'\n'+wrapper),(m.start,m.start,contract+'\n')])
if __name__=='__main__':
 p=Path('books/checkpoint-cbase-release.lisp');s=p.read_text();p.write_text(rewrite(s))
