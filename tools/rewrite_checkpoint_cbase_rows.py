#!/usr/bin/env python3
"""Parameterize the sole catalog identity implementation; keep active aliases."""
from pathlib import Path
import re
from lisp_rewrite import parse,match,write
NAMES=['summary-word','hash-p','identity-p','held-p','promised-p']
PREFIX='fn2-checkpoint-cbase-'
def rewrite(s):
    if '(defun '+PREFIX+'row-identity-p ' in s:return s
    edits=[];parsed=parse(s)
    for short in NAMES:
        old=PREFIX+short;new=PREFIX+'row-'+short
        h=match('(defun '+old+' ?*body)',parsed.forms,deep=False)[0]
        text=s[h.start:h.end]
        if short=='summary-word':
            text='''(defun fn2-checkpoint-cbase-row-summary-word (r i fn2-checkpoint-summary)
 (declare (xargs :stobjs fn2-checkpoint-summary
 :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (natp r) (< r 2)
             (< r (fn2-checkpoint-summary-rows fn2-checkpoint-summary)) (natp i) (< i 8))))
 (fn2-checkpoint-summary-descriptor-word r i fn2-checkpoint-summary))'''
        else:
            for name in NAMES:text=re.sub(r'(?<![\w-])'+re.escape(PREFIX+name)+r'(?![\w-])',PREFIX+'row-'+name,text)
            # All actual generated summary field reads use explicit row zero.
            text=re.sub(r'(\(fn2-checkpoint-summary-[\w-]+) 0 fn2-checkpoint-summary',r'\1 r fn2-checkpoint-summary',text)
            if short=='hash-p':
                text=text.replace('(i c fn2-checkpoint-summary','(i r c fn2-checkpoint-summary')
                text=text.replace('(fn2-checkpoint-cbase-row-summary-word i ','(fn2-checkpoint-cbase-row-summary-word r i ')
                text=text.replace('(+ 1 i) c ','(+ 1 i) r c ')
                text=text.replace(':guard (and ',':guard (and (natp r) (< r 2) (< r (fn2-checkpoint-summary-rows fn2-checkpoint-summary)) ',1)
            else:
                text=text.replace('(fn2-checkpoint-summary fn2-checkpoint-cbase-holds)\n (declare','(r fn2-checkpoint-summary fn2-checkpoint-cbase-holds)\n (declare',1)
                text=text.replace('(fn2-checkpoint-cbase-row-identity-p fn2-checkpoint-summary','(fn2-checkpoint-cbase-row-identity-p r fn2-checkpoint-summary')
                text=text.replace('(fn2-checkpoint-cbase-row-hash-p 0 c ','(fn2-checkpoint-cbase-row-hash-p 0 r c ')
                if short=='identity-p':text=text.replace('(< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))','(natp r) (< r 2) (< r (fn2-checkpoint-summary-rows fn2-checkpoint-summary))',1)
        if short=='summary-word':
            wrapper='''(defun fn2-checkpoint-cbase-summary-word (i fn2-checkpoint-summary)
 (declare (xargs :stobjs fn2-checkpoint-summary
 :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary)) (natp i) (< i 8))))
 (fn2-checkpoint-cbase-row-summary-word 0 i fn2-checkpoint-summary))'''
        elif short=='hash-p':
            wrapper='''(defun fn2-checkpoint-cbase-hash-p (i c fn2-checkpoint-summary fn2-checkpoint-cbase-holds)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-cbase-holds)
 :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-cbase-holds-wfp fn2-checkpoint-cbase-holds)
             (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary)) (natp i) (<= i 8) (natp c) (< c (fn2-checkpoint-cbase-holds-rows fn2-checkpoint-cbase-holds)))))
 (fn2-checkpoint-cbase-row-hash-p i 0 c fn2-checkpoint-summary fn2-checkpoint-cbase-holds))'''
        else:
            wrapper=f'''(defun {old} (fn2-checkpoint-summary fn2-checkpoint-cbase-holds)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-cbase-holds)
 :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-cbase-holds-wfp fn2-checkpoint-cbase-holds))))
 ({new} 0 fn2-checkpoint-summary fn2-checkpoint-cbase-holds))'''
        edits.append((h.start,h.end,text+'\n'+wrapper))
    return write(s,edits)
if __name__=='__main__':
    p=Path('books/checkpoint-cbase-identity.lisp');old=p.read_text();new=rewrite(old);p.write_text(new)
    print('catalog identity row parameterization:', 'changed' if old!=new else 'unchanged')
