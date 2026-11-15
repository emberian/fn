#!/usr/bin/env python3
"""Checked single-generator schema expansion for bounded upload continuations."""
def transform(s):
    states=['stream-init','stream-receiving','stream-stage','stream-write','stream-wrote','stream-block','stream-fence','stream-fenced','stream-final','stream-repack','stream-root-write','stream-root-wrote','stream-root-fence','stream-root-fenced']
    a=':draining :retired :uncertain)'; assert s.count(a)==1;s=s.replace(a, ':draining :retired :uncertain '+ ' '.join(':'+x for x in states)+')')
    a='(mstep :u8) (mdrain :u8) (stored-hashed :u60) (location-hashed :u8))';assert s.count(a)==1
    s=s.replace(a,'''(mstep :u8) (mdrain :u8) (stored-hashed :u60) (location-hashed :u8)
              ;; PEXT is the immutable first payload identity. ROOT is allocated
              ;; only for the final source manifest; promotion never changes MID.
              (rootext :link) (rootepoch :u60) (rootalloc :u60)
              (stream-end :u60) (stream-resets :u60) (stream-stage-used :u32)
              (stream-eof :bool) (stream-stored-finalized :bool) (stream-provisional :u32) (stream-repack :u32))''')
    a='(:draining :upload-row :chunk-window (:storage-window :while (lease :held))))';assert s.count(a)==1
    s=s.replace(a, a[:-1]+'\n'+ '\n'.join('         (:'+x+' :upload-row :chunk-window (:storage-window :while (lease :held)))' for x in states)+')')
    a='lgen lease ilen cepoch calloc cfree mfill munit mstep mdrain stored-hashed location-hashed))';assert s.count(a)==1
    s=s.replace(a,a[:-2]+' rootepoch rootalloc stream-end stream-resets stream-stage-used stream-eof stream-stored-finalized stream-provisional stream-repack))')
    a='(pext *fn2-none*) (lslot *fn2-none*) (cext *fn2-none*)';assert s.count(a)==1;s=s.replace(a,a+' (rootext *fn2-none*)')
    a='(:store-fence) (:store-fenced) (:sealed) (:aborting) (:draining) (:retired) (:uncertain))';assert s.count(a)==1
    s=s.replace(a,a[:-1]+' '+ ' '.join('(:'+x+')' for x in states)+')')
    return s
