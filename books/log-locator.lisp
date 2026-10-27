; books/log-locator.lisp -- the durable log locator (LC, D-LC-1; owner L).
; loc0 = the durable segment id (u64, allocated monotonically, never reused).
; loc1 = offset * 2^32 + len: the SERVED wire range of the article inside its record.
(in-package "ACL2")

(defun fn-locp (loc0 loc1)
  (declare (xargs :guard t))
  (and (unsigned-byte-p 64 loc0)
       (unsigned-byte-p 64 loc1)))

(defun fn-loc-make (seg off len)
  (declare (xargs :guard (and (unsigned-byte-p 64 seg)
                              (unsigned-byte-p 32 off)
                              (unsigned-byte-p 32 len))))
  (mv (nfix seg)
      (+ (* (nfix off) 4294967296) (nfix len))))

(defun fn-loc-segment (loc0 loc1)
  (declare (xargs :guard (fn-locp loc0 loc1))
           (ignore loc1))
  (nfix loc0))

(defun fn-loc-offset (loc0 loc1)
  (declare (xargs :guard (fn-locp loc0 loc1))
           (ignore loc0))
  (floor (nfix loc1) 4294967296))

(defun fn-loc-len (loc0 loc1)
  (declare (xargs :guard (fn-locp loc0 loc1))
           (ignore loc0))
  (mod (nfix loc1) 4294967296))

(encapsulate ()
  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm fn-loc-accessors-of-make
    (implies (and (unsigned-byte-p 64 seg)
                  (unsigned-byte-p 32 off)
                  (unsigned-byte-p 32 len))
             (mv-let (loc0 loc1) (fn-loc-make seg off len)
               (and (fn-locp loc0 loc1)
                    (equal (fn-loc-segment loc0 loc1) seg)
                    (equal (fn-loc-offset loc0 loc1) off)
                    (equal (fn-loc-len loc0 loc1) len)))))

  (defthm fn-loc-make-of-accessors
    (implies (fn-locp loc0 loc1)
             (and (unsigned-byte-p 32 (fn-loc-offset loc0 loc1))
                  (unsigned-byte-p 32 (fn-loc-len loc0 loc1))
                  (equal (fn-loc-make (fn-loc-segment loc0 loc1)
                                      (fn-loc-offset loc0 loc1)
                                      (fn-loc-len loc0 loc1))
                         (mv loc0 loc1))))))

; D-LC-1 as a named invariant (L21, approved by main 10-13 ~07:20). Lives in books/log-locator.lisp (L's base book,
; no includes beyond local arithmetic), so LB's log-verified-map / catalog-columns cite it by including log-locator.
; KEYS is the verified map's key list (fn-lb-vmap-index: conses (segment . offset) under ruling (B)).
; SEGS is the fn-lb-log-model-segsp shape: entries (id octets entries).
; An id is "allocated" iff below NEXT-ID, or equal to it once the exhausted bit is set (the max-u64 last allocation,
; fn-lc-allocator-refuses-before-wraparound). A fresh allocation happens only when not exhausted and returns NEXT-ID.

(defun fn-lc-id-allocatedp (id next-id exhaustedp)
  (declare (xargs :guard t))
  (and (natp id) (natp next-id)
       (or (< id next-id)
           (and exhaustedp (equal id next-id)))))

(defun fn-lc-seg-ids-allocatedp (segs next-id exhaustedp)
  (declare (xargs :guard t))
  (if (consp segs)
      (and (consp (car segs))
           (fn-lc-id-allocatedp (car (car segs)) next-id exhaustedp)
           (fn-lc-seg-ids-allocatedp (cdr segs) next-id exhaustedp))
    t))

(defun fn-lc-key-ids-allocatedp (keys next-id exhaustedp)
  (declare (xargs :guard t))
  (if (consp keys)
      (and (consp (car keys))
           (fn-lc-id-allocatedp (car (car keys)) next-id exhaustedp)
           (fn-lc-key-ids-allocatedp (cdr keys) next-id exhaustedp))
    t))

(defun fn-lc-segment-ids-below-next (next-id exhaustedp segs keys)
  (declare (xargs :guard t))
  (and (natp next-id) (booleanp exhaustedp)
       (fn-lc-seg-ids-allocatedp segs next-id exhaustedp)
       (fn-lc-key-ids-allocatedp keys next-id exhaustedp)))
