; fn: the node's own web face -- the page keystones over the emitter the
; host runs (lane web-native, PRF-338; split from books/web-render.lisp for
; the per-book time budget).  Subject: fn-wr-emit, which
; books/web-session.lisp fn-wss-page calls for every page fn-web-step
; answers (host/native/web-host.lisp writes that buffer).

(in-package "ACL2")
(include-book "web-render")

; -----------------------------------------------------------------------------
; The keystones over the function the host runs (fn-wr-emit, called by
; books/web-session.lisp fn-wss-page for every page).

(defthm fn-wr-emit-writes-vocabulary-or-escaped
  ; KEYSTONE (PRF-338): the octets the emitter appends to the page buffer
  ; are the concatenation of pieces each of which is the renderer's own
  ; markup (*fn-wr-vocabulary*) or escaped text (fn-wr-safe-textp: no < > "
  ; ', every & an entity).
  (implies (and (true-listp fn-web-out) (fn-wr-segs-okp segs))
           (and (equal (fn-wr-emit segs fn-web-in fn-web-out)
                       (append fn-web-out (fn-wr-flat (fn-wr-pieces segs fn-web-in))))
                (fn-wr-pieces-okp (fn-wr-pieces segs fn-web-in))))
  :hints (("Goal" :in-theory (e/d (fn-wr-segs-okp) (fn-wr-emit fn-wr-pieces fn-wr-flat))
           :use ((:instance fn-wr-emit-is-seq)
                 (:instance fn-wr-seq-is-flat-pieces (in fn-web-in))
                 (:instance fn-wr-pieces-okp-of-okp-segs (in fn-web-in))))))

(local
 (defthm fn-wr-nth-take
   (implies (and (natp s) (natp n) (< s n))
            (equal (nth s (take n in)) (nth s in)))
   :hints (("Goal" :in-theory (enable nth take)))))

(local
 (defthm fn-wr-emit-span-take
   (implies (and (natp n) (natp e) (<= e n))
            (equal (fn-wr-emit-span s e (take n in) out) (fn-wr-emit-span s e in out)))
   :hints (("Goal" :induct (fn-wr-emit-span s e in out)
            :in-theory (disable fn-wr-emit-span-is-append fn-wr-escape-octet)))))

(local
 (defthm fn-wr-emit-unstuffed-take
   (implies (and (natp n) (natp e) (<= e n))
            (equal (fn-wr-emit-unstuffed s e b (take n in) out)
                   (fn-wr-emit-unstuffed s e b in out)))
   :hints (("Goal" :induct (fn-wr-emit-unstuffed s e b in out)
            :in-theory (disable fn-wr-emit-unstuffed-is-append fn-wr-escape-octet)))))

(local
 (defthm fn-wr-slice-take
   (implies (and (natp n) (natp e) (<= e n))
            (equal (fn-oct-slice-list s e (take n in)) (fn-oct-slice-list s e in)))
   :hints (("Goal" :induct (fn-oct-slice-list s e in) :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-wr-emit-decoded-take
   (implies (and (natp n) (natp e) (<= e n))
            (equal (fn-wr-emit-decoded s e (take n in) out) (fn-wr-emit-decoded s e in out)))
   :hints (("Goal" :in-theory (e/d (fn-wr-emit-decoded)
                                   (fn-wr-emit-decoded-is-append fn-wr-emit-span-is-append
                                    fn-wr-emit-list-is-append fn-wr-emit-span))))))

(local
 (defthm fn-wr-emit-take-natp
   (implies (and (fn-wr-segsp segs) (natp n) (fn-wr-segs-within segs n))
            (equal (fn-wr-emit segs (take n in) out) (fn-wr-emit segs in out)))
   :hints (("Goal" :induct (fn-wr-emit segs in out)
            :in-theory (e/d (fn-wr-segsp fn-wr-segs-within)
                            (fn-wr-emit-is-seq fn-wr-emit-span-is-append
                             fn-wr-emit-unstuffed-is-append fn-wr-emit-span
                             fn-wr-emit-unstuffed fn-wr-emit-decoded
                             fn-wr-emit-decoded-is-append))))))

(local
 (defthm fn-wr-segs-within-nfix
   (equal (fn-wr-segs-within segs (nfix n)) (fn-wr-segs-within segs n))
   :hints (("Goal" :in-theory (enable fn-wr-segs-within)))))

(defthm fn-wr-emit-reads-only-its-spans
  ; KEYSTONE (PRF-338): identical input, identical octets -- the emitter
  ; reads the reply buffer only below its segments' highest span end N.
  (implies (and (fn-wr-segsp segs) (fn-wr-segs-within segs n))
           (equal (fn-wr-emit segs (take n fn-web-in) fn-web-out)
                  (fn-wr-emit segs fn-web-in fn-web-out)))
  :hints (("Goal" :use ((:instance fn-wr-emit-take-natp (n (nfix n)) (in fn-web-in)
                                   (out fn-web-out)))
           :in-theory (disable fn-wr-emit-take-natp fn-wr-emit fn-wr-segsp fn-wr-segs-within))))
