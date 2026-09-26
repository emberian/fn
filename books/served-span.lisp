; fn: the owner read the host calls, over a range of the octet buffer
; (D27; REP-012; PRF-181).
;
; books/owner-served-carried.lisp closes the served fold at the owner:
; fn-scar-ocfg-read-tls-prefix is the read host/owner-host.lisp fn-owner-chunk
; calls with the socket observation AS A LIST (a 512-element cons list per
; socket read, coerced by host/native/owner.lisp fnn-octet-list).  This book is
; the same read over a range [i, end) of the octet buffer: host/owner-host.lisp
; fn-owner-chunk-span calls fn-scar-ocfg-read-span after
; host/native/owner.lisp fnn-owner-handle-chunk has filled the buffer once from
; the socket byte vector (fnn-octets-fill), so no octet of a read is a cons
; cell.  The served fold reads the range in place by index (fn-octets-get); the
; wire machine's read is books/wire-span.lisp fn-wire-feed-span.
;
; KEYSTONES:
;   fn-scar-feed-span-is-feed-counted (no hypothesis): the buffer fold IS the
;     carried counted fold fn-scar-feed-counted over the range's bytes
;     (fn-oct-slice-list i end), byte for byte;
;   fn-scar-ocfg-read-span-is-reference-under-ocl-relation: under the
;     configured owner's relation the span read is fn-ocfg-read-tls-prefix over
;     those octets, the reference read the list path already establishes as
;     correct.
; Every function is guard-verified.
;
; Reducing the per-byte connection rebuild to a per-FRAMED-EVENT rebuild (the
; wire machine already frames the whole body in one span; the served fold does
; not yet dispatch per span) is PKT-479, with the per-line wire index scan.

(in-package "ACL2")
(include-book "owner-served-carried")
(include-book "wire-span")

; -----------------------------------------------------------------------------
; The carried fold over a buffer range: fn-scar-feed-counted, reading the range
; by index instead of consuming a list.  Its shape is fn-scar-feed-counted's,
; byte for byte, so the correspondence below is a plain induction.

(defun fn-scar-feed-span (conn i end live trie arts fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :verify-guards nil))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let* ((here (fn-scar-feed-byte conn (fn-octets-get i fn-octets) live trie arts))
           (tail (fn-scar-feed-span (fn-served-result-conn here) (+ 1 i) end
                                    live trie arts fn-octets))
           (tail-result (fn-served-counted-result tail)))
      (fn-served-counted-make
       (+ 1 (fn-served-counted-consumed tail))
       (fn-served-make-result
        (fn-served-result-conn tail-result)
        (mbe :logic (append (fn-served-result-effects here)
                            (fn-served-result-effects tail-result))
             :exec (fn-ag-append (fn-served-result-effects here)
                                 (fn-served-result-effects tail-result))))))))

(defthm fn-scar-feed-span-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-scar-feed-span conn i end live trie arts fn-octets)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-scar-feed-span conn i end live trie arts fn-octets)
           :in-theory (e/d (fn-served-counted-make fn-served-counted-consumed)
                           (fn-scar-feed-byte fn-wire-fast-statep)))))

(local
 (defthm fn-scar-span-feed-preserves-fast-statep
   (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
            (fn-wire-fast-statep
             (fn-served-conn-wire
              (fn-served-result-conn
               (fn-served-counted-result
                (fn-scar-feed-span conn i end live trie arts fn-octets))))))
   :hints (("Goal" :induct (fn-scar-feed-span conn i end live trie arts fn-octets)
            :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                            (fn-scar-feed-byte fn-wire-fast-statep))))))

(verify-guards fn-scar-feed-span
  :hints (("Goal"
           :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                           (fn-scar-feed-byte fn-wire-fast-statep
                            fn-served-counted-consumed))
           :use ((:instance fn-scar-feed-byte-preserves-fast-statep
                            (byte (fn-octets-get i fn-octets)))))))

; -----------------------------------------------------------------------------
; The correspondence: the buffer fold is the list counted fold over the range.

(local
 (defthm fn-scar-span-slice-open
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n fn-octets)
                   (cons (fn-octets-get i fn-octets)
                         (fn-oct-slice-list (1+ i) n fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-scar-span-slice-empty
   (implies (or (not (natp i)) (not (natp n)) (>= i n))
            (equal (fn-oct-slice-list i n fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

; KEYSTONE: no hypothesis.  Both folds step one byte -- the buffer's cell i is
; the slice's car, the buffer range [i+1, end) is the slice's cdr -- so a plain
; induction on the range gives the equality; a closed wire and a handshaking
; session answer alike on both sides.
(defthm fn-scar-feed-span-is-feed-counted
  (equal (fn-scar-feed-span conn i end live trie arts fn-octets)
         (fn-scar-feed-counted conn (fn-oct-slice-list i end fn-octets)
                               live trie arts))
  :hints (("Goal" :induct (fn-scar-feed-span conn i end live trie arts fn-octets)
           :in-theory (e/d (fn-scar-feed-span fn-scar-feed-counted
                            fn-served-counted-make fn-served-counted-consumed
                            fn-served-counted-result)
                           (fn-scar-feed-byte fn-wire-fast-statep)))))

(local
 (defthm fn-scar-span-slice-len
   (implies (and (natp i) (natp n))
            (equal (len (fn-oct-slice-list i n fn-octets)) (nfix (- n i))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(in-theory (disable fn-scar-feed-span))

; -----------------------------------------------------------------------------
; The read entries, each the shape of its list twin.

(defun fn-scar-step-span-core (conn i end live trie arts fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))))
  (let* ((wire (fn-served-conn-wire conn))
         (fed (fn-scar-feed-span conn i end live trie arts fn-octets))
         (result (fn-served-counted-result fed))
         (wire2 (fn-served-conn-wire (fn-served-result-conn result))))
    (fn-served-counted-make
     (fn-served-counted-consumed fed)
     (fn-served-make-result
      (fn-served-result-conn result)
      (mbe :logic
           (append (fn-served-result-effects result)
                   (if (and (not (fn-served-closed-wirep wire))
                            (fn-served-closed-wirep wire2))
                       (list (fn-nntp-close-effect))
                     nil))
           :exec
           (fn-ag-append
            (fn-served-result-effects result)
            (if (and (not (fn-served-closed-wirep wire))
                     (fn-served-closed-wirep wire2))
                (list (fn-nntp-close-effect))
              nil)))))))

(defthm fn-scar-step-span-core-is-step-counted-core
  (equal (fn-scar-step-span-core conn i end live trie arts fn-octets)
         (fn-scar-step-counted-core conn (fn-oct-slice-list i end fn-octets)
                                    live trie arts))
  :hints (("Goal" :in-theory (e/d (fn-scar-step-span-core fn-scar-step-counted-core)
                                  (fn-scar-feed-counted fn-served-closed-wirep)))))

(defun fn-scar-step-span-fast (conn i end live trie arts fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))))
  (if (not (fn-wire-fast-statep (fn-served-conn-wire conn)))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (fn-scar-step-span-core conn i end live trie arts fn-octets)))

(defthm fn-scar-step-span-fast-is-step-counted-fast
  (equal (fn-scar-step-span-fast conn i end live trie arts fn-octets)
         (fn-scar-step-counted-fast conn (fn-oct-slice-list i end fn-octets)
                                    live trie arts))
  :hints (("Goal" :in-theory (e/d (fn-scar-step-span-fast fn-scar-step-counted-fast)
                                  (fn-scar-step-span-core fn-scar-step-counted-core
                                   fn-wire-fast-statep)))))

(in-theory (disable fn-scar-step-span-core fn-scar-step-span-fast))

(defun fn-scar-own-read-span (o id i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (live (fn-sn-node (fn-own-store o)))
        (trie (fn-own-view-index (fn-own-view o)))
        (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
    (if conn
        (let* ((counted
                 (fn-scar-step-span-fast
                  (fn-own-tls-served-conn o conn) i end live trie arts fn-octets))
               (result
                 (fn-scar-finish-read
                  o conn (fn-served-counted-result counted) live)))
          (fn-own-tls-make-result
           (fn-served-counted-consumed counted) (car result) (cdr result)))
      (fn-own-tls-make-result (nfix (- end i)) nil o))))

(defthm fn-scar-own-read-span-is-own-read-tls-prefix
  (implies (and (natp i) (natp end))
           (equal (fn-scar-own-read-span o id i end fn-octets)
                  (fn-scar-own-read-tls-prefix o id (fn-oct-slice-list i end fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-scar-own-read-span fn-scar-own-read-tls-prefix)
                                  (fn-scar-step-counted-fast fn-scar-finish-read
                                   fn-own-tls-served-conn)))))

; The function host/owner-host.lisp fn-owner-chunk-span calls.
(defun fn-scar-ocfg-read-span (oc id i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))))
  (let ((result (fn-scar-own-read-span (fn-ocfg-owner oc) id i end fn-octets)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed result)
     (fn-own-tls-result-effects result)
     (fn-ocfg-with-read-owner oc id (fn-own-tls-result-owner result)))))

(defthm fn-scar-ocfg-read-span-is-read-tls-prefix
  (implies (and (natp i) (natp end))
           (equal (fn-scar-ocfg-read-span oc id i end fn-octets)
                  (fn-scar-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-scar-ocfg-read-span fn-scar-ocfg-read-tls-prefix)
                                  (fn-scar-own-read-tls-prefix
                                   fn-scar-own-read-span)))))

; KEYSTONE for the host line: under the configured owner's relation and its
; view trie's correspondence, the span read is the reference read of the
; range's bytes, for every connection identifier and every range.
(defthm fn-scar-ocfg-read-span-is-reference-under-ocl-relation
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (natp i) (natp end))
           (equal (fn-scar-ocfg-read-span oc id i end fn-octets)
                  (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets))))
  :hints (("Goal" :in-theory (disable fn-scar-ocfg-read-span
                                      fn-scar-ocfg-read-tls-prefix
                                      fn-ocfg-read-tls-prefix fn-ocl-relation
                                      fn-scar-view-indexedp))))

; Preservation: the span read leaves the store, hence the premise, as it
; found them.
(defthm fn-scar-ocfg-read-span-keeps-store
  (implies (and (natp i) (natp end))
           (equal (fn-own-store
                   (fn-ocfg-owner
                    (fn-own-tls-result-owner
                     (fn-scar-ocfg-read-span oc id i end fn-octets))))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (disable fn-scar-ocfg-read-span
                                      fn-scar-ocfg-read-tls-prefix))))

(defthm fn-scar-ocfg-read-span-preserves-node-premise
  (implies (and (natp i) (natp end)
                (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
           (fn-node-statep
            (fn-sn-node
             (fn-own-store
              (fn-ocfg-owner
               (fn-own-tls-result-owner
                (fn-scar-ocfg-read-span oc id i end fn-octets)))))))
  :hints (("Goal" :in-theory (disable fn-scar-ocfg-read-span
                                      fn-scar-ocfg-read-tls-prefix fn-node-statep))))

(in-theory (disable fn-scar-own-read-span fn-scar-ocfg-read-span))
