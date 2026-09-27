; fn: the served fold over a span of the octet buffer, one framed event at a
; time (D27; REP-012; PKT-479).
;
; books/served-span.lisp fn-scar-feed-span, the fold host/owner-host.lisp
; fn-owner-chunk-span reaches, stepped fn-scar-feed-byte once per octet: per
; octet a new wire state, a new twelve-field connection
; (fn-served-conn-with-wire), a served result and a counted record, and a
; non-tail frame -- lane post-alloc measured ~1.1 MB of a 2.2 MB owner POST of
; 2 KiB there (sb-sprof :alloc, 2026-09-27).  fn-scar-scan-span is the same
; fold taken one framed event at a time: books/wire-scan.lisp fn-wire-scan
; runs the wire machine over the range until its first event (a line at a
; time, one cons per octet of the retained line), and the connection is
; rebuilt and the event dispatched once per event, as fn-scar-feed-byte
; dispatches it.  The PKT-600 yield after a submission and the stops at a
; closed wire and a TLS handshake are the byte fold's.
;
; KEYSTONE fn-scar-scan-span-is-feed-counted (no hypothesis): the span scan IS fn-scar-feed-counted over the range's octets
; (fn-oct-slice-list i end), hence (books/served-span.lisp
; fn-scar-feed-span-is-feed-counted) the byte fold fn-scar-feed-span the
; served read is specified by.  books/served-span.lisp fn-scar-step-span-core
; runs this function as the executable of fn-scar-feed-span (mbe).

(in-package "ACL2")
(include-book "served-carried")
(include-book "wire-scan")

(defun fn-scar-scan-span (conn i end live trie arts fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-scar-dispatch-events
                                                      fn-served-submission)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let* ((w (fn-wire-scan (fn-served-conn-wire conn) i end fn-octets))
           (next (fn-wsp-next w))
           (here (fn-scar-dispatch-events
                  (fn-served-conn-with-wire conn (fn-wsp-state w))
                  (fn-wsp-events w) live trie arts)))
      ;; PKT-600: yield after the event that completed a submission; the host
      ;; re-enters at i + consumed.
      (if (fn-served-submission (fn-served-result-effects here))
          (fn-served-counted-make
           (- next i)
           (fn-served-make-result (fn-served-result-conn here)
                                  (fn-served-result-effects here)))
        (let* ((tail (fn-scar-scan-span (fn-served-result-conn here) next end
                                        live trie arts fn-octets))
               (tail-result (fn-served-counted-result tail)))
          (fn-served-counted-make
           (+ (- next i) (fn-served-counted-consumed tail))
           (fn-served-make-result
            (fn-served-result-conn tail-result)
            (mbe :logic (append (fn-served-result-effects here)
                                (fn-served-result-effects tail-result))
                 :exec (fn-ag-append (fn-served-result-effects here)
                                     (fn-served-result-effects tail-result))))))))))

(defthm fn-scar-scan-span-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-scar-scan-span conn i end live trie arts fn-octets)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-scar-scan-span conn i end live trie arts fn-octets)
           :in-theory (e/d (fn-served-counted-make fn-served-counted-consumed)
                           (fn-scar-dispatch-events fn-wire-fast-statep)))))

(local
 (defthm fn-sscan-scan-preserves-fast-statep
   (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
            (fn-wire-fast-statep
             (fn-served-conn-wire
              (fn-served-result-conn
               (fn-scar-dispatch-events
                (fn-served-conn-with-wire
                 conn
                 (fn-wsp-state (fn-wire-scan (fn-served-conn-wire conn) i end
                                             fn-octets)))
                events live trie arts)))))
   :hints (("Goal" :in-theory (disable fn-scar-dispatch-events fn-wire-fast-statep)))))

(verify-guards fn-scar-scan-span
  :hints (("Goal"
           :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                           (fn-scar-dispatch-events fn-wire-fast-statep
                            fn-served-counted-consumed)))))

; -----------------------------------------------------------------------------
; The correspondence.

(local
 (defthm fn-sscan-with-wire-twice
   (equal (fn-served-conn-with-wire (fn-served-conn-with-wire conn w1) w2)
          (fn-served-conn-with-wire conn w2))
   :hints (("Goal" :in-theory (enable fn-served-conn-with-wire)))))

(local
 (defthm fn-sscan-handshaking-of-with-wire
   (equal (fn-served-tls-handshakingp (fn-served-conn-with-wire conn w))
          (fn-served-tls-handshakingp conn))
   :hints (("Goal" :in-theory (enable fn-served-tls-handshakingp)))))

(local
 (defthm fn-sscan-feed-byte-without-event-keeps-open
   (implies (and (not (equal (fn-wire-state-mode wire-state) :closed))
                 (not (consp (fn-wire-result-events
                              (fn-wire-feed-byte wire-state byte)))))
            (not (equal (fn-wire-state-mode
                         (fn-wire-result-state (fn-wire-feed-byte wire-state byte)))
                        :closed)))
   :hints (("Goal" :in-theory (enable fn-wire-feed-byte fn-wire-after-line
                                      fn-wire-close)))))

(local
 (defthm fn-sscan-slice-open
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n fn-octets)
                   (cons (fn-octets-get i fn-octets)
                         (fn-oct-slice-list (1+ i) n fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sscan-slice-empty
   (implies (or (not (natp i)) (not (natp n)) (>= i n))
            (equal (fn-oct-slice-list i n fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sscan-dispatch-no-events
   (implies (not (consp events))
            (equal (fn-scar-dispatch-events conn events live trie arts)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-scar-dispatch-events conn events live trie arts))))))

(local
 (defthm fn-sscan-feed-counted-nil
   (equal (fn-scar-feed-counted conn nil live trie arts)
          (fn-served-counted-make 0 (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-scar-feed-counted conn nil live trie arts))))))

(local
 (defthm fn-sscan-feed-counted-cons
   (equal (fn-scar-feed-counted conn (cons b rest) live trie arts)
          (if (or (fn-served-closed-wirep (fn-served-conn-wire conn))
                  (fn-served-tls-handshakingp conn))
              (fn-served-counted-make 0 (fn-served-make-result conn nil))
            (let ((here (fn-scar-feed-byte conn b live trie arts)))
              (if (fn-served-submission (fn-served-result-effects here))
                  (fn-served-counted-make
                   1 (fn-served-make-result (fn-served-result-conn here)
                                            (fn-served-result-effects here)))
                (let* ((tail (fn-scar-feed-counted
                              (fn-served-result-conn here) rest live trie arts))
                       (tail-result (fn-served-counted-result tail)))
                  (fn-served-counted-make
                   (+ 1 (fn-served-counted-consumed tail))
                   (fn-served-make-result
                    (fn-served-result-conn tail-result)
                    (append (fn-served-result-effects here)
                            (fn-served-result-effects tail-result)))))))))
   :hints (("Goal" :expand ((fn-scar-feed-counted conn (cons b rest)
                                                  live trie arts))))))

(local
 (defun fn-sscan-ind (conn i end fn-octets)
   (declare (xargs :stobjs fn-octets :measure (nfix (- end i))
                   :verify-guards nil))
   (if (or (not (natp i)) (not (natp end)) (>= i end))
       (list conn i end)
     (let ((r (fn-wire-feed-byte (fn-served-conn-wire conn)
                                 (fn-octets-get i fn-octets))))
       (if (consp (fn-wire-result-events r))
           (list conn i end)
         (fn-sscan-ind (fn-served-conn-with-wire conn (fn-wire-result-state r))
                       (+ 1 i) end fn-octets))))))

; The byte fold over [i, end) splits at the wire's first event: every octet
; before it only moves the wire, and the event is dispatched where
; fn-scar-feed-byte dispatches it.
(local
 (defthm fn-sscan-feed-counted-splits
   (implies (and (not (fn-served-closed-wirep (fn-served-conn-wire conn)))
                 (not (fn-served-tls-handshakingp conn))
                 (natp i) (natp end) (< i end))
            (equal
             (fn-scar-feed-counted conn (fn-oct-slice-list i end fn-octets)
                                   live trie arts)
             (let* ((w (fn-wire-span-fold (fn-served-conn-wire conn) i end
                                          fn-octets))
                    (next (fn-wsp-next w))
                    (here (fn-scar-dispatch-events
                           (fn-served-conn-with-wire conn (fn-wsp-state w))
                           (fn-wsp-events w) live trie arts)))
               (if (fn-served-submission (fn-served-result-effects here))
                   (fn-served-counted-make
                    (- next i)
                    (fn-served-make-result (fn-served-result-conn here)
                                           (fn-served-result-effects here)))
                 (let* ((tail (fn-scar-feed-counted
                               (fn-served-result-conn here)
                               (fn-oct-slice-list next end fn-octets)
                               live trie arts))
                        (tail-result (fn-served-counted-result tail)))
                   (fn-served-counted-make
                    (+ (- next i) (fn-served-counted-consumed tail))
                    (fn-served-make-result
                     (fn-served-result-conn tail-result)
                     (append (fn-served-result-effects here)
                             (fn-served-result-effects tail-result)))))))))
   :hints (("Goal" :induct (fn-sscan-ind conn i end fn-octets)
            :in-theory (e/d (fn-scar-feed-byte fn-served-closed-wirep
                             fn-served-counted-make fn-served-counted-consumed
                             fn-served-counted-result)
                            (fn-wire-feed-byte fn-wire-fast-statep
                             fn-scar-dispatch-events fn-scar-feed-counted
                             fn-served-submission fn-served-tls-handshakingp))
            :expand ((fn-wire-span-fold (fn-served-conn-wire conn)
                                        i end fn-octets))))))

; KEYSTONE (PKT-479), no hypothesis: the event-at-a-time scan the served
; read runs is the carried byte fold over the range's octets, on every
; connection and every range.
(defthm fn-scar-scan-span-is-feed-counted
  (equal (fn-scar-scan-span conn i end live trie arts fn-octets)
         (fn-scar-feed-counted conn (fn-oct-slice-list i end fn-octets)
                               live trie arts))
  :hints (("Goal" :induct (fn-scar-scan-span conn i end live trie arts fn-octets)
           :in-theory (e/d (fn-scar-scan-span fn-served-counted-make
                            fn-served-counted-consumed fn-served-counted-result)
                           (fn-scar-dispatch-events fn-wire-fast-statep
                            fn-scar-feed-counted fn-sscan-feed-counted-cons
                            fn-sscan-slice-open
                            fn-served-submission fn-served-closed-wirep
                            fn-served-tls-handshakingp)))
          (and stable-under-simplificationp
               '(:expand ((fn-scar-feed-counted conn
                                                (fn-oct-slice-list i end fn-octets)
                                                live trie arts))))))

(in-theory (disable fn-scar-scan-span))
