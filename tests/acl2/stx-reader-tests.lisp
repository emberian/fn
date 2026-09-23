; Historical reader projection: a Store verdict is selected by Message-ID,
; pinned with the archive, and rendered without consulting a live keyring.
(in-package "ACL2")
(include-book "../../books/stx-reader")

(defconst *fn-stx-reader-principal*
  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
    16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31))
(defconst *fn-stx-reader-v1*
  (fn-stx-make-verdict :verified *fn-stx-reader-principal* 7))
(defconst *fn-stx-reader-legacy*
  (fn-stx-make-verdict :verified '(1 2 3) 6))
(defconst *fn-stx-reader-unverified*
  (fn-stx-make-verdict :unverified :signature 8))

(assert-event
 (equal (fn-stx-reader-verdict "<v1@fn>"
                               (list (cons "<legacy@fn>" *fn-stx-reader-legacy*)
                                     (cons "<v1@fn>" *fn-stx-reader-v1*)))
        (append *fn-stx-token-verified*
                (cons 32
                      (append (fn-stx-hex-octets *fn-stx-reader-principal*)
                              (fn-stx-keyring-suffix 7))))))

(assert-event
 (equal (fn-stx-reader-verdict "<legacy@fn>"
                               (list (cons "<legacy@fn>" *fn-stx-reader-legacy*)))
        (append *fn-stx-token-verified*
                (cons 32 (append *fn-stx-token-legacy*
                                 (fn-stx-keyring-suffix 6))))))

(assert-event
 (equal (fn-stx-reader-verdict "<bad@fn>"
                               (list (cons "<bad@fn>" *fn-stx-reader-unverified*)))
        (fn-stx-verified-item *fn-stx-reader-unverified*)))

(assert-event
 (equal (fn-stx-reader-verdict "<missing@fn>" nil)
        (append *fn-stx-token-absent*
                (cons 32 *fn-stx-token-no-record*))))

; A newer Store snapshot does not alter the value already pinned in a
; connection.  These two immutable lists deliberately disagree for one ID.
(assert-event
 (let* ((pinned (list (cons "<v1@fn>" *fn-stx-reader-v1*)))
        (later (cons (cons "<v1@fn>" *fn-stx-reader-unverified*) pinned)))
   (and (equal (fn-stx-reader-verdict "<v1@fn>" pinned)
               (fn-stx-reader-item *fn-stx-reader-v1*))
        (not (equal (fn-stx-reader-verdict "<v1@fn>" pinned)
                    (fn-stx-reader-verdict "<v1@fn>" later))))))
