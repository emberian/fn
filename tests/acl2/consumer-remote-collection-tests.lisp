(in-package "ACL2")
(include-book "../../books/consumer-remote-collection-buffer")
(include-book "../../books/consumer-remote-collection-client")
(include-book "../../books/records-attach")

(defun fn-crcol-test-semantic ()
 (declare (xargs :guard t))
 (let* ((ingress '(:authenticated (:remote-consumer :poll (97)) (112) (65) (78) 3 7))
        (a (fn-make-article "<a>" 1 '("a") '(("a" . 1)) t 0))
        (closed (fn-make-article "<closed>" 2 '("b") '(("b" . 1)) t 0))
        (b (fn-make-article "<b>" 3 '("a") '(("a" . 2)) t 0))
        (scanner (fn-crps-state '(source) nil nil '((97) (98)) 1 3 3 :read nil nil nil))
        (cfg (fn-inj-make-config-full t nil '((97) (98)) 4096
               (list nil nil nil '(("a" "a" "*" 3) ("a" "b" "*" 0))) nil))
        (view (list 3 3 (fn-make-state '("a" "b") nil nil 3 nil nil) nil nil nil
               '((:withdrawal "<a>" "<cause>" nil nil 0 nil)
                 (:withdrawal "<closed>" "<cause>" nil nil 0 nil)
                 (:withdrawal "<b>" "<cause>" nil nil 0 nil)) nil (list a closed b) nil)))
  (fn-cp-nth 1 (fn-crm-begin scanner '(1 1 0 "<cause>" 4 ("b")) ingress 9 cfg view))))

(defun fn-crcol-test-prepare (answer fuel stop-after-first fn-arena)
 (declare (xargs :stobjs fn-arena :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))
         (and stop-after-first (equal (fn-cp-nth 8 (fn-cp-nth 1 answer)) 1))) answer
  (let ((s (fn-cp-nth 1 answer)))
   (fn-crcol-test-prepare (fn-crcol-tick s (fn-cp-nth 1 s) (fn-cp-nth 2 s) 2 fn-arena)
                         (1- fuel) stop-after-first fn-arena))))

(defun fn-crcol-test-write (answer key scope fuel fn-arena fn-octets)
 (declare (xargs :stobjs (fn-arena fn-octets) :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) (mv answer fn-octets)
  (mv-let (next fn-octets) (fn-crcol-write-step (fn-cp-nth 1 answer) key scope 4096 fn-arena fn-octets)
   (fn-crcol-test-write next key scope (1- fuel) fn-arena fn-octets))))

; Real semantic filtering, interrupted preparation, both target writers,
; unchanged outer FNCT encoder -> actual version-aware client decoder.
(defun fn-crcol-fixture-multiple-with-located-boundary ()
 (declare (xargs :guard t))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena)
   (with-local-stobj fn-octets
    (mv-let (ok fn-arena fn-octets)
     (let* ((semantic (fn-crcol-test-semantic)) (key (fn-cp-nth 1 semantic))
            (scope (fn-cp-nth 2 semantic)) (start (fn-crcol-begin semantic 3 4096))
            (interrupted (fn-crcol-test-prepare start 800 t fn-arena))
            (held (fn-cp-nth 1 interrupted))
            (ready (fn-crcol-test-prepare interrupted 800 nil fn-arena))
            (writer (fn-crcol-write-begin ready key scope 3 4096 0 4096)))
      (mv-let (answer fn-octets) (fn-crcol-test-write writer key scope 200 fn-arena fn-octets)
       (let* ((bytes (fn-octets-list fn-octets))
              (a (fn-ncr-withdrawal-report '(60 97 62))) (b (fn-ncr-withdrawal-report '(60 98 62)))
              (cursor (fn-cp-cursor-encode (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2)))
              (reply (fn-ncl-poll-reply-encode :accepted cursor bytes))
              (located (fn-crcol-client-locate-begin '(input) 1 3 4096 fn-octets))
              (one (fn-crcol-client-locate-step (fn-cp-nth 1 located) '(input) fn-octets))
              (two (fn-crcol-client-locate-step (fn-cp-nth 3 one) '(input) fn-octets)))
        (mv (and (equal (fn-cp-nth 0 interrupted) :yield)
                 (equal (fn-cp-nth 8 held) 1) (null (fn-cp-nth 12 held))
                 (equal (fn-cp-nth 5 (fn-cp-nth 3 (fn-cp-nth 3 held))) 1)
                 (equal (fn-crcol-tick held key '(changed) 2 fn-arena)
                        '(:refused :remote-semantic-source-changed))
                 (equal (fn-cp-nth 0 ready) :collection-ready) (equal (fn-cp-nth 1 ready) 2)
                 (equal (fn-cp-nth 5 (fn-cp-nth 4 ready)) 2)
                 (equal answer (list :encoded (fn-cp-nth 4 ready)))
                 (equal bytes (fn-crcol-encode-reference (list a b) 3 4096))
                 (equal (fn-crcol-client-poll :poll reply 1 3 4096)
                    (list :consumer-poll-reports cursor '((:withdrawn (60 97 62)) (:withdrawn (60 98 62)))))
                 (equal (fn-crcol-client-poll :poll reply nil 3 4096) '(:refused :remote-report-version))
                 (equal (fn-crcol-client-report bytes 1 1 4096) '(:refused :remote-report-count))
                 (equal located (fn-crcol-client-locate-begin-reference '(input) 1 3 4096 bytes))
                 (equal one (fn-crcol-client-locate-step-reference (fn-cp-nth 1 located) '(input) bytes))
                 (equal (fn-crcol-client-locate-step (fn-cp-nth 1 located) '(changed) fn-octets)
                        '(:refused :consumer-source-changed))
                 (equal one (list :part 13 21 (list :remote-collection-locate '(input) 21 33 1)))
                 (equal two (list :part 25 33 (list :remote-collection-locate '(input) 33 33 0)))
                 (equal (fn-crcol-client-locate-step (fn-cp-nth 3 two) '(input) fn-octets) '(:complete))
                 (equal (fn-crcol-client-report (append bytes '(0)) 1 3 4096) '(:refused :remote-report-tail)))
            fn-arena fn-octets))))
     (mv ok fn-arena))) ok)))

(assert-event (fn-crcol-fixture-multiple-with-located-boundary))

; Explicit item/byte limits reject the WHOLE event, no first-target success.
(defun fn-crcol-fixture-limits ()
 (declare (xargs :guard t))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena)
   (let* ((semantic (fn-crcol-test-semantic))
          (items (fn-crcol-test-prepare (fn-crcol-begin semantic 1 4096) 800 nil fn-arena))
          (bytes (fn-crcol-test-prepare (fn-crcol-begin semantic 3 32) 800 nil fn-arena)))
    (mv (and (equal items '(:refused :oversize)) (equal bytes '(:refused :oversize))
             (equal (fn-crcol-begin semantic nil 4096) '(:refused :remote-report-profile))) fn-arena)) ok)))
(assert-event (fn-crcol-fixture-limits))

; Existing singleton variant stays byte-identical for an old-capability client.
(assert-event
 (let* ((bytes (fn-ncr-withdrawal-report '(60 97 62)))
        (wire (fn-crcol-encode-reference (list bytes) 1 4096)))
  (and (equal wire bytes) (equal (fn-crcol-client-report wire nil 1 4096)
                                '(:reports (:withdrawn (60 97 62)))))))

; Complete result + complete buffer effect teeth for unconditional boundary.
; The deliberately wrong expected effect is a mutation witness, no dropped
; hypothesis exists on this unconditional representation theorem.
(defun fn-crcol-fixture-boundary ()
 (declare (xargs :guard t))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena)
   (with-local-stobj fn-octets
    (mv-let (ok fn-arena fn-octets)
     (let* ((s (fn-crcol-write-state '(key) '(scope) :header '(70 78) nil nil 2 2 0 2 2 nil)))
      (mv-let (expected effect) (fn-crcol-write-reference s '(key) '(scope) 2 fn-arena nil)
       (mv-let (answer fn-octets) (fn-crcol-write-step s '(key) '(scope) 2 fn-arena fn-octets)
        (mv (and (equal answer expected) (equal (fn-octets-list fn-octets) effect)
                 (equal effect '(70)) (not (equal effect '(78)))) fn-arena fn-octets))))
     (mv ok fn-arena))) ok)))
(assert-event (fn-crcol-fixture-boundary))
