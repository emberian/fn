; Exact v1 report and cursor projection from a real composite constructor.
(in-package "ACL2")
(include-book "../../books/consumer-poll-projection")
(include-book "hybrid-store-tests")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")

(assert-event (equal (fn-cpj-max-cursor-octets) 346))
; D27 (signed-path): the widest composite the Store and poll frames carry,
; no longer the old 196,608 data cap.
(assert-event (equal (fn-cpj-max-event-octets) *fn-stxa-max-octets*))
(assert-event (< 196608 (fn-cpj-max-event-octets)))

(defconst *cpj-cursor*
  (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 3))
(defconst *cpj-cursor-bytes* (fn-cp-cursor-encode *cpj-cursor*))
(defconst *cpj-event-bytes* (fn-stxa-encode *hst-injected-event*))
(make-event `(defconst *cpj-projection*
               ',(fn-cpj-project *cpj-cursor-bytes* *cpj-event-bytes*)))

(assert-event
 (and (eq (car *cpj-projection*) :ok)
      (equal (nth 1 *cpj-projection*)
             '((1) (2) (3) (4) (5) 1 1 1 3))
      (equal (nth 2 *cpj-projection*) 2)
      (equal (nth 3 *cpj-projection*) 3)
      (equal (nth 4 *cpj-projection*)
             (fn-stxa-authored-id *hst-injected-event*))
      (equal (nth 6 *cpj-projection*) *hst-authored-source*)
      (equal (nth 7 *cpj-projection*) *hst-injected-received*)
      (equal (nth 8 *cpj-projection*) *hst-principal*)))

; A valid cursor from another prefix, a legacy parent, malformed bytes and
; a substituted authored identity cannot be projected as one poll result.
(assert-event
 (equal (fn-cpj-project
         (fn-cp-cursor-encode
          (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2))
         *cpj-event-bytes*)
        '(:refused :binding)))
(assert-event
 (equal (fn-cpj-project *cpj-cursor-bytes*
                        (fn-stxa-encode
                         (fn-stxa-make
                          2 3 4 4 (fn-stxa-profile *hst-injected-event*)
                          (fn-stxa-content-subject *hst-injected-event*)
                          (fn-stxa-article-record *hst-injected-event*)
                          (fn-stxa-verdict-event *hst-injected-event*))))
        '(:refused :binding)))
(assert-event (equal (fn-cpj-project *cpj-cursor-bytes* '(0 1 2))
                     '(:refused :codec)))
(assert-event
 (equal (fn-cpj-project *cpj-cursor-bytes*
                        (fn-stxa-encode *hst-carried-wrong-id*))
        '(:refused :authored-binding)))
(assert-event
 (equal (fn-cpj-project (make-list 347 :initial-element 0)
                        *cpj-event-bytes*)
        '(:refused :limit)))
(assert-event
 (equal (fn-cpj-project '(1 . 2) *cpj-event-bytes*)
        '(:refused :limit)))
(assert-event
 (equal (fn-cpj-project *cpj-cursor-bytes* '(1 . 2))
        '(:refused :limit)))
