;; Teeth for books/store-identity (Mini M4).
;;
;; fn-stid-reply-of-a-genesis-decodes: reachable, every antecedent and the
;; conclusion, on the genesis `init' writes, for no consumer state and for a
;; bootstrapped one.  Hypotheses removed, each answered by name:
;;   (fn-gen-p g)      a verdict that is no genesis -> refused no-genesis;
;;   (fn-cp-statep cs) a state with an empty history -> refused
;;                     consumer-state (never an empty identity field).
;; fn-stid-value-is-a-reply-value has no hypothesis: its witnesses are all
;; three answers decoding to themselves.  The line and the exit class of each.
(in-package "ACL2")
(include-book "../../books/store-identity")
(include-book "../../books/codec-attach")

(defconst *sitt-node* (make-list 32 :initial-element 7))
(defconst *sitt-revision* '(97 98 99))  ; abc

(make-event
 `(defconst *sitt-g* ',(fn-gen-record-for *sitt-node* '(1 2 3 4) 1000 *sitt-revision*
                                          *fn-bs-profile-development*)))
(make-event
 `(defconst *sitt-verdict*
    ',(fn-gen-open (fn-gen-octets-for *sitt-node* '(1 2 3 4) 1000 *sitt-revision*
                                      *fn-bs-profile-development*)
                   *fn-bs-profile-development*)))

(defconst *sitt-cs* (fn-cp-initial '(1 2) '(3 4 5) 0))

; Every antecedent.
(assert-event (fn-gen-p *sitt-g*))
(assert-event (equal *sitt-verdict* (list :genesis *sitt-g* (caddr *sitt-verdict*))))
(assert-event (fn-cp-statep *sitt-cs*))

; The conclusion, unbootstrapped and bootstrapped.
(assert-event
 (equal (fn-stid-reply-read (fn-stid-reply *sitt-verdict* nil '(118 49)))
        (list :accepted
              (list (fn-gen-format *sitt-g*) *sitt-node* (fn-gen-schema *sitt-g*)
                    (fn-gen-profile-digest *sitt-g*) '(:unbootstrapped nil)
                    *sitt-revision* '(118 49) *fn-wgx-file-digest*))))
(assert-event
 (equal (fn-stid-reply-read (fn-stid-reply *sitt-verdict* *sitt-cs* nil))
        (list :accepted
              (list (fn-gen-format *sitt-g*) *sitt-node* (fn-gen-schema *sitt-g*)
                    (fn-gen-profile-digest *sitt-g*) '(:bootstrapped ((1 2) (3 4 5)))
                    *sitt-revision* *fn-stid-unknown* *fn-wgx-file-digest*))))

; Hypothesis removed: no genesis.
(assert-event
 (equal (fn-stid-reply-read (fn-stid-reply '(:refused :profile-digest) *sitt-cs* nil))
        '(:refused :no-genesis)))
; Hypothesis removed: a consumer state whose history is empty.
(assert-event (not (fn-cp-statep (fn-cp-initial nil '(3 4 5) 0))))
(assert-event
 (equal (fn-stid-reply-read (fn-stid-reply *sitt-verdict* (fn-cp-initial nil '(3 4 5) 0) nil))
        '(:refused :consumer-state)))

; The request is recognized, and nothing longer is.
(assert-event (fn-stid-request-p (fn-stid-request)))
(assert-event (not (fn-stid-request-p (append (fn-stid-request) '(0)))))

; A reply with one octet changed is no reply the client reads.
(assert-event
 (let ((r (fn-stid-reply *sitt-verdict* *sitt-cs* nil)))
   (null (fn-stid-reply-read (update-nth 12 (mod (+ 1 (nth 12 r)) 256) r)))))

; The lines and exit classes.
(assert-event
 (equal (fn-stid-exit-class (fn-stid-value *sitt-verdict* *sitt-cs* nil)) :accepted))
(assert-event (equal (fn-stid-exit-class '(:refused :no-genesis)) :refused))
(assert-event (equal (fn-stid-exit-class nil) :fenced))
(assert-event
 (equal (fn-stid-line '(:refused :consumer-state))
        (fn-wgx-str "fn-store-identity-refused-v1 consumer-state")))
(assert-event
 (let ((line (fn-stid-line (fn-stid-value *sitt-verdict* nil nil))))
   (and (fn-wg-prefixp (fn-wgx-str "fn-store-identity-v1 format=") line)
        (search (append (fn-wgx-str " consumer=unbootstrapped created-revision=abc running-revision=unknown grammar=")
                        (fn-wgx-hex *fn-wgx-file-digest*))
                line))))
(assert-event
 (search (fn-wgx-str " consumer=bootstrapped history=0102 incarnation=030405 created-revision=abc")
         (fn-stid-line (fn-stid-value *sitt-verdict* *sitt-cs* nil))))

; The verb: one absolute control path; anything else is usage.
(assert-event (equal (fn-stid-cli-plan (list (fn-wgx-str "/n/control")))
                     (list :run (fn-wgx-str "/n/control"))))
(assert-event (equal (fn-stid-cli-plan (list (fn-wgx-str "n/control"))) '(:usage)))
(assert-event (equal (fn-stid-cli-plan nil) '(:usage)))
(assert-event (equal (fn-stid-cli-plan (list (fn-wgx-str "/n/control") (fn-wgx-str "x")))
                     '(:usage)))
(assert-event (equal (list (fn-stid-exit-code (fn-stid-value *sitt-verdict* nil nil))
                           (fn-stid-exit-code '(:refused :no-genesis))
                           (fn-stid-exit-code nil))
                     '(0 1 3)))
