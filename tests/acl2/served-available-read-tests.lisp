; Actual generated command and parsed-event consumers, not formatter twins.
; Owner credit/capture and native endpoint composition remain separate debt.
(in-package "ACL2")
(include-book "served-available-commands-tests")
(include-book "../../books/served-available-read")

(defun cav-read-index (archive)
  (declare (xargs :mode :program))
  (fn-gidx-pin-with-control (fn-midx-build (fn-state-articles archive))
                            (fn-gidx-build (fn-state-articles archive)) nil))

(defun cav-read-agrees (line session raw index reference ref-index v fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((tokens (fn-nntp-tokenize line))
         (command (fn-scr-command-available session raw index nil nil tokens v fn-arena fn-cat))
         (event (fn-av-scr-step session raw index nil nil (list :command line) v fn-arena fn-cat))
         (expected (fn-nntp-step-pinned session reference ref-index nil nil
                                        (list :command line) fn-arena)))
    (and (fn-nntp-command-inputp line) (consp tokens)
         (fn-nntp-command-arguments-at-mostp tokens)
         (equal command event)
         (equal (fn-nntp-result-session command) (fn-nntp-result-session expected))
         (equal (fn-ovw-expand (fn-nntp-result-effects command) fn-arena fn-cat)
                (fn-ovw-expand (fn-nntp-result-effects expected) fn-arena fn-cat)))))

(defun cav-read-run (survivors fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat) (cav-av-fill 0 34 survivors fn-arena fn-cat)
      (let* ((raw (fn-make-state '("fn.available") '(("fn.available" . 35))
                                (cav-av-articles 34 34 fn-cat) 0 nil nil))
             (available (fn-nntp-available-archive raw fn-arena))
             (index (cav-read-index raw))
             (ai (cav-read-index available))
             (s (fn-nntp-make-session t "fn.available" 1 t))
             (last-s (fn-nntp-make-session t "fn.available" 34 t)))
        (mv
         (and (fn-statep raw) (fn-statep available)
              (cav-av-facts-completep (fn-state-articles raw) fn-arena fn-cat)
              (fn-gidx-pin-correspondencep index raw)
              (fn-gidx-pin-correspondencep ai available)
              (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles raw))
              (fn-midx-correspondencep (fn-gidx-pin-trie ai) (fn-state-articles available))
              (cav-read-agrees (fn-nntp-string-octets "GROUP fn.available") s raw index available ai 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "LISTGROUP") s raw index available ai 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "NEXT") s raw index available ai 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "LAST") last-s raw index available ai 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "LIST ACTIVE") s raw index available ai 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "LIST COUNTS") s raw index available ai 34 fn-arena fn-cat)
              ; Retained retrieval has the raw subject, including absent/tombstoned IDs.
              (cav-read-agrees (fn-nntp-string-octets "STAT 2") s raw index raw index 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "ARTICLE <1@available.test>") s raw index raw index 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "HEAD 1") s raw index raw index 34 fn-arena fn-cat)
              (cav-read-agrees (fn-nntp-string-octets "BODY 34") last-s raw index raw index 34 fn-arena fn-cat))
         fn-cat fn-arena)))))

(defun cav-read-local-cat (survivors fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (with-local-stobj fn-cat
    (mv-let (answer fn-cat fn-arena) (cav-read-run survivors fn-arena fn-cat)
      (mv answer fn-arena))))

(defun cav-read-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (cav-read-local-cat survivors fn-arena) answer)))

(assert-event (cav-read-local '(1 34)))
(assert-event (cav-read-local nil))

; Actual owner/credit endpoint on a constructed reader pin with complete facts.
; This is an executable route witness, not the selective owner refinement.
(defun cav-credit-pin-run (survivors fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat) (cav-av-fill 0 34 survivors fn-arena fn-cat)
      (let* ((raw (fn-make-state '("fn.available") '(("fn.available" . 35))
                                (cav-av-articles 34 34 fn-cat) 0 nil nil))
             (available (fn-nntp-available-archive raw fn-arena))
             (index (cav-read-index raw))
             (ai (cav-read-index available))
             (auth (fn-auth-open-session raw nil nil nil nil nil))
             (conn (fn-own-conn-make-indexed 0 34 nil (fn-wire-initial-state 512 4096)
                                            auth raw nil nil nil index))
             (view (fn-own-view-make-indexed 34 nil raw nil index))
             (owner (fn-own-make (fn-sn-make-v6 (fn-state-groups raw) 0 nil nil nil nil 0 nil nil 0 nil nil nil nil) view (list conn) 1 1 nil nil nil nil nil nil nil nil nil nil))
             (oc (fn-ocfg-make owner nil nil nil))
             (credits (fn-mcr-make 1048576 0 0 0 0 0 nil))
             (line (fn-nntp-string-octets "GROUP fn.available"))
             (wire (append line '(13 10)))
             (fn-octets (fn-octets-from-list wire fn-octets))
             (result (fn-av-mca-read-span credits oc nil 0 0 (len wire) nil nil 32 107552
                                         fn-octets fn-arena fn-cat))
             (expected (fn-nntp-step-pinned (fn-nntp-open-session raw) available ai nil nil
                                            (list :command line) fn-arena)))
        (mv (and (cav-av-facts-completep (fn-state-articles raw) fn-arena fn-cat)
                 (fn-gidx-pin-correspondencep index raw)
                 (fn-auth-session-consistentp auth raw)
                 (fn-mcr-fundedp credits)
                 (equal (fn-own-tls-result-consumed (car result)) (len wire))
                 (equal (fn-own-tls-result-effects (car result)) (fn-nntp-result-effects expected))
                 (equal (fn-nntp-session-group
                          (fn-auth-reader-session
                           (fn-own-conn-session
                            (fn-own-find-conn 0 (fn-own-conns
                             (fn-ocfg-owner (fn-own-tls-result-owner (car result))))))))
                        "fn.available")
                 (fn-mcr-fundedp (cdr result)))
            fn-octets fn-arena fn-cat)))))

(defun cav-credit-pin-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (with-local-stobj fn-arena
        (mv-let (answer fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (answer fn-octets fn-arena fn-cat)
              (cav-credit-pin-run survivors fn-octets fn-arena fn-cat)
              (mv answer fn-octets fn-arena)))
          (mv answer fn-octets)))
      answer)))

(assert-event (cav-credit-pin-local '(1 34)))
(assert-event (cav-credit-pin-local nil))
