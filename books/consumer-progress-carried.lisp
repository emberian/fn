; Sole fixed5 CP/account metadata: first four field meanings unchanged,
; trailing field is the maintained CP-entry list annotation. The guards here
; check only fixed metadata shape, never a retained graph. Old4 is unavailable.
; Each authority/config decision runs once; entry annotations stay literal.
(in-package "ACL2")
(include-book "consumer-account-initial")
(include-book "consumer-config-authority")

(defun fn-cpm-metadatap (metadata)
 (declare (xargs :guard t))
 (and (eq (fn-cp-nth 0 metadata) :account-carries)
      (consp (ec-call (nthcdr 4 metadata)))
      (null (ec-call (nthcdr 5 metadata)))))

(defun fn-cpm-account4 (metadata)
 (declare (xargs :guard t))
 (and metadata
      (list (fn-cp-nth 0 metadata) (fn-cp-nth 1 metadata)
            (fn-cp-nth 2 metadata) (fn-cp-nth 3 metadata))))

(defun fn-cpm-metadata5 (account4 entries-metadata)
 (declare (xargs :guard t))
 (and account4
      (list (fn-cp-nth 0 account4) (fn-cp-nth 1 account4)
            (fn-cp-nth 2 account4) (fn-cp-nth 3 account4) entries-metadata)))

(defun fn-cpm-initial (history incarnation frontier hn in)
 (declare (xargs :guard t))
 (mv-let (cp account4) (fn-caac-initial history incarnation frontier hn in)
  (mv cp (fn-cpm-metadata5 account4 nil))))

(defun fn-cpm-authority-step (cp event metadata)
 (declare (xargs :guard t))
 (if (not (fn-cpm-metadatap metadata))
     (mv '(:refused :consumer-metadata-unavailable) metadata nil)
  (mv-let (one account4 rootcarry)
    (fn-caac-step cp event (fn-cpm-account4 metadata))
    (if (eq (car one) :ok)
        (mv one (fn-cpm-metadata5 account4 (fn-cp-nth 4 metadata)) rootcarry)
      (mv one metadata rootcarry)))))

(defun fn-cpm-config-preflight (cp metadata)
 (declare (xargs :guard t))
 (if (null cp) (fn-cca-preflight cp nil)
  (if (not (fn-cpm-metadatap metadata))
      '(:refused :consumer-metadata-unavailable)
    (let ((one (fn-cca-preflight cp (fn-cpm-account4 metadata))))
     (if (eq (car one) :ok)
         (list :ok (fn-cp-nth 1 one)
               (fn-cpm-metadata5 (fn-cp-nth 2 one) (fn-cp-nth 4 metadata)))
       one)))))

(in-theory (disable fn-cpm-metadatap fn-cpm-account4 fn-cpm-metadata5
                    fn-cpm-initial fn-cpm-authority-step fn-cpm-config-preflight))
