; Bounded concrete FNCT identity-evidence export. No stored-data scan occurs here.
(in-package "ACL2")
(include-book "machines-c-read")
(include-book "fnct-pool")
(include-book "cns-kind")
(include-book "cursor")
(fn2-book-layer :e)
; Fail at admission if the schema grows: the exporter must then grow with
; its producer, rather than silently omit fields or impose a stored-data cap.
(assert-event (and (equal *fn2-identity-evidence-entry-num-fields* 11)
                   (<= *fn2-identity-evidence-entry-max-size* 400)))
(local (in-theory (disable fn2-fields-rows fn2-reads-rows fn2-pool-rows
 fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp)))

; Decode exactly one full entry, then retain only its nine ordered keys.
; Source ownership and the destination query ownership are independent.
(defun fn2-peer-export-resume (x fcrows base slot gen off len sk ss sg lease lgen ok os og
 fn2-reads fn2-id-decides fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-fields fn2-pool)
 :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp base) (<= (+ base *fn2-identity-evidence-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (natp off) (natp len) (<= len 400)
                    (unsigned-byte-p 8 ok) (unsigned-byte-p 32 os) (unsigned-byte-p 60 og)))
       (mv :bounds fn2-reads fn2-fields fn2-pool))
      ((mv code b0) (fn2-read-stripe x fcrows fn2-reads fn2-id-decides fn2-fields))
      ((unless (and (eq code :ok) (natp x) (< x (fn2-reads-rows fn2-reads))))
       (mv :bounds fn2-reads fn2-fields fn2-pool))
      ; Decoding and copying cannot overwrite fields still to be read.
      ((unless (or (<= (+ base *fn2-identity-evidence-entry-num-fields*) (+ b0 *fn2-read-lo*))
                   (<= (+ b0 *fn2-read-lo* 9) base)))
       (mv :bounds fn2-reads fn2-fields fn2-pool))
      ((mv code next fn2-fields)
       (fn2-identity-evidence-entry-decode base slot gen off (+ off len) sk ss sg fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (equal next (+ off len)))) (mv :format fn2-reads fn2-fields fn2-pool))
      ((mv code fn2-fields fn2-pool)
       (fn2-rd-key-save 0 9 1 base sk ss sg (+ b0 *fn2-read-lo*) 0 lease lgen ok os og fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-fields fn2-pool))
      (fn2-reads (fn2-reads-put x (qset 1) (qk ok) (qs os) (qg og))))
  (mv :ok fn2-reads fn2-fields fn2-pool)))
(fn2-rd-shape fn2-peer-export-resume
 (x fcrows base slot gen off len sk ss sg lease lgen ok os og fn2-reads fn2-id-decides fn2-fields fn2-pool)
 ((fn2-reads 1) (fn2-fields 2) (fn2-pool 3)) (fn2-reads fn2-id-decides fn2-fields fn2-pool)
 (fn2-read-stripe fn2-identity-evidence-entry-decode fn2-rd-key-save (:keep fn2-reads-rows)))

; Validate the delivered source at the current run version before reading its owner.
; All eleven fields are copied; the lease holds at most 250 name + 32 digest octets.
(defun fn2-peer-export-entry (x base slot gen ok os og
 fn2-reads fn2-run-installed fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-run-installed fn2-fields fn2-pool)
 :guard (and (fn2-reads-wfp fn2-reads) (fn2-run-installed-wfp fn2-run-installed)
             (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp base) (<= (+ base 12) (fn2-fields-rows fn2-fields))
                    (natp x) (< x (fn2-reads-rows fn2-reads)) (equal (fn2-reads-sid x fn2-reads) 1)))
       (mv :bounds 0 0 fn2-fields fn2-pool))
      ((mv code eb) (fn2-rd-entry-row x 0 fn2-reads fn2-run-installed fn2-fields))
      ((unless (eq code :ok)) (mv code 0 0 fn2-fields fn2-pool))
      ((unless (or (<= (+ base 12) eb) (<= (+ eb 11) base)))
       (mv :bounds 0 0 fn2-fields fn2-pool))
      ((mv code fn2-fields fn2-pool)
       (fn2-rd-key-save 0 11 1 eb (fn2-reads-ek x fn2-reads) (fn2-reads-es x fn2-reads)
        (fn2-reads-eg x fn2-reads) base 512 slot gen ok os og fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code 0 0 fn2-fields fn2-pool))
      (len (fn2-identity-evidence-entry-size base fn2-fields))
      ((unless (and (natp len) (<= len 400))) (mv :size 0 0 fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-set-value (+ base 11) len fn2-fields))
      ((mv code & fn2-pool)
       (fn2-peer-export-length-encode (+ base 11) slot gen 1024 ok os og fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code 0 0 fn2-fields fn2-pool))
      ((mv code end fn2-pool)
       (fn2-identity-evidence-entry-encode base slot gen 1026 ok os og fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (equal end (+ 1026 len)))) (mv :format 0 0 fn2-fields fn2-pool)))
  (mv :ok 1024 (+ 2 len) fn2-fields fn2-pool)))
(fn2-rd-shape fn2-peer-export-entry
 (x base slot gen ok os og fn2-reads fn2-run-installed fn2-fields fn2-pool)
 ((fn2-fields 3) (fn2-pool 4)) (fn2-reads fn2-run-installed fn2-fields fn2-pool)
 (fn2-rd-entry-row fn2-rd-key-save fn2-identity-evidence-entry-size fn2-peer-export-length-encode
  fn2-identity-evidence-entry-encode fn2-reads-sid fn2-reads-ek fn2-reads-es fn2-reads-eg))

(fn2-fnct-def-result fn2-peer-export-put-result fn2-peer-export-result
 (cut more nextoff nextlen count ioff ilen)
 ((version *fn2-peer-export-version*) (interpretation *fn2-peer-export-interpretation*)
  (coverage *fn2-peer-export-coverage-local*) (cut cut) (stop more)
  (next :ref nextoff nextlen) (count count) (entries :ref ioff ilen)))

(defmacro fn2-peer-export-core-events ()
 '(progn
   ; Reserve the bounded workspace once, before the first scan or resume.
   (defun fn2-peer-export-pad-core (slot gen ok os og fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-pool)
     (fn2-cursor-pool-pad 1024 slot gen ok os og fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-peer-export-pad-core
    (slot gen ok os og fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-peer-export-resume-core (x base slot gen off len sk ss sg lease lgen ok os og fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core))
                (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-fields fn2-pool)
     (fn2-peer-export-resume x (fn2-fc-rows fn2-fc) base slot gen off len sk ss sg lease lgen ok os og
      fn2-reads fn2-id-decides fn2-fields fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-peer-export-resume-core
    (x base slot gen off len sk ss sg lease lgen ok os og fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-peer-export-entry-core (x base slot gen ok os og fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code off len fn2-fields fn2-pool)
     (fn2-peer-export-entry x base slot gen ok os og fn2-reads fn2-run-installed fn2-fields fn2-pool)
     (mv code off len fn2-core)))
   (fn2-core-preserves fn2-peer-export-entry-core
    (x base slot gen ok os og fn2-core) :position 3 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-peer-export-pad-core fn2-peer-export-resume-core fn2-peer-export-entry-core))))
