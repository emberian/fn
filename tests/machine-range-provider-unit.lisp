; Generator controls; actual upload TAKE is tested separately.
(in-package "ACL2")
(include-book "../books/machine-arms")
(assert-event (equal (fn2-machine-class-form 1 'fn2-pool) 1))
(assert-event (equal (fn2-machine-class-form '(:bytes window-bytes) 'fn2-pool)
                     '(fn2-pool-class-for window-bytes fn2-pool)))
(assert-event (fn2-machine-class-specp '(:bytes (:from input-config page-request))))
(assert-event (not (fn2-machine-class-specp '(:bytes (:from input-config page-request extra)))))
(assert-event (not (fn2-machine-class-specp '(:bytes (page-request input-config)))))
(assert-event
 (equal (fn2-machine-class-form '(:bytes (:from input-config page-request)) 'fn2-pool)
        '(fn2-pool-class-for (page-request input-config) fn2-pool)))
(assert-event
 (equal (fn2-machine-range-inputs
          '((:storage-window :slot a :gen ag :class (:bytes (:from input-config page-request)))
            (:chunk-window :slot b :gen bg :class 0)
            (:storage-window :slot c :gen cg :class (:bytes (:from input-config other-request)))))
        '(input-config)))
(assert-event
 (equal (fn2-arms-registry-reserves
          '((:storage-window :slot a :gen ag :class (:bytes (:from input-config page-request))))
          0 'installed 'refused)
        '(mv-let (code0 slot0 pgen0 fn2-pool)
          (fn2-pool-reserve (fn2-pool-class-for (page-request input-config) fn2-pool) kind target gen fn2-pool)
          (if (not (eq code0 :ok)) refused installed))))
