"""Checked atomic-page followup to the original rolling schema generator."""

def transform(text):
    helper = '; The profile-dependent third taken range reads the SAME initialized input row.\n(defun fn2-upload-stream-request-bytes (fn2-input-config)\n (declare (xargs :stobjs fn2-input-config :guard (fn2-input-config-wfp fn2-input-config)))\n (fn2-upload-stream-page-bytes\n  (+ (if (< 0 (fn2-input-config-rows fn2-input-config))\n         (fn2-input-config-article-max 0 fn2-input-config) 0)\n     *fn2-upload-mid-line-max*)))\n(defthm fn2-upload-stream-request-bytes-natural\n (natp (fn2-upload-stream-request-bytes fn2-input-config))\n :rule-classes :type-prescription)\n'
    marker = '(defun fn2-input-config-profilep (profile)'
    assert text.count(marker) == 1
    text = text.replace(marker, helper + marker)
    old = '(:chunk-window :slot c1-slot :gen c1-gen :class (:bytes *fn2-upload-body-window-bytes*)))'
    assert text.count(old) == 1
    text = text.replace(old, '(:chunk-window :slot c1-slot :gen c1-gen :class (:bytes *fn2-upload-body-window-bytes*))\n                  (:storage-window :slot lslot :gen lgen\n                   :class (:bytes (:from fn2-input-config fn2-upload-stream-request-bytes))))\n         :set ((lease *fn2-upload-lease-held*))')
    assert text.count('lgen lease ilen cepoch') == 1
    text = text.replace('lgen lease ilen cepoch', 'ilen cepoch')
    text = text.replace(';; A connection takes the row with its two chunks (A-S7).',
                        ';; A connection takes all three windows atomically, including its profile-sized page.')
    for phase in ['head', 'identity', 'receiving', 'validating', 'discard']:
        old_hold = f'(:{phase} :upload-row :chunk-window)'
        assert text.count(old_hold) == 1
        text = text.replace(old_hold, f'(:{phase} :upload-row :chunk-window (:storage-window :while (lease :held)))')
    return text
