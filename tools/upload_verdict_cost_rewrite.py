#!/usr/bin/env python3
"""Explicit followup to block-cost replay: charge the separate header verdict."""
def arm_charge(s):
    start=s.index('(:stream-init :on-refusal')
    start=s.index('((equal row-mstep 0)',start)
    end=s.index('((equal row-mstep 1)',start)
    part=s[start:end]
    old='(:charge :steps *fn2-work-transition* :runnable t)'
    assert part.count(old)==2
    part=part.replace(old,'(:charge :bytes *fn2-upload-verdict-work-bytes* :steps *fn2-work-transition* :runnable t)')
    return s[:start]+part+s[end:]
