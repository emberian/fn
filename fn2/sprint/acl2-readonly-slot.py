#!/usr/bin/env python3
"""Run tools/acl2 with the SAME global slot locks opened read-only.

The sandbox permits reading the global pool but forbids its diagnostic writes.
flock(LOCK_EX) on an existing read-only descriptor still excludes every normal
launcher. Nothing relocates the pool, changes its count, or bypasses tools/acl2.
Only the slot acquisition hook differs; PID/label diagnostics go under build/.
"""
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import runpy
import sys
sys.dont_write_bytecode = True
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import acl2_slots

@contextmanager
def shared_readonly_slot(label='acl2', log=None, poll=acl2_slots.POLL_SECONDS,
                         report_every=acl2_slots.REPORT_SECONDS, wait_seconds=None):
    count = acl2_slots.slot_count()
    directory = acl2_slots.slot_directory()
    if directory != Path(acl2_slots.DEFAULT_SLOT_DIR).expanduser():
        raise RuntimeError('sprint requires the ordinary machine-wide slot directory')
    started = time.monotonic()
    if wait_seconds is None:
        wait_seconds = acl2_slots.configured_wait()
    descriptor = None
    while descriptor is None:
        for index in range(count):
            candidate = os.open(directory / f'slot-{index:03d}', os.O_RDONLY)
            try:
                fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                os.close(candidate)
            else:
                descriptor = candidate
                break
        if descriptor is None:
            if wait_seconds is not None and time.monotonic() - started >= wait_seconds:
                raise acl2_slots.SlotWaitExpired('sprint timed out waiting on global ACL2 slots')
            time.sleep(min(poll, 1))
    held = ROOT / 'build' / f'sprint-acl2-holder-{os.getpid()}.txt'
    try:
        held.write_text(f'{os.getpid()} slot={index}/{count} {label}\n')
        yield acl2_slots.Slot(index=index, seconds=round(time.monotonic()-started, 3), slots=count)
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)
        with held.open('a') as record:
            record.write('released\n')

if __name__ == '__main__':
    acl2_slots.slot = shared_readonly_slot
    runpy.run_path(str(ROOT / 'tools' / 'acl2'), run_name='__main__')
