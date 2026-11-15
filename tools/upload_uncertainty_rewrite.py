"""Compose only the reviewed upload uncertainty delta, with an exact inverse."""
import json
from pathlib import Path

FIXTURE = Path(__file__).resolve().parent / 'fixtures/upload_uncertainty_transform.json'


def transform(source, name, reverse=False):
    record = json.loads(FIXTURE.read_text())['files'].get(name)
    if record is None:
        return source
    before, after = ('after', 'before') if reverse else ('before', 'after')
    for hunk in record['hunks']:
        old, new = hunk[before], hunk[after]
        count = source.count(old)
        if count != 1:
            raise ValueError(f'{name}: expected one reviewed uncertainty site, got {count}')
        source = source.replace(old, new, 1)
    return source
