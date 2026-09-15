"""Check the sealed SM11 bridge quotations against the current SM frame.

The bridge's QUOTATIONS.json pins SM11 bytes. Later frames (SM12, SM15) moved or
reworded some quoted spans. A pinned realignment ledger records, per quotation,
whether it is exact, relocated unchanged, or superseded by new wording, with the
replacement span hashed. Nothing here proves the bridge; it verifies bytes.
"""
from tools.bundlelib import digest, require

SCHEMA = 'bridge-quote-realignment-v1'


def locate(raw, quoted):
    """1-based start line when `quoted` occurs exactly once at a line boundary."""
    if raw.count(quoted) != 1:
        return None
    offset = raw.index(quoted)
    if offset and raw[offset-1:offset] != b'\n':
        return None
    return raw[:offset].count(b'\n') + 1


def classify(q, raw):
    quoted = q['text'].encode('utf-8')
    lines = raw.splitlines(keepends=True)
    a, b = q['start_line'], q['end_line']
    if digest(raw) == q['source_sha256'] and b <= len(lines) and b''.join(lines[a-1:b]) == quoted:
        return 'exact', a
    start = locate(raw, quoted)
    if start is not None:
        return 'relocated', start
    return 'superseded', None


def check_quotes(quotes, frames, ledger, current_sm):
    """frames: {frame: {file: bytes}} for the current frames; SM11 quotes map to current_sm."""
    require(isinstance(ledger, dict) and ledger.get('schema') == SCHEMA
            and ledger.get('current_frame') == current_sm, 'realignment ledger schema')
    entries = ledger['quotes']
    require(set(entries) == {q['id'] for q in quotes} and len(entries) == len(quotes), 'ledger quote inventory')
    counts = {'exact': 0, 'relocated': 0, 'superseded': 0}
    relocations, superseded = [], []
    for q in quotes:
        frame = current_sm if q['frame'] == 'SM11' else q['frame']
        require(frame in frames and q['file'] in frames[frame], 'quote outside frame: ' + q['id'])
        raw = frames[frame][q['file']]
        quoted = q['text'].encode('utf-8')
        require(digest(quoted) == q['quote_sha256'], 'quote hash: ' + q['id'])
        a, b = q['start_line'], q['end_line']
        require(type(a) is int and type(b) is int and 1 <= a <= b, 'quote range: ' + q['id'])
        status, line = classify(q, raw)
        e = entries[q['id']]
        require(e.get('status') == status and e.get('file') == q['file'] and e.get('frame') == frame
                and e.get('original_line') == a, 'ledger status mismatch: ' + q['id'])
        require(e.get('current_source_sha256') == digest(raw), 'ledger source hash: ' + q['id'])
        if status == 'superseded':
            require(q['frame'] == 'SM11', 'only SM quotations may be superseded: ' + q['id'])
            lines = raw.splitlines(keepends=True)
            s, t = e.get('current_start'), e.get('current_end')
            require(type(s) is int and type(t) is int and 1 <= s <= t <= len(lines), 'superseded range: ' + q['id'])
            require(digest(b''.join(lines[s-1:t])) == e.get('current_excerpt_sha256')
                    and e.get('original_quote_sha256') == q['quote_sha256']
                    and isinstance(e.get('reason'), str) and e['reason'], 'superseded excerpt: ' + q['id'])
            superseded.append(q['id'])
        else:
            require(e.get('current_line') == line, 'ledger line: ' + q['id'])
            if status == 'relocated':
                relocations.append({'id': q['id'], 'original_frame': q['frame'], 'current_frame': frame,
                                    'original_line': a, 'current_line': line,
                                    'current_source_sha256': digest(raw), 'quote_bytes_unchanged': True})
        counts[status] += 1
    return {'counts': counts, 'relocations': relocations, 'superseded': superseded}


def build_ledger(quotes, frames, current_sm, replacements):
    """Compute the ledger from current bytes; `replacements` supplies superseded spans by quote id."""
    entries = {}
    for q in quotes:
        frame = current_sm if q['frame'] == 'SM11' else q['frame']
        raw = frames[frame][q['file']]
        status, line = classify(q, raw)
        e = {'status': status, 'frame': frame, 'file': q['file'], 'original_frame': q['frame'],
             'original_line': q['start_line'], 'current_source_sha256': digest(raw)}
        if status == 'superseded':
            s, t, reason = replacements[q['id']]
            lines = raw.splitlines(keepends=True)
            e.update({'current_start': s, 'current_end': t,
                      'current_excerpt_sha256': digest(b''.join(lines[s-1:t])),
                      'original_quote_sha256': q['quote_sha256'], 'reason': reason})
        else:
            e['current_line'] = line
        entries[q['id']] = e
    return {'schema': SCHEMA, 'current_frame': current_sm, 'quotes': entries}
