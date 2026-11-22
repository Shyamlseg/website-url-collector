
import argparse
import csv
import os
import re
from datetime import datetime, timezone
from pathlib import Path

COLUMNS = [
    'run_date', 'seed_set', 'queue_no', 'company_url',
    'discovered_links', 'pages_processed', 'captured_pages', 'other_html_pages',
    'failed_pages', 'skipped_pages', 'blocked_http', 'remaining_links',
    'stop_reason', 'status', 'status_reason', 'run_id',
]
BLOCK_CODES = {401, 403, 429}


def to_int(value, default=0):
    try:
        return int(float(str(value).strip()))
    except (ValueError, TypeError):
        return default


def is_true(value):
    return str(value).strip().lower() == 'true'


def count_rows(path):
    """Data rows in a CSV (header and TOTAL rows excluded); None if the file is missing."""
    if not path.exists():
        return None
    with path.open(encoding='utf-8-sig', newline='') as f:
        reader = csv.reader(f)
        next(reader, None)
        return sum(1 for r in reader if r and r[0] != 'TOTAL')


def last_row(path):
    if not path.exists():
        return None
    with path.open(encoding='utf-8-sig', newline='') as f:
        rows = [r for r in csv.DictReader(f) if r and any((v or '').strip() for v in r.values())]
    return rows[-1] if rows else None


def perf_counts(path):
    """(ok_pages, blocked_http, total_requests) from PERFORMANCE_REPORT.csv; None if missing."""
    if not path.exists():
        return None
    ok = blocked = total = 0
    with path.open(encoding='utf-8-sig', newline='') as f:
        for r in csv.DictReader(f):
            if not r or (next(iter(r.values())) or '') == 'TOTAL':
                continue
            code = to_int(r.get('http_status'), -1)
            total += 1
            if 200 <= code < 400:
                ok += 1
            elif code in BLOCK_CODES:
                blocked += 1
    return ok, blocked, total


def seed_url(seed_dir, n):
    path = seed_dir / f'company-{n}.csv'
    if not path.exists():
        return ''
    with path.open(encoding='utf-8-sig', newline='') as f:
        rows = list(csv.reader(f))
    return rows[1][0] if len(rows) > 1 and rows[1] else ''


def build_row(n, url, folder, set_name, run_id, run_date, max_pages):
    row = {'run_date': run_date, 'seed_set': set_name, 'queue_no': n,
           'company_url': url, 'run_id': run_id}
    if folder is None:
        row.update(status='NO_OUTPUT', status_reason='company never ran or crashed before writing output')
        return row

    rs_path = next(iter(sorted(folder.rglob('RUN_SUMMARY.csv'))), None)
    rs = last_row(rs_path) if rs_path else None
    failed_n = count_rows(folder / 'failed_pages.csv') or 0
    skipped_n = count_rows(folder / 'skipped_pages.csv') or 0
    pdf_n = count_rows(folder / 'pdf_pages.csv') or 0
    html_n = count_rows(folder / 'html_pages.csv') or 0
    perf = perf_counts(folder / 'PERFORMANCE_REPORT.csv')

    if rs:
        processed = to_int(rs.get('processed'))
        failed = to_int(rs.get('failed_pages'), failed_n)
        skipped = to_int(rs.get('skipped_pages'), skipped_n)
        remaining = to_int(rs.get('remaining_discovered'))
        discovered = to_int(rs.get('discovered'), processed + failed + skipped + remaining)
        captured = to_int(rs.get('pdf_pages'), pdf_n)
        other_html = to_int(rs.get('html_pages'), html_n)
        stop_reason = rs.get('stop_reason', '')
        page_limit = is_true(rs.get('page_limit_reached'))
        runtime_limit = is_true(rs.get('runtime_limit_reached'))
        depth_hit = is_true(rs.get('max_depth_reached'))
    else:
        processed = count_rows(folder / 'classified_pages.csv') or (pdf_n + html_n)
        failed, skipped, remaining = failed_n, skipped_n, 0
        discovered = processed + failed + skipped
        captured, other_html = pdf_n, html_n
        stop_reason = 'unknown (no RUN_SUMMARY in output)'
        page_limit = processed >= max_pages > 0
        runtime_limit = depth_hit = False

    ok_pages, blocked_http, total_req = perf if perf else (processed, 0, 0)
    row.update(discovered_links=discovered, pages_processed=processed, captured_pages=captured,
               other_html_pages=other_html, failed_pages=failed, skipped_pages=skipped,
               blocked_http=blocked_http, remaining_links=remaining, stop_reason=stop_reason)

    if ok_pages == 0:
        status, why = 'BLOCKED', f'no page loaded successfully (failed={failed}, 401/403/429={blocked_http})'
    elif ok_pages <= 2 and total_req and blocked_http / total_req >= 0.5:
        status, why = 'BLOCKED', f'mostly blocked responses ({blocked_http} of {total_req} requests were 401/403/429)'
    elif page_limit or runtime_limit or remaining > 0:
        parts = [p for p, hit in (('page budget reached', page_limit), ('runtime limit reached', runtime_limit),
                                  (f'{remaining} links left in queue', remaining > 0)) if hit]
        status, why = 'LIMIT_REACHED', '; '.join(parts)
    else:
        status, why = 'COMPLETED', 'queue exhausted' + ('; max depth was reached' if depth_hit else '')
    row.update(status=status, status_reason=why)
    return row


def key_of(url):
    return re.sub(r'^https?://(www\.)?', '', (url or '').strip().lower()).rstrip('/')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--reports', required=True, help='folder holding collector-shard-*/company-*')
    ap.add_argument('--seeds', required=True, help='folder holding company-N.csv seed files')
    ap.add_argument('--total', type=int, required=True)
    ap.add_argument('--set-name', required=True)
    ap.add_argument('--run-id', default=os.environ.get('GITHUB_RUN_ID', ''))
    ap.add_argument('--max-pages', type=int, default=0)
    ap.add_argument('--previous', default='', help='existing COMPANY_SUMMARY.csv to update')
    ap.add_argument('--out', required=True)
    ap.add_argument('--this-run-out', required=True)
    a = ap.parse_args()

    folders = {}
    for d in Path(a.reports).glob('collector-shard-*/company-*'):
        m = re.search(r'company-(\d+)$', d.name)
        if d.is_dir() and m:
            folders[int(m.group(1))] = d
    run_date = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')
    seed_dir = Path(a.seeds)
    rows = [build_row(n, seed_url(seed_dir, n), folders.get(n), a.set_name, a.run_id, run_date, a.max_pages)
            for n in range(1, a.total + 1)]

    with open(a.this_run_out, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS, extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)

    # Latest status per company: new rows replace old rows for the same URL.
    merged = {}
    prev = Path(a.previous) if a.previous else None
    if prev and prev.exists():
        with prev.open(encoding='utf-8-sig', newline='') as f:
            for r in csv.DictReader(f):
                merged[key_of(r.get('company_url'))] = r
    for r in rows:
        merged[key_of(r['company_url'])] = r
    with open(a.out, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS, extrasaction='ignore', restval='')
        w.writeheader()
        w.writerows(merged.values())

    counts = {}
    for r in rows:
        counts[r['status']] = counts.get(r['status'], 0) + 1
    print(f'{len(rows)} companies:', ', '.join(f'{k}={v}' for k, v in sorted(counts.items())))
    summary = os.environ.get('GITHUB_STEP_SUMMARY')
    if summary:
        with open(summary, 'a', encoding='utf-8') as f:
            f.write(f'\n## Company status ({a.set_name})\n\n| Status | Companies |\n|---|---|\n')
            for k, v in sorted(counts.items()):
                f.write(f'| {k} | {v} |\n')
            bad = [r for r in rows if r['status'] in ('BLOCKED', 'NO_OUTPUT')]
            if bad:
                f.write('\n**Blocked or no output:**\n\n')
                for r in bad[:100]:
                    f.write(f"- {r['company_url'] or 'company ' + str(r['queue_no'])} - {r['status']}: {r['status_reason']}\n")


if __name__ == '__main__':
    main()
