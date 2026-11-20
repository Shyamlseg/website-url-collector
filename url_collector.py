
from __future__ import annotations
import argparse, asyncio, csv, hashlib, json, logging, os, re, signal, sqlite3, sys, time
from dataclasses import dataclass, fields
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit
from playwright.async_api import async_playwright, Error as PWError, TimeoutError as PWTimeout

# --------------------------------------------------------------------------- #
# Static vocabularies
# --------------------------------------------------------------------------- #
DOC_EXT = {'.pdf', '.doc', '.docx', '.xls', '.xlsx', '.ppt', '.pptx', '.rtf', '.odt', '.ods', '.odp'}
ASSET_EXT = {'.css', '.js', '.mjs', '.png', '.jpg', '.jpeg', '.svg', '.gif', '.webp', '.avif', '.ico',
             '.woff', '.woff2', '.ttf', '.eot', '.mp4', '.webm', '.mp3', '.wav', '.zip', '.rar', '.7z',
             '.gz', '.tar', '.map'}
DOC_MIME = ('application/pdf', 'application/msword', 'application/vnd.openxmlformats-officedocument',
            'application/vnd.oasis.opendocument', 'application/vnd.ms-excel',
            'application/vnd.ms-powerpoint', 'application/rtf', 'application/octet-stream')
# Broad hint: file extensions AND document-ish folders. Used ONLY to decide which
# content links deserve a HEAD check. Never used to stop crawling a URL.
DOC_HINT = re.compile(
    r'(?:\.(?:pdf|docx?|xlsx?|pptx?|rtf|od[tsp])(?:$|[?#])'
    r'|/(?:downloads?|documents?|files?|uploads?|storage|assets?/docs?|media/docs?|attachments?)(?:/|$)'
    r'|\.ashx(?:$|[?#])|/getfile|/download\.aspx|/viewdocument)', re.I)
# Strict hint: real file signals only. Used for crawl policy / child filtering.
DOC_FILE_HINT = re.compile(
    r'(?:\.(?:pdf|docx?|xlsx?|pptx?|rtf|od[tsp])(?:$|[?#])'
    r'|\.ashx(?:$|[?#])|/getfile|/download\.aspx|/viewdocument)', re.I)
# Document URL inside onclick / data-* attribute text.
ATTR_DOC_RX = re.compile(r"""(['"])([^'"]+?\.(?:pdf|docx?|xlsx?|pptx?|rtf|od[tsp])(?:[?#][^'"]*)?)\1"""
                         r"""|([^\s'"=()]+?\.(?:pdf|docx?|xlsx?|pptx?|rtf|od[tsp]))(?=$|[\s?#'")])""", re.I)
# PDF.js / generic embedded-viewer wrappers: ...viewer.html?file=/x.pdf
VIEWER_PARAMS = ('file', 'url', 'src', 'document', 'doc', 'pdf', 'href')
UNSAFE = re.compile(r'/(?:logout|log-out|login|log-in|signin|sign-in|signup|sign-up|register|cart|'
                    r'checkout|basket|my-?account|wp-admin|wp-login|admin|search|share|print)(?:/|$)', re.I)
PKEYS = {'page', 'p', 'paged', 'offset', 'start', 'pagenum', 'pagenumber', 'pg', 'from', 'skip'}
NEXT = re.compile(r'^(?:next|next page|older|older posts?|more|forward|\d{1,4}|page\s*\d{1,4})\s*'
                  r'(?:›|»|→|>|>>)?$', re.I)
NEXT_SYMBOL = re.compile(r'^(?:›|»|→|>|>>|next\s*[›»→>]*)$', re.I)
LOAD = re.compile(r'\b(?:load|show|view|see)\s+(?:\d+\s+)?more\b', re.I)
COOKIE = re.compile(r'^(?:accept(?: all| cookies| all cookies)?|allow all|i agree|agree|ok|got it|'
                    r'understood|continue|dismiss|close|reject all|only necessary)$', re.I)
YEAR = re.compile(r'^(19|20)\d{2}$')
ESG_NAV = re.compile(
    r'\b(?:esg|sustainab(?:ility|le)?|environment(?:al)?|climate|social(?: responsibility)?|'
    r'governance|corporate governance|ethics|compliance|polic(?:y|ies)|reports?|disclosures?|'
    r'documents?|charters?|human rights|responsible sourcing|health and safety|board|committees?|'
    r'resources?|responsibility|investors?|financials?|results?|shareholders?|notices?|'
    r'annual reports?|presentations?|filings?|downloads?)\b', re.I)
MENU_NAV = re.compile(r'^(?:menu|open menu|navigation|main menu|site menu|more)$', re.I)
# Anchors that say nothing on their own: borrow the card heading.
GENERIC_ANCHOR = re.compile(r'^(?:read more|learn more|more|view|view more|details|download|'
                            r'click here|find out more|explore|see more)?$', re.I)
# Path-based pagination (/page/2, /page-2, /pg2, /p/2).
PAGE_PATH_RX = re.compile(r'/(?:page|pg)[-/_]?(\d+)/?$|/p/(\d+)/?$', re.I)
# Article / detail pages (dated paths, numeric ids, long slugs).
DETAIL_RX = re.compile(r'/(?:19|20)\d{2}/(?:0?[1-9]|1[0-2])(?:/|$)|/\d{5,}(?:/|$)'
                       r'|/[a-z0-9]+(?:-[a-z0-9]+){4,}/?$', re.I)
# First folder that means shop / product catalogue - never holds company documents.
ECOM_FOLDERS = {'p', 'pd', 'dp', 'product', 'products', 'shop', 'store', 'item', 'items', 'sku',
                'buy', 'deals', 'deal', 'coupons', 'brands', 'brand', 'c', 'category',
                'categories', 'collections', 'catalog', 'catalogue', 'recipes', 'recipe'}

# Vocabulary syntax:  "foo" = exact token match, "foo*" = token prefix match,
# "foo-bar" = consecutive token phrase.
ESG_STRONG = (
    'esg', 'sustainab*', 'environment*', 'climate', 'climate-change', 'carbon', 'carbon-footprint',
    'footprint', 'emission*', 'ghg', 'greenhouse-gas', 'net-zero', 'netzero', 'decarbon*', 'renewable*',
    'photovoltaic', 'solar', 'wind-power', 'energy-efficiency', 'energy-transition', 'water',
    'water-stewardship', 'waste', 'zero-waste', 'recycl*', 'circular-economy', 'circularity',
    'biodiversity', 'nature', 'natural-capital', 'deforestation', 'pollution', 'social-impact',
    'social-responsibility', 'corporate-responsibility', 'corporate-accountability', 'accountability',
    'csr', 'brsr', 'community', 'community-investment', 'human-right*', 'labor-right*', 'labour-right*',
    'modern-slavery', 'responsible-sourcing', 'responsible-supply-chain', 'supplier-code',
    'supply-chain-standard*', 'diversity', 'inclusion', 'equity', 'dei', 'health-and-safety',
    'occupational-health', 'employee-wellbeing', 'wellbeing', 'governance', 'ethics', 'ethical',
    'compliance', 'code-of-conduct', 'business-conduct', 'anti-corruption', 'anti-bribery',
    'whistleblower', 'whistleblowing', 'risk-management', 'stakeholder*', 'materiality',
    'integrated-report*', 'sustainability-report*', 'responsibility-report*', 'annual-report*',
    'impact-report*', 'tcfd', 'tnfd', 'sasb', 'gri', 'cdp', 'csrd', 'sfdr', 'issb', 'sdg', 'sdgs',
    'taxonomy', 'scope-1', 'scope-2', 'scope-3', 'transition-plan', 'charter', 'disclosure*',
    'general-meeting*', 'annual-general-meeting*', 'ordinary-general-meeting*', 'agm',
    'privacy', 'privacy-policy', 'data-protection', 'personal-data',
)
ESG_GATEWAY = (
    'about', 'about-us', 'who-we-are', 'company', 'corporate', 'our-approach', 'our-commitment*',
    'responsibility', 'policy', 'policies', 'committee', 'committees', 'board', 'leadership',
    'resource', 'resources', 'report', 'reports', 'reporting', 'publication*', 'document*',
    'download*', 'library', 'archive', 'centre', 'center', 'hub', 'investor*', 'esg-data',
)
# v5: HARD negatives - sections that never hold company documents. Blocked.
HARD_NEGATIVE = (
    'contact', 'contact-us', 'email-alert*', 'subscribe', 'subscription*', 'newsletter*',
    'customer-support', 'support', 'help', 'faq', 'faqs', 'request-information', 'request-a-demo',
    'demo', 'photo', 'photos', 'photography', 'image', 'images', 'gallery', 'galleries', 'video',
    'videos', 'multimedia', 'audio', 'youtube', 'vimeo', 'podcast*', 'webinar*', 'career', 'careers',
    'job', 'jobs', 'vacancies', 'recruitment', 'dealer*', 'store-locator', 'stores', 'shop', 'cart',
    'checkout', 'login', 'logout', 'signin', 'signup', 'register', 'account', 'my-account',
    'profile', 'search', 'share', 'print', 'cookie', 'cookies', 'terms', 'terms-of-use',
    'accessibility', 'sitemap', 'rss', 'feed', 'stock-quote', 'share-price', 'shareprice',
    'stock-chart', 'calculator*', 'emi-calculator',
)
# v5: SOFT negatives - loop-prone sections that MAY hold documents (press
# releases, events with presentations). Not blocked, crawled last.
SOFT_NEGATIVE = (
    'news', 'newsroom', 'news-release*', 'press', 'press-release*', 'press-room', 'media',
    'media-release*', 'media-centre', 'media-center', 'event', 'events', 'calendar', 'conference*',
    'stories', 'story', 'article', 'articles', 'blog', 'blogs', 'insight', 'insights', 'location',
    'locations', 'webcast*',
)
# Path tokens that strongly imply "this page lists documents".
DOC_HUB = ('report', 'reports', 'reporting', 'publication*', 'document*', 'download*', 'library',
           'archive', 'resource', 'resources', 'disclosure*', 'filing*', 'policy', 'policies',
           'data-centre', 'data-center', 'esg-data', 'general-meeting*',
           'annual-general-meeting*', 'ordinary-general-meeting*', 'agm', 'egm', 'charter*',
           # v5: investor / financial pages are document hubs, not negatives.
           'investor*', 'financial*', 'result*', 'earning*', 'quarterly*', 'annual*',
           'presentation*', 'shareholder*', 'shareholding*', 'dividend*', 'iepf', 'notice*',
           'intimation*', 'announcement*', 'transcript*', 'proxy', 'sec-filing*', '10-k', '10-q',
           '20-f', 'credit-rating*', 'corporate-governance', 'governance', 'code*', 'regulation*',
           'sebi', 'postal-ballot', 'outcome*', 'board-meeting*', 'statutory', 'secretarial',
           'compliance*', 'debenture*', 'bond*', 'debt*', 'prospectus', 'brochure*', 'factsheet*',
           'fact-sheet*', 'rera', 'csr', 'brsr', 'esg', 'sustainab*', 'circular*', 'form*')


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #
def now():
    return datetime.now(timezone.utc).isoformat(timespec='seconds')


def ext(url):
    name = urlsplit(url).path.rsplit('/', 1)[-1].lower()
    return '.' + name.rsplit('.', 1)[-1] if '.' in name else ''


def env(name, default, typ):
    v = os.getenv(name)
    if v in (None, ''):
        return default
    if typ is bool:
        return v.lower() in ('1', 'true', 'yes', 'on')
    try:
        return typ(v)
    except (TypeError, ValueError):
        logging.warning('Ignoring invalid %s=%r', name, v)
        return default


def canon(value):
    """Lowercase and split into alphanumeric tokens."""
    return [t for t in re.split(r'[^a-z0-9]+', (value or '').lower()) if t]


def compile_vocab(entries):
    """Returns (exact set, prefix tuple, phrase tuple)."""
    exact, prefixes, phrases = set(), [], []
    for raw in entries:
        star = raw.endswith('*')
        item = raw[:-1] if star else raw
        toks = canon(item)
        if not toks:
            continue
        if len(toks) > 1:
            phrases.append((tuple(toks), star))
        elif star:
            prefixes.append(toks[0])
        else:
            exact.add(toks[0])
    return exact, tuple(prefixes), tuple(phrases)


def match_vocab(tokens, compiled):
    exact, prefixes, phrases = compiled
    tset = set(tokens)
    if tset & exact:
        return True
    for t in tokens:
        for pre in prefixes:
            if t.startswith(pre):
                return True
    n = len(tokens)
    for phrase, star in phrases:
        m = len(phrase)
        for i in range(n - m + 1):
            window = tokens[i:i + m]
            if window[:-1] == list(phrase[:-1]) and (
                    window[-1].startswith(phrase[-1]) if star else window[-1] == phrase[-1]):
                return True
    return False


V_STRONG = compile_vocab(ESG_STRONG)
V_GATEWAY = compile_vocab(ESG_GATEWAY)
V_NEGATIVE = compile_vocab(HARD_NEGATIVE)
V_SOFT = compile_vocab(SOFT_NEGATIVE)
V_DOC_HUB = compile_vocab(DOC_HUB)


def split_label(text):
    """links() returns 'card heading | anchor text'. Returns (anchor, label_for_scoring).
    The heading is only borrowed when the anchor itself is generic."""
    parts = (text or '').split(' | ')
    anchor = parts[-1].strip()
    scoring = ' '.join(p.strip() for p in parts) if GENERIC_ANCHOR.match(anchor) else anchor
    return anchor, scoring


def path_page_num(path):
    m = PAGE_PATH_RX.search(path or '')
    if not m:
        return None
    return int(m.group(1) or m.group(2))


def slugify(value, limit=60):
    return re.sub(r'[^a-z0-9]+', '_', (value or '').lower()).strip('_')[:limit] or 'site'


def output_dir_for(seed, root):
    """Per-seed directory keyed on netloc + path + hash."""
    p = urlsplit(seed)
    key = slugify((p.netloc or '') + (p.path or ''))
    digest = hashlib.sha1(seed.encode('utf-8', 'ignore')).hexdigest()[:8]
    return root / f'{key}_{digest}'


def strip_fragment(u):
    p = urlsplit(u or '')
    return urlunsplit((p.scheme, p.netloc, p.path or '/', p.query, ''))


# --------------------------------------------------------------------------- #
# Config
# --------------------------------------------------------------------------- #
@dataclass
class Config:
    # ---- bounded expansion ----
    max_pagination_pages: int = 8
    max_load_more_clicks: int = 5
    max_year_options: int = 4
    max_depth: int = 6
    max_pages_per_website: int = 400
    max_documents_per_page: int = 200
    max_esg_navigation_clicks_per_page: int = 8
    # ---- anti-trap ----
    section_probe_pages: int = 12           # zero-doc pages processed in a section before it is abandoned
    expansion_budget_seconds: int = 35      # time for pagination + load-more + year loops per page
    sitemap_document_folders: bool = False  # queue parent folder of sitemap document URLs
    max_low_priority_children_per_page: int = 10   # news / blog / events links followed per page
    # ---- per-website limits ----
    max_minutes_per_website: int = 15       # hard time budget per website
    stall_minutes: int = 5                  # stop a website if no page finishes for this long
    parallel_websites: int = 3              # websites crawled at the same time
    # ---- timing ----
    page_timeout_seconds: int = 45
    delay_between_pages_seconds: float = 0.35
    max_retries: int = 2
    max_runtime_minutes: int = 170
    stabilization_seconds: float = 0.6
    document_head_timeout_seconds: int = 4
    page_attempt_timeout_seconds: int = 75
    page_close_timeout_seconds: int = 5
    # ---- scope ----
    crawl_subdomains: bool = True
    restrict_to_seed_language: bool = True
    allowed_hosts: tuple = ()
    # ---- budgets ----
    max_new_children_per_page: int = 60
    max_homepage_children: int = 150
    max_pages_per_url_family: int = 25
    max_query_variants_per_path: int = 3
    follow_same_family_links_from_detail_pages: bool = False
    prioritize_document_likely_pages: bool = True
    # ---- query handling ----
    query_parameter_mode: str = 'whitelist'         # 'whitelist' or 'blacklist'
    keep_meaningful_query_parameters: tuple = (
        'year', 'page', 'paged', 'p', 'offset', 'start', 'category', 'cat', 'type', 'section',
        'id', 'doc', 'document', 'file', 'lang', 'locale', 'tab')
    remove_query_parameters: tuple = ('utm_source', 'utm_medium', 'utm_campaign', 'utm_term',
                                      'utm_content', 'fbclid', 'gclid', 'msclkid', 'mc_cid',
                                      'mc_eid', 'ref', 'referrer', '_ga')
    # ---- robots / sitemap ----
    respect_robots_txt: bool = True
    use_sitemap: bool = True
    max_sitemaps: int = 25
    max_sitemap_urls: int = 5000
    max_neutral_sitemap_urls: int = 150
    # ---- runtime ----
    concurrency: int = 4
    block_heavy_resources: bool = True
    export_checkpoint_pages: int = 25
    recover_orphaned_pages: bool = True
    user_agent: str = 'Mozilla/5.0 (compatible; WebsiteURLCollector/5.0)'
    robots_agent: str = 'websiteurlcollector'

    @classmethod
    def load(cls, path):
        raw = {}
        if path and Path(path).exists():
            try:
                raw = json.loads(Path(path).read_text(encoding='utf-8')) or {}
            except (OSError, ValueError) as exc:
                logging.warning('Config %s unreadable (%s); using defaults', path, exc)
                raw = {}
        defaults = cls()
        names = {f.name for f in fields(cls)}
        for k in list(raw):
            if k not in names:
                logging.warning('Ignoring unknown config key %r', k)
                raw.pop(k)
            elif isinstance(getattr(defaults, k), tuple):
                raw[k] = tuple(raw[k])
        c = cls(**raw)
        mapping = {
            'max_pagination_pages': ('MAX_PAGINATION_PAGES', int),
            'max_load_more_clicks': ('MAX_LOAD_MORE_CLICKS', int),
            'max_year_options': ('MAX_YEAR_OPTIONS', int),
            'max_depth': ('MAX_DEPTH', int),
            'max_pages_per_website': ('MAX_PAGES', int),
            'max_documents_per_page': ('MAX_DOCUMENTS_PER_PAGE', int),
            'max_esg_navigation_clicks_per_page': ('MAX_ESG_NAVIGATION_CLICKS_PER_PAGE', int),
            'section_probe_pages': ('SECTION_PROBE_PAGES', int),
            'expansion_budget_seconds': ('EXPANSION_BUDGET_SECONDS', int),
            'sitemap_document_folders': ('SITEMAP_DOCUMENT_FOLDERS', bool),
            'max_low_priority_children_per_page': ('MAX_LOW_PRIORITY_CHILDREN_PER_PAGE', int),
            'max_minutes_per_website': ('MAX_MINUTES_PER_WEBSITE', int),
            'stall_minutes': ('STALL_MINUTES', int),
            'parallel_websites': ('PARALLEL_WEBSITES', int),
            'page_timeout_seconds': ('PAGE_TIMEOUT_SECONDS', int),
            'delay_between_pages_seconds': ('DELAY_BETWEEN_PAGES_SECONDS', float),
            'max_retries': ('MAX_RETRIES', int),
            'max_runtime_minutes': ('MAX_RUNTIME_MINUTES', int),
            'stabilization_seconds': ('STABILIZATION_SECONDS', float),
            'document_head_timeout_seconds': ('DOCUMENT_HEAD_TIMEOUT_SECONDS', int),
            'page_attempt_timeout_seconds': ('PAGE_ATTEMPT_TIMEOUT_SECONDS', int),
            'page_close_timeout_seconds': ('PAGE_CLOSE_TIMEOUT_SECONDS', int),
            'crawl_subdomains': ('CRAWL_SUBDOMAINS', bool),
            'restrict_to_seed_language': ('RESTRICT_TO_SEED_LANGUAGE', bool),
            'max_new_children_per_page': ('MAX_NEW_CHILDREN_PER_PAGE', int),
            'max_homepage_children': ('MAX_HOMEPAGE_CHILDREN', int),
            'max_pages_per_url_family': ('MAX_PAGES_PER_URL_FAMILY', int),
            'max_query_variants_per_path': ('MAX_QUERY_VARIANTS_PER_PATH', int),
            'follow_same_family_links_from_detail_pages': ('FOLLOW_SAME_FAMILY_LINKS_FROM_DETAIL_PAGES', bool),
            'prioritize_document_likely_pages': ('PRIORITIZE_DOCUMENT_LIKELY_PAGES', bool),
            'query_parameter_mode': ('QUERY_PARAMETER_MODE', str),
            'respect_robots_txt': ('RESPECT_ROBOTS_TXT', bool),
            'use_sitemap': ('USE_SITEMAP', bool),
            'max_sitemaps': ('MAX_SITEMAPS', int),
            'max_sitemap_urls': ('MAX_SITEMAP_URLS', int),
            'max_neutral_sitemap_urls': ('MAX_NEUTRAL_SITEMAP_URLS', int),
            'concurrency': ('CONCURRENCY', int),
            'block_heavy_resources': ('BLOCK_HEAVY_RESOURCES', bool),
            'export_checkpoint_pages': ('EXPORT_CHECKPOINT_PAGES', int),
            'recover_orphaned_pages': ('RECOVER_ORPHANED_PAGES', bool),
            'user_agent': ('USER_AGENT', str),
        }
        for attr, (name, typ) in mapping.items():
            setattr(c, attr, env(name, getattr(c, attr), typ))
        # Clamps - every ceiling must stay bounded.
        c.max_pagination_pages = max(1, c.max_pagination_pages)
        c.max_load_more_clicks = max(0, c.max_load_more_clicks)
        c.max_year_options = max(0, c.max_year_options)
        c.max_documents_per_page = max(1, c.max_documents_per_page)
        c.max_esg_navigation_clicks_per_page = max(0, c.max_esg_navigation_clicks_per_page)
        c.concurrency = max(1, min(16, c.concurrency))
        c.max_depth = max(0, c.max_depth)
        c.max_pages_per_website = max(1, c.max_pages_per_website)
        c.section_probe_pages = max(3, c.section_probe_pages)
        c.max_low_priority_children_per_page = max(0, c.max_low_priority_children_per_page)
        c.max_minutes_per_website = max(1, c.max_minutes_per_website)
        c.stall_minutes = max(1, c.stall_minutes)
        c.parallel_websites = max(1, min(6, c.parallel_websites))
        c.expansion_budget_seconds = max(5, min(c.expansion_budget_seconds,
                                                c.page_attempt_timeout_seconds - 20))
        if c.query_parameter_mode not in ('whitelist', 'blacklist'):
            c.query_parameter_mode = 'whitelist'
        return c


# --------------------------------------------------------------------------- #
# robots.txt
# --------------------------------------------------------------------------- #
class Robots:
    """Minimal robots.txt evaluator: longest-match wins, allow beats
    disallow on equal length, wildcards and $ supported, Sitemap: collected."""

    def __init__(self, agent='websiteurlcollector'):
        self.agent = agent.lower()
        self.rules = []
        self.sitemaps = []
        self.loaded = False

    @staticmethod
    def _rx(pattern):
        out = ''
        for ch in pattern:
            if ch == '*':
                out += '.*'
            elif ch == '$':
                out += '$'
            else:
                out += re.escape(ch)
        return re.compile('^' + out)

    def parse(self, text):
        groups, current, expect_agent = {}, [], True
        for raw in (text or '').splitlines():
            line = raw.split('#', 1)[0].strip()
            if not line or ':' not in line:
                continue
            key, value = line.split(':', 1)
            key, value = key.strip().lower(), value.strip()
            if key == 'sitemap':
                if value:
                    self.sitemaps.append(value)
                continue
            if key == 'user-agent':
                if not expect_agent:
                    current, expect_agent = [], True
                if value:
                    current.append(value.lower())
                    groups.setdefault(value.lower(), [])
                continue
            if key in ('allow', 'disallow') and current:
                expect_agent = False
                if not value:
                    continue
                for name in current:
                    groups[name].append((key == 'allow', value))
        for name in (self.agent, '*'):
            if name in groups:
                self.rules = [(allow, self._rx(path), len(path)) for allow, path in groups[name]]
                break
        self.loaded = True
        return self

    def allowed(self, url):
        if not self.rules:
            return True
        p = urlsplit(url)
        target = (p.path or '/') + (('?' + p.query) if p.query else '')
        best = None
        for allow, rx, length in self.rules:
            if rx.match(target) and (best is None or length > best[1] or (length == best[1] and allow)):
                best = (allow, length)
        return True if best is None else best[0]


# --------------------------------------------------------------------------- #
# Collector
# --------------------------------------------------------------------------- #
class Collector:
    def __init__(self, seed, cfg, out_root=None):
        self.cfg = cfg
        self.seed = self.norm_seed(seed)
        self.host = (urlsplit(self.seed).hostname or '').lower()
        parts = self.host.split('.')
        self.base = '.'.join(parts[-2:]) if len(parts) > 1 else self.host
        seed_path = urlsplit(self.seed).path or '/'
        m = re.match(r'^/([a-z]{2}(?:-[a-z]{2})?)(?:/|$)', seed_path, re.I)
        self.language_prefix = ('/' + m.group(1).lower() + '/') if m else None
        self.out = output_dir_for(self.seed, out_root or Path('.'))
        self.out.mkdir(parents=True, exist_ok=True)
        self.processed_since_export = 0
        self.document_cache = {}
        self.robots = Robots(cfg.robots_agent)
        self.started = time.monotonic()
        self.stop = False
        self.last_progress = time.monotonic()
        self.page_limit = False
        self.runtime_limit = False
        self.run_delay_seconds = 0.0
        self.run_export_seconds = 0.0
        self.expansion = dict(parent_budget=0, family_limit=0, query_limit=0, same_family=0,
                              after_page_limit=0, negative=0, esg_priority=0, robots_blocked=0,
                              sitemap_seeded=0, orphans_recovered=0, esg_reveals=0,
                              unconfirmed_network_documents=0, section_dead=0,
                              expansion_budget_hits=0, detail_pagination_skipped=0,
                              url_fallbacks=0)
        self.stats = dict(duplicates=0, pagination_detected=0, pagination_limits=0, pagination_states=0,
                          load_more=0, year_switches=0, max_depth=0, documents=0)
        self._lock = asyncio.Lock()
        self.db = sqlite3.connect(self.out / 'crawler.db', timeout=30, isolation_level=None,
                                  check_same_thread=False)
        self.db.row_factory = sqlite3.Row
        self.init_db()

    # ---------------- URL normalization ----------------
    def norm_seed(self, u):
        u = (u or '').strip()
        u = u if re.match(r'^https?://', u, re.I) else 'https://' + u
        p = urlsplit(u)
        if not p.hostname:
            raise ValueError(f'Valid website URL required, got {u!r}')
        return urlunsplit((p.scheme.lower(), p.netloc.lower(), p.path or '/', p.query, ''))

    def norm(self, u, base=None, parent_view=False):
        """Canonical form used for de-duplication only (never for opening).
        parent_view=True additionally strips pagination keys."""
        try:
            p = urlsplit(urljoin(base or self.seed, (u or '').strip()))
            if p.scheme.lower() not in ('http', 'https') or not p.hostname:
                return None
            scheme = p.scheme.lower()
            host = p.hostname.lower().rstrip('.')
            port = p.port
            net = host if port is None or (scheme == 'http' and port == 80) or \
                (scheme == 'https' and port == 443) else f'{host}:{port}'
            path = re.sub('/+', '/', p.path or '/')
            tail = path.rsplit('/', 1)[-1]
            if path != '/' and not path.endswith('/') and '.' not in tail:
                path += '/'
            remove = {x.lower() for x in self.cfg.remove_query_parameters}
            keep = {x.lower() for x in self.cfg.keep_meaningful_query_parameters}
            q = []
            for k, v in parse_qsl(p.query, keep_blank_values=True):
                kl = k.lower()
                if kl in remove or kl.startswith('utm_'):
                    continue
                if parent_view and kl in PKEYS:
                    continue
                if self.cfg.query_parameter_mode == 'whitelist' and keep and kl not in keep:
                    continue
                q.append((k, v))
            q.sort(key=lambda x: (x[0].lower(), x[1]))
            return urlunsplit((scheme, net, path, urlencode(q, doseq=True), ''))
        except (ValueError, UnicodeError):
            return None

    def internal(self, u):
        h = (urlsplit(u).hostname or '').lower()
        allowed = {x.lower() for x in self.cfg.allowed_hosts}
        return h in allowed or h == self.host or (
            self.cfg.crawl_subdomains and (h == self.base or h.endswith('.' + self.base)))

    def doclike(self, u):
        """Broad: worth a HEAD check (includes /documents/ style folders)."""
        if ext(u) in DOC_EXT or DOC_HINT.search(u or ''):
            return True
        for k, v in parse_qsl(urlsplit(u or '').query, keep_blank_values=True):
            if k.lower() in VIEWER_PARAMS and v and (ext(v) in DOC_EXT or DOC_HINT.search(v)):
                return True
        return False

    def filelike(self, u):
        """Strict: certainly a file, never crawl it as a page."""
        if ext(u) in DOC_EXT or DOC_FILE_HINT.search(u or ''):
            return True
        for k, v in parse_qsl(urlsplit(u or '').query, keep_blank_values=True):
            if k.lower() in VIEWER_PARAMS and v and (ext(v) in DOC_EXT or DOC_FILE_HINT.search(v)):
                return True
        return self.document_cache.get(u) is True

    def viewer_target(self, u):
        """If u is an embedded-viewer wrapper, return the real document URL."""
        for k, v in parse_qsl(urlsplit(u or '').query, keep_blank_values=True):
            if k.lower() in VIEWER_PARAMS and v and (ext(v) in DOC_EXT or DOC_HINT.search(v)):
                return urljoin(u, v)
        return None

    def is_detail(self, u):
        """Article/detail URL: dated path, numeric id or long slug.
        v5: a URL that names a document hub (financial-results, investor-...,
        corporate-governance-policies, ...) is never treated as a detail page."""
        path = urlsplit(u or '').path or ''
        if not DETAIL_RX.search(path):
            return False
        return not match_vocab(canon(path), V_DOC_HUB)

    def policy(self, u):
        if not self.internal(u):
            return False, 'external'
        path = (urlsplit(u).path or '/').lower()
        target_host = (urlsplit(u).hostname or '').lower()
        if self.cfg.restrict_to_seed_language and self.language_prefix and \
                target_host == self.host and not path.startswith(self.language_prefix) and path != '/':
            return False, 'outside seed language path ' + self.language_prefix
        if ext(u) in ASSET_EXT:
            return False, 'static asset'
        if self.filelike(u):
            return False, 'document'
        if UNSAFE.search(urlsplit(u).path or ''):
            return False, 'unsafe route'
        if self.cfg.respect_robots_txt and self.robots.loaded and not self.robots.allowed(u):
            return False, 'blocked by robots.txt'
        return True, ''

    # ---------------- schema ----------------
    def init_db(self):
        self.db.executescript("""
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous=NORMAL;
        PRAGMA busy_timeout=30000;
        CREATE TABLE IF NOT EXISTS pages(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            seed_url TEXT NOT NULL, page_url TEXT NOT NULL,
            normalized_url TEXT NOT NULL UNIQUE, parent_url TEXT, link_text TEXT,
            priority INTEGER NOT NULL DEFAULT 2, depth INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'DISCOVERED', page_type TEXT,
            document_found INTEGER NOT NULL DEFAULT 0, document_count INTEGER NOT NULL DEFAULT 0,
            http_status INTEGER,
            pagination_detected INTEGER NOT NULL DEFAULT 0,
            pagination_pages_checked INTEGER NOT NULL DEFAULT 1,
            pagination_limit_reached INTEGER NOT NULL DEFAULT 0,
            document_url TEXT, document_source TEXT,
            url_family TEXT, query_path TEXT, has_query INTEGER NOT NULL DEFAULT 0,
            attempts INTEGER NOT NULL DEFAULT 0,
            discovered_order INTEGER, processed_order INTEGER,
            discovered_at TEXT, processed_at TEXT, error_message TEXT);
        CREATE TABLE IF NOT EXISTS links(
            id INTEGER PRIMARY KEY AUTOINCREMENT, from_url TEXT NOT NULL, to_url TEXT NOT NULL,
            normalized_to_url TEXT NOT NULL, link_text TEXT, discovered_at TEXT,
            UNIQUE(from_url,normalized_to_url));
        CREATE TABLE IF NOT EXISTS document_evidence(
            id INTEGER PRIMARY KEY AUTOINCREMENT, source_url TEXT NOT NULL, document_url TEXT NOT NULL,
            detection_source TEXT NOT NULL, link_text TEXT, detected_at TEXT NOT NULL,
            UNIQUE(source_url,document_url));
        CREATE TABLE IF NOT EXISTS performance(
            id INTEGER PRIMARY KEY AUTOINCREMENT, source_url TEXT NOT NULL, page_type TEXT,
            http_status INTEGER, total_seconds REAL, navigation_seconds REAL,
            stabilization_seconds REAL, interaction_seconds REAL, scan_seconds REAL,
            other_seconds REAL, retry_count INTEGER, recorded_at TEXT);
        CREATE TABLE IF NOT EXISTS crawl_counters(name TEXT PRIMARY KEY, value INTEGER NOT NULL DEFAULT 0);
        CREATE TABLE IF NOT EXISTS priority_audit(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            seed_url TEXT NOT NULL,
            parent_url TEXT,
            candidate_url TEXT NOT NULL,
            link_text TEXT,
            source TEXT,
            depth INTEGER,
            priority INTEGER,
            strong_esg INTEGER NOT NULL DEFAULT 0,
            negative_match INTEGER NOT NULL DEFAULT 0,
            gateway_match INTEGER NOT NULL DEFAULT 0,
            document_hub_match INTEGER NOT NULL DEFAULT 0,
            url_family TEXT,
            decision TEXT NOT NULL,
            reason TEXT,
            recorded_at TEXT NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_priority_decision ON priority_audit(decision,priority);
        CREATE INDEX IF NOT EXISTS idx_priority_candidate ON priority_audit(candidate_url);
        CREATE INDEX IF NOT EXISTS idx_pages_queue  ON pages(status,priority,depth,discovered_order);
        CREATE INDEX IF NOT EXISTS idx_pages_family ON pages(url_family,status);
        CREATE INDEX IF NOT EXISTS idx_pages_qpath  ON pages(query_path,has_query,status);
        CREATE INDEX IF NOT EXISTS idx_pages_status ON pages(status);
        CREATE INDEX IF NOT EXISTS idx_pages_type   ON pages(page_type);
        CREATE INDEX IF NOT EXISTS idx_evidence_src ON document_evidence(source_url);
        """)

    def recover_orphans(self):
        """Requeue rows left in PROCESSING by a hard kill."""
        if not self.cfg.recover_orphaned_pages:
            return
        n = self.db.execute(
            "UPDATE pages SET status='DISCOVERED',error_message='Requeued after interrupted run' "
            "WHERE status='PROCESSING'").rowcount
        if n:
            self.expansion['orphans_recovered'] += n
            logging.info('Recovered %s orphaned PROCESSING page(s)', n)

    # ---------------- classification ----------------
    def url_family(self, u):
        p = urlsplit(u)
        parts = [x for x in (p.path or '').lower().split('/') if x]
        host = (p.hostname or '').lower()
        if not parts:
            return host + '/'

        def variable(x):
            if x.isdigit() or YEAR.fullmatch(x):
                return True
            if len(x) > 24 and ('-' in x or '_' in x):
                return True
            if re.fullmatch(r'[0-9a-f]{8,}', x):
                return True
            return False

        normalized = ['{detail}' if variable(x) and i >= 1 else x for i, x in enumerate(parts)]
        if len(normalized) >= 4:
            normalized = normalized[:3] + ['{detail}']
        return host + '/' + '/'.join(normalized) + '/'

    def query_path(self, u):
        p = urlsplit(u)
        return p.scheme + '://' + p.netloc + p.path

    def signals(self, u, text=''):
        p = urlsplit(u or '')
        tokens = canon((p.path or '') + ' ' + (p.query or '') + ' ' + (text or ''))
        strong = match_vocab(tokens, V_STRONG)
        negative = match_vocab(tokens, V_NEGATIVE)
        gateway = match_vocab(tokens, V_GATEWAY)
        dochub = match_vocab(tokens, V_DOC_HUB)
        return strong, negative, gateway, dochub

    def soft(self, u, text=''):
        """News / blog / events style link (low priority, never blocked)."""
        p = urlsplit(u or '')
        return match_vocab(canon((p.path or '') + ' ' + (text or '')), V_SOFT)

    def path_blocked(self, u, text=''):
        """Only HARD negatives and shop folders are blocked. The URL path wins over
        link text; a hub/ESG word in the path keeps the URL alive."""
        segs = [s for s in (urlsplit(u or '').path or '').split('/') if s]
        if segs and self.language_prefix and '/' + segs[0].lower() + '/' == self.language_prefix:
            segs = segs[1:]
        if len(segs) >= 2 and segs[0].lower() in ECOM_FOLDERS:
            return True
        for seg in segs[:-1]:
            toks = canon(seg)
            if match_vocab(toks, V_NEGATIVE) and not match_vocab(toks, V_STRONG) and \
                    not match_vocab(toks, V_DOC_HUB):
                return True
        path_tokens = canon(urlsplit(u or '').path or '')
        if match_vocab(path_tokens, V_NEGATIVE) and not match_vocab(path_tokens, V_STRONG) and \
                not match_vocab(path_tokens, V_DOC_HUB):
            return True
        if segs:
            return False
        strong, negative, _, dochub = self.signals(u, text)
        return negative and not strong and not dochub

    def priority(self, u, text=''):
        # Detail pages (product / article) only get high priority from their real
        # folders, not from the product or article title.
        if self.is_detail(u):
            segs = [x for x in (urlsplit(u).path or '').split('/') if x][:-1]
            folders = [x for x in segs if not x.isdigit() and not (len(x) > 24 and '-' in x)]
            f_toks = canon(' '.join(folders))
            if match_vocab(f_toks, V_STRONG) or match_vocab(f_toks, V_DOC_HUB):
                return 1
            return 8 if self.soft(u, '') else 3
        strong, negative, gateway, dochub = self.signals(u, text)
        host = (urlsplit(u or '').hostname or '').lower()
        if strong and dochub:
            return 0
        if strong:
            return 0
        if host != self.host and any(k in host for k in ('investor', 'esg', 'sustain', 'responsib', 'ir.')):
            return 0
        if dochub and self.cfg.prioritize_document_likely_pages:
            return 1
        if self.soft(u, text):
            return 8
        if gateway:
            return 2
        return 3

    # ---------------- section zero-yield ----------------
    def section_prefix(self, u):
        """Top-level section of a URL: /p/name/id/ gives /p/ and /en/news/x/ gives /en/news/.
        ESG / about / investor / report sections are judged one level deeper
        (/sustainability/reports/) so one empty sub-area cannot kill them."""
        p = urlsplit(u)
        parts = [x for x in (p.path or '').split('/') if x]
        lang = []
        if parts and self.language_prefix and '/' + parts[0].lower() + '/' == self.language_prefix:
            lang, parts = parts[:1], parts[1:]
        if len(parts) < 2:
            return None
        keep = 1
        toks = canon(parts[0])
        if match_vocab(toks, V_STRONG) or match_vocab(toks, V_GATEWAY) or match_vocab(toks, V_DOC_HUB):
            keep = 2
            if len(parts) < 3:
                return None
        return f'{p.scheme}://{p.netloc}/' + '/'.join(lang + parts[:keep]) + '/'

    def section_is_dead(self, u):
        """Prefix once section_probe_pages pages under the same section were processed
        and none of them held a document; otherwise None."""
        prefix = self.section_prefix(u)
        if not prefix:
            return None
        done, hits = self.db.execute(
            "SELECT COUNT(*), COALESCE(SUM(document_found),0) FROM pages "
            "WHERE status='PROCESSED' AND substr(normalized_url,1,?)=?",
            (len(prefix), prefix)).fetchone()
        return prefix if (done >= self.cfg.section_probe_pages and hits == 0) else None

    # ---------------- counters / budgets ----------------
    def increment_counter(self, name, amount=1):
        self.expansion[name] = self.expansion.get(name, 0) + amount
        self.db.execute('INSERT INTO crawl_counters(name,value) VALUES(?,?) '
                        'ON CONFLICT(name) DO UPDATE SET value=value+excluded.value', (name, amount))

    def family_count(self, family):
        return self.db.execute("SELECT COUNT(*) FROM pages WHERE url_family=? AND status!='SKIPPED'",
                               (family,)).fetchone()[0]

    def query_variant_count(self, u):
        return self.db.execute("SELECT COUNT(*) FROM pages WHERE query_path=? AND has_query=1 "
                               "AND status!='SKIPPED'", (self.query_path(u),)).fetchone()[0]

    def live_count(self):
        return self.db.execute("SELECT COUNT(*) FROM pages WHERE status!='SKIPPED'").fetchone()[0]

    def audit_priority(self, candidate_url, parent_url, link_text, source, depth,
                       priority, strong, negative, gateway, dochub, decision, reason=''):
        family = self.url_family(candidate_url) if candidate_url else ''
        self.db.execute(
            'INSERT INTO priority_audit(seed_url,parent_url,candidate_url,link_text,source,depth,'
            'priority,strong_esg,negative_match,gateway_match,document_hub_match,url_family,'
            'decision,reason,recorded_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)',
            (self.seed, parent_url, candidate_url, (link_text or '')[:500], source, depth,
             priority, int(strong), int(negative), int(gateway), int(dochub), family,
             decision, reason, now()))

    # ---------------- discovery ----------------
    def add(self, u, parent, text, depth, priority=None, source='link'):
        n = self.norm(u, parent or self.seed)
        if not n:
            return False
        # v5: keep the real absolute URL (original slash / query) for opening.
        open_url = strip_fragment(urljoin(parent or self.seed, (u or '').strip()))
        text = (text or '')[:500]
        strong, negative, gateway, dochub = self.signals(n, text)
        if priority is None:
            priority = self.priority(n, text)
        if parent:
            self.db.execute('INSERT OR IGNORE INTO links(from_url,to_url,normalized_to_url,link_text,'
                            'discovered_at) VALUES(?,?,?,?,?)', (parent, open_url, n, text, now()))
        if self.db.execute('SELECT 1 FROM pages WHERE normalized_url=?', (n,)).fetchone():
            self.stats['duplicates'] += 1
            self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                                gateway, dochub, 'IGNORED', 'DUPLICATE_NORMALIZED_URL')
            return False
        if source != 'seed' and self.path_blocked(n, text):
            self.increment_counter('negative')
            self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                                gateway, dochub, 'IGNORED', 'NEGATIVE_PATH_OR_TEXT')
            return False
        ok, why = self.policy(n)
        if not ok and why == 'blocked by robots.txt':
            self.increment_counter('robots_blocked')
        if self.live_count() >= self.cfg.max_pages_per_website:
            self.page_limit = True
            self.increment_counter('after_page_limit')
            self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                                gateway, dochub, 'IGNORED', 'TOTAL_PAGE_LIMIT')
            return False
        family = self.url_family(n)
        qpath = self.query_path(n)
        has_query = 1 if urlsplit(n).query else 0
        # Priority 0 gets a larger allowance, never an unlimited one.
        qv_cap = self.cfg.max_query_variants_per_path * (2 if priority <= 1 else 1)
        fam_cap = self.cfg.max_pages_per_url_family * (3 if priority <= 1 else 1)
        if ok and source != 'seed' and has_query and self.query_variant_count(n) >= qv_cap:
            self.increment_counter('query_limit')
            self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                                gateway, dochub, 'IGNORED', 'QUERY_VARIANT_LIMIT')
            return False
        if ok and source != 'seed' and self.family_count(family) >= fam_cap:
            self.increment_counter('family_limit')
            self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                                gateway, dochub, 'IGNORED', 'URL_FAMILY_LIMIT')
            return False
        status, typ, err = 'DISCOVERED', None, None
        if depth > self.cfg.max_depth:
            status, typ, err = 'SKIPPED', 'SKIPPED', 'Beyond maximum depth'
        elif not ok:
            status, typ, err = 'SKIPPED', 'SKIPPED', why
        order = self.db.execute('SELECT COALESCE(MAX(discovered_order),0)+1 FROM pages').fetchone()[0]
        try:
            self.db.execute(
                'INSERT INTO pages(seed_url,page_url,normalized_url,parent_url,link_text,priority,depth,'
                'status,page_type,url_family,query_path,has_query,discovered_order,discovered_at,'
                'error_message) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)',
                (self.seed, open_url, n, parent, text, priority, depth, status, typ, family, qpath,
                 has_query, order, now(), err))
        except sqlite3.IntegrityError:
            self.stats['duplicates'] += 1
            self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                                gateway, dochub, 'IGNORED', 'DUPLICATE_INSERT_RACE')
            return False
        if priority == 0:
            self.increment_counter('esg_priority')
        decision = 'QUEUED' if status == 'DISCOVERED' else 'SKIPPED'
        self.audit_priority(n, parent, text, source, depth, priority, strong, negative,
                            gateway, dochub, decision, err or 'ACCEPTED')
        logging.info('Discovered [%s] p=%s d=%s src=%s %s', status, priority, depth, source, open_url)
        return status == 'DISCOVERED'

    def claim_next(self):
        """Atomic claim, shallow best-first. Rows inside a section that has already
        proven zero-yield (and that are not document hubs) are skipped here."""
        self.db.execute('BEGIN IMMEDIATE')
        try:
            chosen = None
            for _ in range(500):  # bounded skip loop
                row = self.db.execute(
                    "SELECT * FROM pages WHERE status='DISCOVERED' "
                    "ORDER BY priority ASC, depth ASC, discovered_order ASC LIMIT 1").fetchone()
                if not row:
                    break
                url = row['normalized_url']
                strong, negative, gateway, dochub = self.signals(url, row['link_text'] or '')
                dead = None
                if row['depth'] > 0 and not dochub:
                    dead = self.section_is_dead(url)
                if dead:
                    self.db.execute(
                        "UPDATE pages SET status='SKIPPED',page_type='SKIPPED',error_message=? WHERE id=?",
                        ('Section zero-yield: ' + dead, row['id']))
                    self.increment_counter('section_dead')
                    self.audit_priority(url, row['parent_url'], row['link_text'] or '', 'queue',
                                        row['depth'], row['priority'], strong, negative, gateway,
                                        dochub, 'SKIPPED', 'SECTION_ZERO_YIELD')
                    continue
                self.db.execute("UPDATE pages SET status='PROCESSING',attempts=attempts+1 WHERE id=?",
                                (row['id'],))
                self.audit_priority(url, row['parent_url'], row['link_text'] or '',
                                    'queue', row['depth'], row['priority'], strong, negative,
                                    gateway, dochub, 'CLAIMED', 'SELECTED_BY_PRIORITY_DEPTH_ORDER')
                chosen = row
                break
            self.db.execute('COMMIT')
            return chosen
        except Exception:
            self.db.execute('ROLLBACK')
            raise

    def expired(self):
        if self.stop:
            return True
        t = time.monotonic()
        budget = min(self.cfg.max_runtime_minutes, self.cfg.max_minutes_per_website) * 60
        if t - self.started >= budget:
            logging.warning('Site time budget reached (%s min): %s',
                            self.cfg.max_minutes_per_website, self.seed)
            self.runtime_limit = True
            self.stop = True
        elif t - self.last_progress >= self.cfg.stall_minutes * 60:
            logging.warning('No page finished for %s min; stopping site: %s',
                            self.cfg.stall_minutes, self.seed)
            self.stop = True
        return self.stop

    def out_of_time(self, deadline):
        if self.expired():
            return True
        if deadline is not None and time.monotonic() > deadline:
            self.expansion['expansion_budget_hits'] += 1
            return True
        return False

    # ---------------- sitemap seeding ----------------
    async def seed_from_sitemap(self, ctx):
        if not self.cfg.use_sitemap:
            return
        origin = '{0.scheme}://{0.netloc}'.format(urlsplit(self.seed))
        queue = list(dict.fromkeys(
            [s for s in self.robots.sitemaps if s.startswith('http')] +
            [origin + '/sitemap.xml', origin + '/sitemap_index.xml']))
        seen, fetched, added, neutral_added = set(), 0, 0, 0
        while queue and fetched < self.cfg.max_sitemaps and added < self.cfg.max_sitemap_urls:
            sm = queue.pop(0)
            if sm in seen:
                continue
            seen.add(sm)
            fetched += 1
            try:
                r = await ctx.request.get(sm, timeout=15000, fail_on_status_code=False)
                if r.status >= 400:
                    continue
                body = await r.text()
            except (PWError, PWTimeout, UnicodeDecodeError):
                continue
            locs = re.findall(r'<loc>\s*([^<\s]+)\s*</loc>', body, re.I)
            is_index = '<sitemapindex' in body[:4000].lower()
            for loc in locs:
                if added >= self.cfg.max_sitemap_urls:
                    break
                loc = loc.replace('&amp;', '&')
                if is_index or re.search(r'sitemap[^/]*\.xml(?:\.gz)?$', loc, re.I):
                    if len(queue) + fetched < self.cfg.max_sitemaps:
                        queue.append(loc)
                    continue
                n = self.norm(loc, sm)
                if not n or not self.internal(n):
                    continue
                if self.filelike(n):
                    if self.cfg.sitemap_document_folders:
                        parent = urljoin(n, '.')
                        if self.norm(parent) and self.internal(parent):
                            if self.add(parent, self.seed, 'sitemap document folder', 1, 0, 'sitemap'):
                                added += 1
                    continue
                if self.path_blocked(n):
                    continue
                rank = self.priority(n)
                if rank > 2:
                    if neutral_added >= self.cfg.max_neutral_sitemap_urls:
                        continue
                    neutral_added += 1
                if self.add(loc, self.seed, 'sitemap', 1, rank, 'sitemap'):
                    added += 1
        if added:
            self.increment_counter('sitemap_seeded', added)
            logging.info('Sitemap seeding added %s URL(s) from %s sitemap file(s)', added, fetched)

    async def load_robots(self, ctx):
        if not (self.cfg.respect_robots_txt or self.cfg.use_sitemap):
            return
        origin = '{0.scheme}://{0.netloc}'.format(urlsplit(self.seed))
        try:
            r = await ctx.request.get(origin + '/robots.txt', timeout=12000, fail_on_status_code=False)
            if r.status < 400:
                self.robots.parse(await r.text())
                logging.info('robots.txt loaded: %s rule(s), %s sitemap hint(s)',
                             len(self.robots.rules), len(self.robots.sitemaps))
            else:
                logging.info('robots.txt not available (HTTP %s); no restrictions applied', r.status)
        except (PWError, PWTimeout, UnicodeDecodeError) as exc:
            logging.info('robots.txt fetch failed (%s); no restrictions applied', type(exc).__name__)

    # ---------------- timing wrappers ----------------
    async def settle(self, p, perf=None):
        started = time.perf_counter()
        try:
            await p.wait_for_timeout(int(self.cfg.stabilization_seconds * 1000))
        except PWError:
            pass
        if perf is not None:
            perf['stabilization'] += time.perf_counter() - started

    async def timed_goto(self, p, u, perf=None):
        started = time.perf_counter()
        try:
            return await p.goto(u, wait_until='domcontentloaded',
                                timeout=self.cfg.page_timeout_seconds * 1000)
        finally:
            if perf is not None:
                perf['navigation'] += time.perf_counter() - started

    def record_perf(self, u, page_type, status, started, retry_count, perf=None):
        perf = perf or {'navigation': 0.0, 'stabilization': 0.0, 'interaction': 0.0, 'scan': 0.0}
        total = time.perf_counter() - started
        known = perf['navigation'] + perf['stabilization'] + perf['interaction'] + perf['scan']
        self.db.execute(
            'INSERT INTO performance(source_url,page_type,http_status,total_seconds,navigation_seconds,'
            'stabilization_seconds,interaction_seconds,scan_seconds,other_seconds,retry_count,recorded_at)'
            ' VALUES(?,?,?,?,?,?,?,?,?,?,?)',
            (u, page_type, status, total, perf['navigation'], perf['stabilization'],
             perf['interaction'], perf['scan'], max(0.0, total - known), retry_count, now()))

    # ---------------- page interactions ----------------
    async def cookie(self, p):
        try:
            for role in ('button', 'link'):
                loc = p.get_by_role(role).filter(has_text=COOKIE)
                for i in range(min(await loc.count(), 8)):
                    el = loc.nth(i)
                    if await el.is_visible():
                        await el.click(timeout=1200)
                        return True
        except PWError:
            pass
        return False

    async def reveal(self, p):
        """Reveal bounded navigation controls, then document-section controls. Buttons and
        summaries only are clicked; ordinary anchors are never activated."""
        clicked = False
        clicked_keys = set()
        click_count = 0
        page_path = urlsplit(p.url).path or '/'
        is_host_homepage = page_path.rstrip('/') == ''
        selectors = (
            "header button:not([type=submit]),header [role=button],header summary,"
            "button[aria-haspopup=menu],[role=button][aria-haspopup=menu],"
            "main button:not([type=submit]),main [role=button],main summary,"
            "article button:not([type=submit]),article [role=button],article summary,"
            "[role=main] button:not([type=submit]),[role=main] [role=button],[role=main] summary,"
            "[role=tab]"
        )
        for stage in ('menu', 'esg'):
            while click_count < self.cfg.max_esg_navigation_clicks_per_page:
                candidate = None
                label = ''
                key = None
                try:
                    loc = p.locator(selectors)
                    for i in range(min(await loc.count(), 100)):
                        el = loc.nth(i)
                        try:
                            text = ((await el.inner_text(timeout=350)) or
                                    await el.get_attribute('aria-label') or
                                    await el.get_attribute('title') or '').strip()
                            identity = (text.lower(), await el.get_attribute('id') or '',
                                        await el.get_attribute('class') or '')
                            if identity in clicked_keys or not await el.is_visible():
                                continue
                            if await el.get_attribute('aria-expanded') == 'true' or \
                                    await el.get_attribute('aria-selected') == 'true':
                                continue
                            if stage == 'menu' and is_host_homepage and MENU_NAV.search(text):
                                candidate, label, key = el, text, identity
                                break
                            if stage == 'esg' and ESG_NAV.search(text):
                                candidate, label, key = el, text, identity
                                break
                        except PWError:
                            continue
                    if candidate is None:
                        break
                    before = len(await self.links(p))
                    await candidate.click(timeout=1200)
                    clicked_keys.add(key)
                    click_count += 1
                    clicked = True
                    await p.wait_for_timeout(250)
                    after = len(await self.links(p))
                    self.increment_counter('esg_reveals')
                    logging.info('Navigation revealed label=%s new_links=%s page=%s',
                                 label, max(0, after - before), p.url)
                except PWError:
                    break
        return clicked

    async def links(self, p):
        """Every link on the page. Label format: 'card heading | anchor text'."""
        out, seen = [], set()
        for f in p.frames:
            if f != p.main_frame and f.url and not self.internal(f.url):
                continue
            try:
                vals = await f.locator('a[href],area[href],[data-href],[data-url],[data-link],[data-target]').evaluate_all(
                    "els=>els.slice(0,4000).map(e=>{"
                    "const u=e.href||e.getAttribute('data-href')||e.getAttribute('data-url')||"
                    "e.getAttribute('data-link')||e.getAttribute('data-target')||'';"
                    "const card=e.closest('article,.card,.item,.row,li,section,div');"
                    "const heading=card?card.querySelector('h1,h2,h3,h4,h5,h6,.title,.heading'):null;"
                    "const own=(e.innerText||e.textContent||e.getAttribute('aria-label')||e.title||'').trim();"
                    "const head=heading?(heading.textContent||'').trim():'';"
                    "const label=head?(head+' | '+own):own;"
                    "try{return [new URL(u,document.baseURI).href,label]}catch(_){return ['',label]}})")
            except PWError:
                continue
            src = 'page' if f == p.main_frame else 'iframe'
            for u, t in vals:
                if u and u not in seen and not u.lower().startswith(('javascript:', 'mailto:', 'tel:')):
                    seen.add(u)
                    out.append((u, (t or '')[:500], src))
        return out

    async def content_document_links(self, p):
        """Document candidates from the whole page except shared chrome
        (header / footer / nav / cookie banners). v5: no longer limited to
        <main>, and also reads onclick / data-* attributes."""
        out, seen = [], set()
        blocked = ("header,footer,nav,[role=navigation],[role=banner],[role=contentinfo],"
                   ".navbar,.nav-menu,.main-menu,.mega-menu,.cookie,.cookies,"
                   ".cookie-banner,.cookie-consent,.social,.share")
        js = ("els=>els.filter(a=>!a.closest('%s'))"
              ".map(a=>[a.href,(a.innerText||a.textContent||a.getAttribute('aria-label')||a.title||'').trim()])"
              % blocked)
        attrs = ("els=>els.filter(e=>!e.closest('%s')).map(e=>{"
                 "const v=[e.getAttribute('onclick'),e.getAttribute('data-href'),e.getAttribute('data-url'),"
                 "e.getAttribute('data-file'),e.getAttribute('data-pdf'),e.getAttribute('data-src'),"
                 "e.getAttribute('data-link'),e.getAttribute('data-download'),e.getAttribute('value')]"
                 ".filter(Boolean).join(' ');"
                 "return [v,(e.innerText||e.textContent||e.getAttribute('aria-label')||'').trim().slice(0,300)]})"
                 % blocked)
        embeds = ("els=>els.map(e=>[e.src||e.data||'',(e.getAttribute('title')||e.getAttribute('aria-label')"
                  "||e.tagName).trim()]).filter(x=>x[0])")
        for f in p.frames:
            if f != p.main_frame and f.url and not self.internal(f.url):
                continue
            is_main = f == p.main_frame
            src = 'main_content' if is_main else 'iframe_main_content'
            try:
                vals = list(await f.locator('a[href],area[href]').evaluate_all(js))
            except PWError:
                vals = []
            try:
                vals += list(await f.locator('embed[src],object[data],iframe[src]').evaluate_all(embeds))
            except PWError:
                pass
            for u, t in vals:
                if u and u not in seen:
                    seen.add(u)
                    out.append((u, (t or '')[:500], src))
            try:
                attr_vals = await f.locator(
                    '[onclick],[data-href],[data-url],[data-file],[data-pdf],[data-src],'
                    '[data-link],[data-download],option[value]').evaluate_all(attrs)
            except PWError:
                attr_vals = []
            base = f.url or p.url
            for blob, t in attr_vals:
                for m in ATTR_DOC_RX.finditer(blob or ''):
                    u = urljoin(base, (m.group(2) or m.group(3) or '').strip())
                    if u not in seen and u.startswith('http'):
                        seen.add(u)
                        out.append((u, (t or '')[:500], src + '_attribute'))
        return out

    async def confirm(self, ctx, u):
        """HEAD-verify a candidate; ranged GET fallback on 403/405/501."""
        if u in self.document_cache:
            return self.document_cache[u]
        if ext(u) in DOC_EXT:
            self.document_cache[u] = True
            return True
        found = False
        timeout = self.cfg.document_head_timeout_seconds * 1000
        try:
            r = await ctx.request.head(u, timeout=timeout, fail_on_status_code=False)
            headers = r.headers
            if r.status in (403, 405, 501):
                r = await ctx.request.get(u, timeout=timeout, fail_on_status_code=False,
                                          headers={'Range': 'bytes=0-1023'})
                headers = r.headers
            ct = (headers.get('content-type') or '').lower()
            cd = (headers.get('content-disposition') or '').lower()
            if 'application/octet-stream' in ct:
                found = bool(DOC_FILE_HINT.search(u) or ext(u) in DOC_EXT or 'attachment' in cd)
            else:
                found = any(x in ct for x in DOC_MIME if x != 'application/octet-stream') or \
                    'attachment' in cd
        except (PWError, PWTimeout):
            pass
        self.document_cache[u] = found
        return found

    def is_pagination(self, candidate, parent, text=''):
        anchor, _ = split_label(text)
        q = dict(parse_qsl(urlsplit(candidate).query))
        if any(k.lower() in PKEYS for k in q) and \
                self.norm(candidate, parent_view=True) == self.norm(parent, parent_view=True):
            return True
        if (NEXT.match(anchor) or NEXT_SYMBOL.match(anchor)) and not YEAR.fullmatch(anchor) and \
                urlsplit(candidate).path.rstrip('/') == urlsplit(parent).path.rstrip('/'):
            return True
        return path_page_num(urlsplit(candidate).path) is not None

    # ---------------- scanning ----------------
    async def timed_scan(self, p, ctx, parent, depth, response_docs, perf=None):
        started = time.perf_counter()
        try:
            return await self.scan(p, ctx, parent, depth, response_docs)
        finally:
            if perf is not None:
                perf['scan'] += time.perf_counter() - started

    async def scan(self, p, ctx, parent, depth, response_docs):
        """Returns (documents, all_links)."""
        all_links = await self.links(p)
        documents, seen_docs = [], set()
        cap = self.cfg.max_documents_per_page
        # Network responses are audit-only; DOM evidence is required.
        if response_docs:
            self.increment_counter('unconfirmed_network_documents', len(response_docs))
        # 1) Content links + embedded viewers + onclick/data attributes.
        for u, text, src in await self.content_document_links(p):
            if len(documents) >= cap:
                break
            target = self.viewer_target(u) or u
            if target in seen_docs:
                continue
            if self.doclike(target) and await self.confirm(ctx, target):
                seen_docs.add(target)
                documents.append((target, src if target == u else src + '_embedded_viewer', text))
        for u, src, text in documents[:20]:
            logging.info('Document evidence source=%s page=%s document=%s', src, parent, u)
        if len(documents) > 20:
            logging.info('... plus %s more document(s) on %s', len(documents) - 20, parent)
        # 2) Child discovery.
        candidates, seen = [], set()
        parent_family = self.url_family(parent)
        parent_parts = [x for x in urlsplit(parent).path.split('/') if x]
        parent_is_detail = self.is_detail(parent) or len(parent_parts) >= 4
        _, _, _, parent_dochub = self.signals(parent, '')
        for child, raw_text, _ in all_links:
            n = self.norm(child, parent)
            if not n or n in seen or self.filelike(n) or self.is_pagination(n, parent, raw_text):
                continue
            seen.add(n)
            _, text = split_label(raw_text)
            strong, negative, gateway, dochub = self.signals(n, text)
            rank = self.priority(n, text)
            if self.path_blocked(n, text):
                self.increment_counter('negative')
                self.audit_priority(n, parent, text, 'link', depth + 1, rank, strong, negative,
                                    gateway, dochub, 'IGNORED', 'NEGATIVE_PATH_OR_TEXT')
                continue
            protected_branch = dochub or parent_dochub
            if not protected_branch and parent_is_detail and \
                    not self.cfg.follow_same_family_links_from_detail_pages and \
                    self.url_family(n) == parent_family:
                self.increment_counter('same_family')
                self.audit_priority(n, parent, text, 'link', depth + 1, rank, strong, negative,
                                    gateway, dochub, 'IGNORED', 'SAME_FAMILY_DETAIL_SUPPRESSION')
                continue
            candidates.append((rank, n, text, child))
        candidates.sort(key=lambda x: (x[0], x[1]))
        budget = (self.cfg.max_homepage_children if parent.rstrip('/') == self.seed.rstrip('/')
                  else self.cfg.max_new_children_per_page)
        # v5: fill the page budget in priority order (no per-bucket cap on normal
        # pages); only low-priority news / blog / events links have their own cap.
        normal = [x for x in candidates if x[0] < 8]
        low = [x for x in candidates if x[0] >= 8][:self.cfg.max_low_priority_children_per_page]
        selected = normal[:budget] + low
        for rank, n, text, child in selected:
            self.add(child, parent, text, depth + 1, rank)
        selected_set = {x[1] for x in selected}
        ignored_candidates = [x for x in candidates if x[1] not in selected_set]
        for rank, n, text, _ in ignored_candidates:
            strong, negative, gateway, dochub = self.signals(n, text)
            self.audit_priority(n, parent, text, 'link', depth + 1, rank, strong, negative,
                                gateway, dochub, 'IGNORED', 'PARENT_PRIORITY_BUDGET')
        if ignored_candidates:
            self.increment_counter('parent_budget', len(ignored_candidates))
        return documents, all_links

    # ---------------- pagination ----------------
    def next_page_candidates(self, links, current, visited):
        """Next-page links, smallest unvisited page number first. Same path only."""
        out = []
        cur_num = 1
        for k, v in parse_qsl(urlsplit(current).query):
            if k.lower() in PKEYS and v.isdigit():
                cur_num = int(v)
                break
        pn = path_page_num(urlsplit(current).path)
        if pn is not None:
            cur_num = pn
        cur_base = PAGE_PATH_RX.sub('/', urlsplit(current).path).rstrip('/')
        for u, t, s in links:
            n = self.norm(u, current)
            if not n or not self.internal(n) or n in visited:
                continue
            anchor, _ = split_label(t)
            num = None
            for k, v in parse_qsl(urlsplit(n).query):
                if k.lower() in PKEYS and v.isdigit():
                    num = int(v)
                    break
            n_path = urlsplit(n).path
            path_num = path_page_num(n_path)
            if num is None:
                num = path_num
            same_path = n_path.rstrip('/') == urlsplit(current).path.rstrip('/')
            same_base = PAGE_PATH_RX.sub('/', n_path).rstrip('/') == cur_base
            is_next_text = bool((NEXT.match(anchor) or NEXT_SYMBOL.match(anchor))
                                and not YEAR.fullmatch(anchor))
            if num is not None and num > cur_num and \
                    self.norm(n, parent_view=True) == self.norm(current, parent_view=True):
                out.append((num, n, anchor, s))
            elif path_num is not None and path_num > cur_num and same_base:
                out.append((path_num, n, anchor, s))
            elif is_next_text and same_path and (num is None or num > cur_num):
                out.append((num if num is not None else cur_num + 1, n, anchor, s))
        out.sort(key=lambda x: x[0])
        dedup, seen = [], set()
        for num, n, text, s in out:
            if n not in seen:
                seen.add(n)
                dedup.append((n, text, s))
        return dedup

    async def signature(self, p):
        """DOM fingerprint (URL excluded so repeated content is detected
        even when the URL changes)."""
        try:
            text = (await p.locator('main,[role=main],body').first.inner_text(timeout=3000))[:100000]
        except PWError:
            text = ''
        try:
            hrefs = await p.locator('a[href]').evaluate_all(
                "e=>e.slice(0,1000).map(a=>a.href).sort().join('\\n')")
        except PWError:
            hrefs = ''
        return hashlib.sha256((text + (hrefs or '')).encode(errors='ignore')).hexdigest()

    def merge_docs(self, documents, docs):
        have = {x[0] for x in documents}
        for d in docs:
            if d[0] not in have and len(documents) < self.cfg.max_documents_per_page:
                documents.append(d)
                have.add(d[0])

    async def crawl_pagination(self, p, ctx, base_url, depth, response_docs, documents, perf, deadline=None):
        """Bounded pagination walk. Brakes: page ceiling, visited set, DOM
        signature set, no-new-links exit, no-candidate exit, time budget."""
        detected = 0
        checked = 1
        limit_reached = 0
        visited = {self.norm(base_url) or base_url}
        signatures = {await self.signature(p)}
        try:
            seen_links = {u for u, _, _ in await self.links(p)}
        except PWError:
            seen_links = set()
        current = base_url
        for _ in range(max(0, self.cfg.max_pagination_pages - 1)):
            if self.out_of_time(deadline):
                break
            try:
                links = await self.links(p)
            except PWError:
                break
            cands = self.next_page_candidates(links, current, visited)
            moved = False
            if cands:
                detected = 1
                target = cands[0][0]
                visited.add(target)
                try:
                    await self.timed_goto(p, target, perf)
                    await self.settle(p, perf)
                    moved = True
                    current = target
                except (PWError, PWTimeout):
                    logging.info('Pagination navigation failed: %s', target)
                    break
            else:
                clicked = False
                try:
                    controls = p.locator("[rel=next],.pagination a,.pagination button,.pager a,"
                                         ".pager button,[aria-label*='next' i],"
                                         "a.next,button.next,li.next>a")
                    for i in range(min(await controls.count(), 20)):
                        el = controls.nth(i)
                        try:
                            text = ((await el.inner_text(timeout=500)) or
                                    await el.get_attribute('aria-label') or '').strip()
                            if not await el.is_visible():
                                continue
                            if await el.get_attribute('aria-disabled') == 'true':
                                continue
                            if await el.is_disabled():
                                continue
                        except PWError:
                            continue
                        low = text.lower()
                        # 'next article' / 'next story' are not pagination.
                        if re.search(r'next\s+(?:article|story|post|news|item|product)', low):
                            continue
                        if NEXT.match(text) or NEXT_SYMBOL.match(text) or 'next' in low:
                            try:
                                await el.click(timeout=3000)
                                await self.settle(p, perf)
                                clicked = True
                                detected = 1
                                new_url = self.norm(p.url) or p.url
                                if new_url in visited and new_url != (self.norm(current) or current):
                                    clicked = False
                                    break
                                current = p.url
                                visited.add(new_url)
                                break
                            except PWError:
                                continue
                except PWError:
                    pass
                if not clicked:
                    break
                moved = True
            if not moved:
                break
            sig = await self.signature(p)
            if sig in signatures:
                logging.info('Pagination signature repeated; stopping walk at %s', current)
                break
            signatures.add(sig)
            checked += 1
            self.stats['pagination_states'] += 1
            docs, links2 = await self.timed_scan(p, ctx, base_url, depth, response_docs, perf)
            self.merge_docs(documents, docs)
            new_links = {u for u, _, _ in links2} - seen_links
            seen_links |= new_links
            if not new_links:
                logging.info('Pagination produced no new links; stopping walk at %s', current)
                break
            if self.next_page_candidates(links2, current, visited):
                limit_reached = 1
        if detected:
            self.stats['pagination_detected'] += 1
        if limit_reached:
            self.stats['pagination_limits'] += 1
        if current != base_url and not self.out_of_time(deadline):
            try:
                await self.timed_goto(p, base_url, perf)
                await self.settle(p, perf)
            except (PWError, PWTimeout):
                pass
        return detected, checked, limit_reached

    async def crawl_load_more(self, p, ctx, base_url, depth, response_docs, documents, perf, deadline=None):
        """Bounded load-more clicking: click ceiling + signature set + time budget."""
        if not self.cfg.max_load_more_clicks:
            return
        signatures = {await self.signature(p)}
        for _ in range(self.cfg.max_load_more_clicks):
            if self.out_of_time(deadline):
                return
            try:
                btn = p.get_by_role('button').filter(has_text=LOAD).first
                if not await btn.is_visible():
                    btn = p.get_by_role('link').filter(has_text=LOAD).first
                    if not await btn.is_visible():
                        return
                await btn.click(timeout=3000)
                await self.settle(p, perf)
            except (PWError, PWTimeout):
                return
            sig = await self.signature(p)
            if sig in signatures:
                return
            signatures.add(sig)
            self.stats['load_more'] += 1
            docs, _ = await self.timed_scan(p, ctx, base_url, depth, response_docs, perf)
            self.merge_docs(documents, docs)

    async def crawl_year_options(self, p, ctx, base_url, depth, response_docs, documents, perf, deadline=None):
        """Bounded year-dropdown select-and-rescan loop."""
        if not self.cfg.max_year_options:
            return
        try:
            selects = p.locator('select')
            count = min(await selects.count(), 5)
        except PWError:
            return
        switched = 0
        for i in range(count):
            if switched >= self.cfg.max_year_options or self.out_of_time(deadline):
                return
            sel = selects.nth(i)
            try:
                if not await sel.is_visible():
                    continue
                options = await sel.locator('option').evaluate_all(
                    "els=>els.map(o=>[o.value,(o.textContent||'').trim()])")
            except PWError:
                continue
            years = [(v, t) for v, t in options if re.search(r'(19|20)\d{2}', (t or '') + ' ' + (v or ''))]
            if not years:
                continue
            years.sort(key=lambda x: (x[1] or x[0]), reverse=True)
            signatures = {await self.signature(p)}
            for value, label in years:
                if switched >= self.cfg.max_year_options or self.out_of_time(deadline):
                    return
                try:
                    await sel.select_option(value=value, timeout=3000)
                    await self.settle(p, perf)
                except (PWError, PWTimeout):
                    continue
                sig = await self.signature(p)
                if sig in signatures:
                    continue
                signatures.add(sig)
                switched += 1
                self.stats['year_switches'] += 1
                logging.info('Year option switched to %s on %s', label or value, base_url)
                docs, _ = await self.timed_scan(p, ctx, base_url, depth, response_docs, perf)
                self.merge_docs(documents, docs)
            return

    # ---------------- page processing ----------------
    def progress(self, current_url):
        done = self.db.execute("SELECT COUNT(*) FROM pages WHERE status IN ('PROCESSED','FAILED')"
                               ).fetchone()[0]
        queued = self.db.execute("SELECT COUNT(*) FROM pages WHERE status='DISCOVERED'").fetchone()[0]
        logging.info('PROGRESS site=%s completed=%s queued=%s documents=%s elapsed=%.1fs current=%s',
                     self.host, done, queued, self.stats['documents'],
                     time.monotonic() - self.started, current_url)

    def fail_row(self, row, message, status=None, started=None, retries=None, perf=None):
        order = self.db.execute('SELECT COALESCE(MAX(processed_order),0)+1 FROM pages').fetchone()[0]
        self.db.execute("UPDATE pages SET status='FAILED',page_type='FAILED',http_status=?,"
                        "processed_order=?,processed_at=?,error_message=? WHERE id=?",
                        (status, order, now(), message[:2000], row['id']))
        if started is not None:
            self.record_perf(row['normalized_url'], 'FAILED', status, started,
                             retries if retries is not None else self.cfg.max_retries, perf)

    async def process_with_watchdog(self, ctx, row):
        """Hard ceiling for one source page; closes only pages this task opened."""
        timeout = self.cfg.page_attempt_timeout_seconds
        started = time.perf_counter()
        owned = []
        try:
            await asyncio.wait_for(self.process(ctx, row, owned), timeout=timeout)
        except asyncio.TimeoutError:
            logging.error('HARD PAGE TIMEOUT after %ss: %s', timeout, row['normalized_url'])
            for pg in list(owned):
                await self.safe_close(pg)
            async with self._lock:
                self.fail_row(row, f'Hard page timeout after {timeout}s', None, started)
        except asyncio.CancelledError:
            for pg in list(owned):
                await self.safe_close(pg)
            raise
        except Exception as exc:
            logging.exception('Page watchdog caught unexpected error for %s', row['normalized_url'])
            for pg in list(owned):
                await self.safe_close(pg)
            async with self._lock:
                self.fail_row(row, f'Watchdog error: {type(exc).__name__}: {exc}', None, started)

    async def safe_close(self, p):
        if p is None:
            return
        try:
            await asyncio.wait_for(p.close(), timeout=self.cfg.page_close_timeout_seconds)
        except (asyncio.TimeoutError, PWError):
            logging.warning('Page close timed out; continuing')

    async def process(self, ctx, row, owned):
        u = row['normalized_url']
        # v5: open the URL exactly as the site linked it; the normalized form
        # (added slash, filtered query) is only a fallback.
        targets = [row['page_url'] or u]
        if u not in targets:
            targets.append(u)
        target_idx = 0
        depth = row['depth']
        self.stats['max_depth'] = max(depth, self.stats['max_depth'])
        page_started = time.perf_counter()
        last = ''
        status = None
        for attempt in range(1, self.cfg.max_retries + 2):
            perf = {'navigation': 0.0, 'stabilization': 0.0, 'interaction': 0.0, 'scan': 0.0}
            open_url = targets[target_idx]
            p = await ctx.new_page()
            owned.append(p)
            response_docs = set()
            status = None

            def on_response(r):
                try:
                    if ext(r.url) in DOC_EXT or DOC_FILE_HINT.search(r.url):
                        response_docs.add(r.url)
                        return
                    ct = (r.headers.get('content-type') or '').lower()
                    cd = (r.headers.get('content-disposition') or '').lower()
                    if any(x in ct for x in DOC_MIME if x != 'application/octet-stream') or \
                            'attachment' in cd:
                        response_docs.add(r.url)
                except Exception:
                    pass

            p.on('response', on_response)
            try:
                logging.info('Opening %s attempt %s', open_url, attempt)
                r = await self.timed_goto(p, open_url, perf)
                status = r.status if r else None
                if status and status >= 400:
                    raise RuntimeError(f'HTTP status {status}')
                ct = ''
                if r:
                    try:
                        ct = (await r.all_headers()).get('content-type', '').lower()
                    except PWError:
                        ct = ''
                if ct and 'text/html' not in ct and 'application/xhtml' not in ct:
                    if any(x in ct for x in DOC_MIME):
                        response_docs.add(r.url if r else open_url)
                    else:
                        raise RuntimeError(f'Unexpected content type {ct}')
                await self.settle(p, perf)
                t0 = time.perf_counter()
                interacted = await self.cookie(p)
                interacted = (await self.reveal(p)) or interacted
                perf['interaction'] += time.perf_counter() - t0
                if interacted:
                    await self.settle(p, perf)
                documents, _ = await self.timed_scan(p, ctx, u, depth, response_docs, perf)
                # Expansion has its own time budget, well inside the watchdog.
                deadline = time.monotonic() + self.cfg.expansion_budget_seconds
                pdet, checked, limit = 0, 1, 0
                if self.is_detail(u):
                    self.expansion['detail_pagination_skipped'] += 1
                else:
                    pdet, checked, limit = await self.crawl_pagination(
                        p, ctx, open_url, depth, response_docs, documents, perf, deadline)
                    await self.crawl_load_more(p, ctx, u, depth, response_docs, documents, perf, deadline)
                await self.crawl_year_options(p, ctx, u, depth, response_docs, documents, perf, deadline)
                found = bool(documents)
                page_type = 'PDF' if found else 'HTML'
                async with self._lock:
                    order = self.db.execute(
                        'SELECT COALESCE(MAX(processed_order),0)+1 FROM pages').fetchone()[0]
                    self.db.execute(
                        "UPDATE pages SET status='PROCESSED',page_type=?,document_found=?,"
                        "document_count=?,http_status=?,pagination_detected=?,"
                        "pagination_pages_checked=?,pagination_limit_reached=?,document_url=?,"
                        "document_source=?,processed_order=?,processed_at=?,error_message=NULL "
                        "WHERE id=?",
                        (page_type, int(found), len(documents), status, pdet, checked, limit,
                         documents[0][0] if documents else None,
                         documents[0][1] if documents else None, order, now(), row['id']))
                    for doc_url, doc_src, doc_text in documents:
                        self.db.execute(
                            'INSERT OR IGNORE INTO document_evidence(source_url,document_url,'
                            'detection_source,link_text,detected_at) VALUES(?,?,?,?,?)',
                            (u, doc_url, doc_src, (doc_text or '')[:500], now()))
                    self.stats['documents'] += len(documents)
                    self.record_perf(u, page_type, status, page_started, attempt - 1, perf)
                logging.info('Classified %s %s documents=%s', page_type, open_url, len(documents))
                await self.safe_close(p)
                if p in owned:
                    owned.remove(p)
                return
            except (PWError, PWTimeout, RuntimeError) as e:
                last = f'{type(e).__name__}: {e}'[:2000]
                logging.warning('Attempt failed %s %s', open_url, last)
                await self.safe_close(p)
                if p in owned:
                    owned.remove(p)
                if self.expired():
                    break
                # Try the other URL form once before giving up on a 4xx.
                if target_idx + 1 < len(targets):
                    target_idx += 1
                    self.expansion['url_fallbacks'] += 1
                    continue
                permanent_4xx = status is not None and 400 <= status < 500 and status not in (408, 429)
                if permanent_4xx:
                    logging.info('Permanent HTTP %s; retries skipped for %s', status, open_url)
                    break
                if attempt <= self.cfg.max_retries:
                    await asyncio.sleep(min(2 ** attempt, 6))
        async with self._lock:
            self.fail_row(row, last or 'Unknown failure', status, page_started, self.cfg.max_retries)

    # ---------------- export ----------------
    def export(self):
        d = self.out
        cols = ('seed_url,page_url,normalized_url,page_type,parent_url,link_text,priority,depth,status,'
                'http_status,document_found,document_count,pagination_detected,'
                'pagination_pages_checked,pagination_limit_reached,document_url,document_source,'
                'url_family,error_message,discovered_at,processed_at').split(',')
        rows = self.db.execute('SELECT ' + ','.join(cols) +
                               ' FROM pages ORDER BY discovered_order').fetchall()

        def dump(name, header, records):
            with open(d / name, 'w', newline='', encoding='utf-8-sig') as f:
                w = csv.writer(f)
                w.writerow(header)
                w.writerows(records)

        with open(d / 'classified_pages.csv', 'w', newline='', encoding='utf-8-sig') as f:
            w = csv.DictWriter(f, fieldnames=cols)
            w.writeheader()
            w.writerows(dict(r) for r in rows)
        dump('pdf_pages.csv', ['source_url', 'document_count'],
             [[r['normalized_url'], r['document_count']] for r in rows if r['page_type'] == 'PDF'])
        dump('html_pages.csv', ['source_url', 'parent_url', 'depth'],
             [[r['normalized_url'], r['parent_url'], r['depth']] for r in rows if r['page_type'] == 'HTML'])
        dump('failed_pages.csv', ['source_url', 'parent_url', 'depth', 'http_status', 'error_message'],
             [[r['normalized_url'], r['parent_url'], r['depth'], r['http_status'], r['error_message']]
              for r in rows if r['status'] == 'FAILED'])
        dump('document_evidence.csv', ['source_url', 'document_url', 'detection_source', 'link_text'],
             self.db.execute('SELECT source_url,document_url,detection_source,link_text '
                             'FROM document_evidence ORDER BY id').fetchall())
        dump('skipped_pages.csv', ['source_url', 'reason', 'depth'],
             [[r['normalized_url'], r['error_message'], r['depth']] for r in rows
              if r['status'] == 'SKIPPED'])
        audit_cols = ['seed_url', 'parent_url', 'candidate_url', 'link_text', 'source', 'depth', 'priority',
                      'strong_esg', 'negative_match', 'gateway_match', 'document_hub_match', 'url_family',
                      'decision', 'reason', 'recorded_at']
        audit_rows = self.db.execute('SELECT ' + ','.join(audit_cols) +
                                     ' FROM priority_audit ORDER BY id').fetchall()
        dump('PRIORITY_REPORT.csv', audit_cols,
             [[r[c] for c in audit_cols] for r in audit_rows])
        perf_cols = ['source_url', 'page_type', 'http_status', 'total_seconds', 'navigation_seconds',
                     'stabilization_seconds', 'interaction_seconds', 'scan_seconds', 'other_seconds',
                     'retry_count']
        perf_rows = self.db.execute('SELECT ' + ','.join(perf_cols) +
                                    ' FROM performance ORDER BY id').fetchall()
        with open(d / 'PERFORMANCE_REPORT.csv', 'w', newline='', encoding='utf-8-sig') as f:
            w = csv.writer(f)
            w.writerow(perf_cols)
            w.writerows([[r[c] for c in perf_cols] for r in perf_rows])
            if perf_rows:
                totals = [sum(float(r[c] or 0) for r in perf_rows) for c in perf_cols[3:9]]
                w.writerow(['TOTAL', '', '', *['%.3f' % x for x in totals], ''])

    def summary(self):
        c = dict(self.db.execute('SELECT status,COUNT(*) FROM pages GROUP BY status').fetchall())
        t = dict(self.db.execute('SELECT page_type,COUNT(*) FROM pages GROUP BY page_type').fetchall())
        total = self.db.execute('SELECT COUNT(*) FROM pages').fetchone()[0]
        docs = self.db.execute('SELECT COUNT(*) FROM document_evidence').fetchone()[0]
        logging.info(
            'FINAL seed=%s discovered=%s processed=%s document_pages=%s documents=%s html=%s failed=%s '
            'skipped=%s duplicates=%s pagination=%s pagination_limits=%s pagination_states=%s '
            'load_more=%s year_switches=%s max_depth=%s page_limit=%s runtime_limit=%s runtime=%.1fs '
            'delay=%.1fs export=%.1fs parent_budget=%s family_limit=%s query_limit=%s same_family=%s '
            'after_page_limit=%s negative=%s esg_priority=%s robots_blocked=%s sitemap_seeded=%s '
            'orphans_recovered=%s esg_reveals=%s unconfirmed_network_documents=%s section_dead=%s '
            'expansion_budget_hits=%s detail_pagination_skipped=%s url_fallbacks=%s output=%s',
            self.seed, total, c.get('PROCESSED', 0), t.get('PDF', 0), docs, t.get('HTML', 0),
            c.get('FAILED', 0), c.get('SKIPPED', 0), self.stats['duplicates'],
            self.stats['pagination_detected'], self.stats['pagination_limits'],
            self.stats['pagination_states'], self.stats['load_more'], self.stats['year_switches'],
            self.stats['max_depth'], self.page_limit, self.runtime_limit,
            time.monotonic() - self.started, self.run_delay_seconds, self.run_export_seconds,
            self.expansion['parent_budget'], self.expansion['family_limit'],
            self.expansion['query_limit'], self.expansion['same_family'],
            self.expansion['after_page_limit'], self.expansion['negative'],
            self.expansion['esg_priority'], self.expansion['robots_blocked'],
            self.expansion['sitemap_seeded'], self.expansion['orphans_recovered'],
            self.expansion['esg_reveals'], self.expansion['unconfirmed_network_documents'],
            self.expansion['section_dead'], self.expansion['expansion_budget_hits'],
            self.expansion['detail_pagination_skipped'], self.expansion['url_fallbacks'], self.out)

    # ---------------- run loop ----------------
    async def worker(self, ctx, name):
        while not self.expired():
            async with self._lock:
                attempted = self.db.execute(
                    "SELECT COUNT(*) FROM pages WHERE status IN ('PROCESSED','FAILED','PROCESSING')"
                ).fetchone()[0]
                if attempted >= self.cfg.max_pages_per_website:
                    self.page_limit = True
                    return
                row = self.claim_next()
            if not row:
                # Other workers may still be adding children; wait briefly before quitting.
                async with self._lock:
                    busy = self.db.execute(
                        "SELECT COUNT(*) FROM pages WHERE status='PROCESSING'").fetchone()[0]
                if busy:
                    await asyncio.sleep(1.0)
                    continue
                return
            self.progress(row['page_url'] or row['normalized_url'])
            await self.process_with_watchdog(ctx, row)
            self.last_progress = time.monotonic()
            async with self._lock:
                self.processed_since_export += 1
                if self.processed_since_export >= self.cfg.export_checkpoint_pages:
                    t0 = time.perf_counter()
                    self.export()
                    self.run_export_seconds += time.perf_counter() - t0
                    self.processed_since_export = 0
            t0 = time.perf_counter()
            await asyncio.sleep(self.cfg.delay_between_pages_seconds)
            self.run_delay_seconds += time.perf_counter() - t0

    async def run(self):
        self.started = time.monotonic()          # per-site clock starts here
        self.last_progress = self.started
        self.recover_orphans()
        async with async_playwright() as pw:
            b = await pw.chromium.launch(headless=True, args=['--disable-dev-shm-usage'])
            ctx = await b.new_context(ignore_https_errors=True, accept_downloads=False,
                                      user_agent=self.cfg.user_agent)
            ctx.set_default_timeout(self.cfg.page_timeout_seconds * 1000)
            if self.cfg.block_heavy_resources:
                async def block_heavy(route):
                    try:
                        if route.request.resource_type in ('image', 'media', 'font'):
                            await route.abort()
                        else:
                            await route.continue_()
                    except PWError:
                        pass
                await ctx.route('**/*', block_heavy)
            try:
                try:
                    await asyncio.wait_for(self.load_robots(ctx), timeout=30)
                except asyncio.TimeoutError:
                    logging.warning('robots.txt timed out: %s', self.seed)
                if self.cfg.respect_robots_txt and self.robots.loaded and \
                        not self.robots.allowed(self.seed):
                    logging.warning('Seed URL is disallowed by robots.txt: %s', self.seed)
                self.add(self.seed, None, 'Home', 0, 0, 'seed')
                try:
                    await asyncio.wait_for(self.seed_from_sitemap(ctx), timeout=120)
                except asyncio.TimeoutError:
                    logging.warning('Sitemap seeding stopped after 120s: %s', self.seed)
                self.last_progress = time.monotonic()
                workers = [asyncio.create_task(self.worker(ctx, f'w{i}'))
                           for i in range(self.cfg.concurrency)]
                hard = self.cfg.max_minutes_per_website * 60 + \
                    self.cfg.page_attempt_timeout_seconds + 60
                try:
                    await asyncio.wait_for(asyncio.gather(*workers, return_exceptions=True),
                                           timeout=hard)
                except asyncio.TimeoutError:
                    logging.error('Hard site timeout; workers cancelled: %s', self.seed)
                    self.stop = True
            finally:
                for closer in (ctx.close, b.close):
                    try:
                        await asyncio.wait_for(closer(), timeout=20)
                    except Exception:
                        logging.warning('Browser close timed out for %s; continuing', self.seed)

    def close(self):
        try:
            self.db.commit()
        except sqlite3.Error:
            pass
        self.db.close()


def aggregate_outputs(root, collectors):
    """Merge per-seed CSV files into the output root."""
    names = ('classified_pages.csv', 'pdf_pages.csv', 'html_pages.csv', 'failed_pages.csv',
             'document_evidence.csv', 'skipped_pages.csv', 'PERFORMANCE_REPORT.csv',
             'PRIORITY_REPORT.csv')
    for name in names:
        header = None
        all_rows = []
        for collector in collectors:
            path = collector.out / name
            if not path.exists() or path.stat().st_size == 0:
                continue
            with path.open('r', encoding='utf-8-sig', newline='') as handle:
                rows = list(csv.reader(handle))
            if not rows:
                continue
            if header is None:
                header = rows[0]
            for row in rows[1:]:
                if row and row[0] != 'TOTAL':
                    all_rows.append(row)
        if header is not None:
            with (root / name).open('w', encoding='utf-8-sig', newline='') as handle:
                writer = csv.writer(handle)
                writer.writerow(header)
                writer.writerows(all_rows)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def seed_values(manual, path):
    seeds = []
    for item in (manual or []):
        for piece in re.split(r'[,\s]+', item.strip()):
            if piece:
                seeds.append(piece)
    if path and Path(path).exists():
        text = Path(path).read_text(encoding='utf-8-sig', errors='ignore')
        first = text.splitlines()[0] if text.splitlines() else ''
        if ',' in first or re.search(r'website_url|url|seed|site|domain|link', first, re.I):
            reader = csv.DictReader(text.splitlines())
            keys = [k for k in (reader.fieldnames or [])
                    if k and re.search(r'website_url|url|seed|site|domain|link', k, re.I)]
            if keys:
                for row in reader:
                    for k in keys:
                        v = (row.get(k) or '').strip()
                        if v and not v.lower().startswith(('website_url', 'url')):
                            seeds.append(v)
                            break
            else:
                for line in text.splitlines()[1:]:
                    v = line.split(',')[0].strip()
                    if v:
                        seeds.append(v)
        else:
            for line in text.splitlines():
                v = line.strip()
                if v and not v.startswith('#'):
                    seeds.append(v)
    out, seen = [], set()
    for s in seeds:
        key = s.lower().rstrip('/')
        if key not in seen:
            seen.add(key)
            out.append(s)
    if not out:
        raise ValueError('No seed URL supplied (use --website-url or provide seeds.csv)')
    return out


async def amain(a):
    handlers = [logging.StreamHandler(sys.stdout)]
    try:
        handlers.append(logging.FileHandler(a.log, encoding='utf-8'))
    except OSError:
        pass
    logging.basicConfig(level=os.getenv('LOG_LEVEL', 'INFO'),
                        format='%(asctime)sZ %(levelname)s %(message)s',
                        handlers=handlers, force=True)
    cfg = Config.load(a.config)
    seeds = seed_values(a.website_url, a.seeds)
    root = Path(a.output_dir)
    root.mkdir(parents=True, exist_ok=True)
    logging.info('Seeds (%s): %s', len(seeds), ', '.join(seeds))
    collectors = []
    for seed in seeds:
        try:
            collectors.append(Collector(seed, cfg, root))
        except ValueError as exc:
            logging.error('Skipping invalid seed %r: %s', seed, exc)
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, lambda *_: [setattr(x, 'stop', True) for x in collectors])
        except (ValueError, OSError):
            pass
    semaphore = asyncio.Semaphore(cfg.parallel_websites)
    failures = []

    async def run_one(c):
        async with semaphore:
            try:
                logging.info('=== Seed %s -> %s', c.seed, c.out)
                await c.run()
            except Exception as exc:
                logging.exception('Fatal collector error for %s', c.seed)
                failures.append((c.seed, exc))
            finally:
                try:
                    c.export()
                    c.summary()
                finally:
                    c.close()

    await asyncio.gather(*(run_one(c) for c in collectors))
    aggregate_outputs(root, collectors)
    if failures:
        raise SystemExit(f'{len(failures)} seed(s) failed')


def main():
    p = argparse.ArgumentParser(description='Collect website pages that expose PDF/Office documents.')
    p.add_argument('--website-url', action='append', default=None,
                   help='Seed URL (repeatable, or comma-separated).')
    p.add_argument('--config', default='collector_config.json')
    p.add_argument('--seeds', default='seeds.csv')
    p.add_argument('--output-dir', default='.')
    p.add_argument('--log', default='collector.log')
    a = p.parse_args()
    if not a.website_url:
        envval = os.getenv('WEBSITE_URL', '')
        a.website_url = [envval] if envval else []
    try:
        asyncio.run(amain(a))
    except KeyboardInterrupt:
        print('Interrupted', file=sys.stderr)
        sys.exit(130)
    except SystemExit:
        raise
    except Exception as e:
        print(f'Collector failed: {e}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
