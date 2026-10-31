#!/usr/bin/env python3
"""Citation check for the thesis.

Checks the citations in the thesis against the bibliography and against
the citation rules from the decision log:
  - only papers whose full text is available are cited
    (literature table: "Do not cite ..." or "PDF in folder" = FALSE),
  - a preprint without a peer-reviewed version is cited only when it is
    marked in the text as not yet peer reviewed.

It also lists cited sources that are missing from the bibliography,
duplicate entries, entries without pages or DOI, and entries that are
never cited (BibTeX leaves those out of the reference list).

Usage, from the thesis folder:
    python tools/check_citations.py
    python tools/check_citations.py --sheet Papers.csv

--sheet  CSV export of the "Papers" tab of the literature table
         (Google Sheets: open the Papers tab, then File > Download >
         Comma-separated values). Without it, the "do not cite" check
         is skipped.

Only text that ends up in the PDF is checked: the script starts at
main.tex and follows \\input / \\include. Commented-out lines are ignored.

Exit code: 1 if something is listed under MUST FIX, otherwise 0.
Needs only the Python standard library (Python 3.8 or newer).
"""

import argparse
import csv
import difflib
import re
import sys
import unicodedata
from collections import defaultdict
from pathlib import Path

# ---------------------------------------------------------------- LaTeX

INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")
BIB_RE = re.compile(r"\\(?:bibliography|addbibresource)\s*\{([^}]+)\}")
# \cite, \citep, \citet, \citeauthor, \nocite, \parencite, \textcite, ...
# with up to two optional arguments, e.g. \cite[p.~3]{key1,key2}
CITE_RE = re.compile(
    r"\\([a-zA-Z]*cite[a-zA-Z]*)\*?\s*(?:\[[^\]]*\]\s*){0,2}\{([^}]*)\}"
)
NOT_CITE_COMMANDS = {"citestyle", "bibliographystyle"}
# What counts as "marked as not yet peer reviewed" in the text
PEER_NOTE_RE = re.compile(r"peer[\s~-]*review|preprint", re.IGNORECASE)


def strip_comments(text):
    """Remove LaTeX comments (keeps \\%), line numbers stay the same."""
    return "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in text.splitlines())


def read(path):
    return path.read_text(encoding="utf-8", errors="replace")


def collect_tex_files(root, main_name):
    """main.tex plus every file it includes (recursively), in order."""
    order, missing, seen = [], [], set()

    def visit(path):
        if path in seen:
            return
        seen.add(path)
        if not path.exists():
            missing.append(path)
            return
        order.append(path)
        text = strip_comments(read(path))
        for m in INPUT_RE.finditer(text):
            name = m.group(1).strip()
            if not name.endswith(".tex"):
                name += ".tex"
            visit((root / name).resolve())

    visit((root / main_name).resolve())
    return order, missing


def find_citations(root, files):
    """Returns a list of dicts: file, line, key, pos, text (file content)."""
    cites = []
    for path in files:
        text = strip_comments(read(path))
        for m in CITE_RE.finditer(text):
            if m.group(1).lower() in NOT_CITE_COMMANDS:
                continue
            for key in m.group(2).split(","):
                key = key.strip()
                if key:
                    cites.append({
                        "file": path.relative_to(root).as_posix(),
                        "line": text.count("\n", 0, m.start()) + 1,
                        "key": key,
                        "pos": m.start(),
                        "text": text,
                    })
    return cites


def sentence_context(text, pos):
    """The sentence (or table row) that contains pos, plus the one before.

    Boundaries: blank lines, end of a sentence, and table row ends (\\\\).
    """
    para_start = text.rfind("\n\n", 0, pos)
    para_start = 0 if para_start == -1 else para_start + 2
    para_end = text.find("\n\n", pos)
    para_end = len(text) if para_end == -1 else para_end
    para = text[para_start:para_end]
    rel = pos - para_start
    bounds = [0]
    for m in re.finditer(r"(?<=[.!?])\s+(?=[A-Z\\])|\\\\", para):
        bounds.append(m.end())
    bounds.append(len(para))
    idx = max(i for i, b in enumerate(bounds[:-1]) if b <= rel)
    start = bounds[max(idx - 1, 0)]
    end = bounds[idx + 1]
    return para[start:end]


# ---------------------------------------------------------------- BibTeX

FIELD_RE = re.compile(r"\s*,?\s*([A-Za-z][\w-]*)\s*=\s*")


def parse_fields(body):
    fields, k, n = {}, 0, len(body)
    while k < n:
        m = FIELD_RE.match(body, k)
        if not m:
            break
        name, k = m.group(1).lower(), m.end()
        if k >= n:
            break
        if body[k] == "{":
            depth, start = 0, k
            while k < n:
                if body[k] == "{":
                    depth += 1
                elif body[k] == "}":
                    depth -= 1
                    if depth == 0:
                        k += 1
                        break
                k += 1
            value = body[start + 1:k - 1]
        elif body[k] == '"':
            k += 1
            depth, start = 0, k
            while k < n and not (body[k] == '"' and depth == 0):
                if body[k] == "{":
                    depth += 1
                elif body[k] == "}":
                    depth -= 1
                k += 1
            value = body[start:k]
            k += 1
        else:
            m2 = re.compile(r"[^,]*").match(body, k)
            value, k = m2.group(0), m2.end()
        fields[name] = " ".join(value.split())
    return fields


def parse_bib(text):
    """Returns (entries in file order, duplicate keys)."""
    entries, seen, duplicates = [], set(), []
    i = 0
    while True:
        at = text.find("@", i)
        if at == -1:
            break
        m = re.compile(r"@\s*([a-zA-Z]+)\s*\{").match(text, at)
        if not m:
            i = at + 1
            continue
        etype = m.group(1).lower()
        depth, j = 1, m.end()
        while j < len(text) and depth:
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
            j += 1
        i = j
        if etype in ("comment", "string", "preamble"):
            continue
        body = text[m.end():j - 1]
        comma = body.find(",")
        if comma == -1:
            continue
        key = body[:comma].strip()
        entry = {"key": key, "type": etype,
                 "line": text.count("\n", 0, at) + 1}
        entry.update(parse_fields(body[comma + 1:]))
        if key in seen:
            duplicates.append(key)
        seen.add(key)
        entries.append(entry)
    return entries, duplicates


PREPRINT_RE = re.compile(r"arxiv|ssrn|medrxiv|biorxiv|preprint|10\.48550", re.I)
DOI_EXPECTED_RE = re.compile(r"springer|lncs|lnbip|acm|ieee|elsevier|wiley", re.I)
ARTICLE_NO_RE = re.compile(r"\bart(icle)?\.?\s*(no\.?\s*)?\d|\be\d{4,}", re.I)
# Venues that do not give page numbers or DOIs, so a gap there is normal
NO_PAGES_VENUE_RE = re.compile(r"learning representations|\biclr\b", re.I)
NO_DOI_VENUE_RE = re.compile(r"journal of machine learning research|\bjmlr\b|\bpmlr\b", re.I)


def is_preprint(e):
    where = " ".join(e.get(f, "") for f in
                     ("journal", "howpublished", "note", "url", "eprint",
                      "archiveprefix", "publisher", "doi"))
    if e["type"] in ("misc", "unpublished", "online", "electronic"):
        return bool(PREPRINT_RE.search(where))
    if e["type"] == "article":
        return bool(PREPRINT_RE.search(e.get("journal", "")))
    return False  # published in proceedings or a book


def missing_details(e):
    """Pages / DOI that a reader would expect for this type of entry."""
    gaps = []
    t = e["type"]
    venue_all = " ".join(e.get(f, "") for f in ("journal", "booktitle", "publisher", "series"))
    if t in ("article", "inproceedings", "incollection"):
        has_number = ("pages" in e or "eid" in e or "articleno" in e
                      or ARTICLE_NO_RE.search(e.get("note", "")))
        if not has_number and not NO_PAGES_VENUE_RE.search(venue_all):
            gaps.append("pages")
    if t == "article" and "doi" not in e and not NO_DOI_VENUE_RE.search(venue_all):
        gaps.append("DOI")
    if t in ("inproceedings", "incollection") and "doi" not in e:
        venue = " ".join(e.get(f, "") for f in ("booktitle", "publisher", "series"))
        if DOI_EXPECTED_RE.search(venue):
            gaps.append("DOI")
    return gaps


def short_ref(e):
    author = e.get("author", "?").split(" and ")[0]
    surname = author.split(",")[0].strip() if "," in author else author.split()[-1]
    surname = re.sub(r"[{}]", "", surname)
    more = " et al." if " and " in e.get("author", "") else ""
    return f"{surname}{more} {e.get('year', '?')}"


# ---------------------------------------------------------------- Sheet

def norm_title(s):
    s = re.sub(r"\\[a-zA-Z]+\s*", "", s)
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]", "", s.lower())


def read_sheet(path):
    """Papers that must not be cited, from the literature table export."""
    with open(path, newline="", encoding="utf-8-sig") as f:
        rows = list(csv.reader(f))
    header_idx = next((i for i, r in enumerate(rows)
                       if "ID" in r and "Title" in r), None)
    if header_idx is None:
        sys.exit(f"Could not find the header row (ID, Title) in {path}.")
    header = [h.strip().lower() for h in rows[header_idx]]

    def col(prefix):
        return next((i for i, h in enumerate(header) if h.startswith(prefix)), None)

    c_id, c_title = col("id"), col("title")
    c_pdf, c_rel = col("pdf in folder"), col("relevance level")
    blocked = []
    for r in rows[header_idx + 1:]:
        r = r + [""] * (len(header) - len(r))
        title = r[c_title].strip()
        if not title:
            continue
        rel = r[c_rel].strip() if c_rel is not None else ""
        pdf = r[c_pdf].strip().upper() if c_pdf is not None else ""
        reason = None
        if rel.lower().startswith("do not cite") or "no full text" in rel.lower():
            reason = rel
        elif pdf == "FALSE":
            reason = "no full text (PDF in folder = FALSE)"
        if reason:
            blocked.append({"id": r[c_id].strip(), "title": title,
                            "norm": norm_title(title), "reason": reason})
    return blocked


def match_blocked(entry, blocked):
    t = norm_title(entry.get("title", ""))
    if not t:
        return None
    for b in blocked:
        if t == b["norm"]:
            return b
        shorter, longer = sorted((t, b["norm"]), key=len)
        if len(shorter) >= 30 and longer.startswith(shorter):
            return b
        if difflib.SequenceMatcher(None, t, b["norm"]).ratio() >= 0.9:
            return b
    return None


# ---------------------------------------------------------------- Report

def where(cs, limit=4):
    places = list(dict.fromkeys(f"{c['file']}, line {c['line']}" for c in cs))
    extra = f" (+{len(places) - limit} more)" if len(places) > limit else ""
    return "; ".join(places[:limit]) + extra


def main():
    here = Path(__file__).resolve().parent
    default_root = here.parent if (here.parent / "main.tex").exists() else Path.cwd()
    ap = argparse.ArgumentParser(description="Check the citations of the thesis.")
    ap.add_argument("--root", type=Path, default=default_root,
                    help="thesis folder (default: %(default)s)")
    ap.add_argument("--main", default="main.tex", help="main LaTeX file")
    ap.add_argument("--sheet", type=Path,
                    help="CSV export of the Papers tab of the literature table")
    args = ap.parse_args()
    root = args.root.resolve()

    files, missing_files = collect_tex_files(root, args.main)
    if not files:
        sys.exit(f"{args.main} not found in {root}.")
    cites = find_citations(root, files)

    bib_names = []
    for path in files:
        for m in BIB_RE.finditer(strip_comments(read(path))):
            bib_names += [b.strip() for b in m.group(1).split(",")]
    bib_paths = [root / (b if b.endswith(".bib") else b + ".bib") for b in bib_names]
    bib_paths = [p for p in bib_paths if p.exists()] or [root / "library" / "citations.bib"]
    entries, dup_keys = [], []
    for p in bib_paths:
        e, d = parse_bib(read(p))
        entries += e
        dup_keys += d
    bib = {}
    for e in entries:
        bib.setdefault(e["key"], e)  # BibTeX uses the first entry with a key

    by_key = defaultdict(list)
    for c in cites:
        by_key[c["key"]].append(c)
    nocite_all = "*" in by_key
    cited_keys = [k for k in by_key if k != "*"]

    must, check, info = [], [], []

    # 1. Cited but not in the bibliography
    for k in cited_keys:
        if k not in bib:
            must.append(("Cited, but not in the bibliography (shows as [?] in the PDF)",
                         f"{k}\n      {where(by_key[k])}"))

    # 2. Do-not-cite papers (literature table)
    blocked = read_sheet(args.sheet) if args.sheet else None
    if blocked is not None:
        for k in cited_keys:
            if k in bib:
                b = match_blocked(bib[k], blocked)
                if b:
                    must.append(("Cited, but marked in the literature table as not citable",
                                 f"{k} = {b['id']} \"{b['title']}\"\n"
                                 f"      table says: {b['reason']}\n"
                                 f"      {where(by_key[k])}"))

    # 3. Preprints without a note in the text
    for k in cited_keys:
        if k in bib and is_preprint(bib[k]):
            unmarked = [c for c in by_key[k]
                        if not PEER_NOTE_RE.search(
                            CITE_RE.sub("", sentence_context(c["text"], c["pos"])))]
            if unmarked:
                must.append(("Preprint cited without \"not yet peer reviewed\" in the same "
                             "or the previous sentence",
                             f"{k} ({short_ref(bib[k])}, {bib[k].get('howpublished') or bib[k].get('journal') or 'preprint'})\n"
                             f"      {where(unmarked)}"))
            else:
                info.append(("Preprints cited and marked as not yet peer reviewed",
                             f"{k} ({short_ref(bib[k])}), {len(by_key[k])}x"))

    # 4. Duplicate entries
    for k in sorted(set(dup_keys)):
        must.append(("Same key twice in the bibliography", k))
    seen_titles = {}
    for e in entries:
        t = norm_title(e.get("title", ""))
        if t and t in seen_titles and seen_titles[t] != e["key"]:
            check.append(("Same paper twice in the bibliography (different keys)",
                          f"{seen_titles[t]} and {e['key']}"))
        seen_titles.setdefault(t, e["key"])

    # 5. Missing pages / DOI (cited entries only)
    for k in sorted(cited_keys):
        if k in bib:
            gaps = missing_details(bib[k])
            if gaps:
                check.append(("Cited entry with missing pages or DOI",
                              f"{k} ({short_ref(bib[k])}, @{bib[k]['type']}): no {' and no '.join(gaps)}"))

    # 6. Never cited
    if not nocite_all:
        for e in entries:
            if e["key"] not in by_key:
                info.append(("In the bibliography but never cited (not printed)",
                             f"{e['key']} ({short_ref(e)}), citations.bib line {e['line']}"))

    for f in missing_files:
        try:
            shown = f.relative_to(root).as_posix()
        except ValueError:
            shown = str(f)
        check.append(("Included file not found", shown))

    # ---- print
    print("Citation check")
    print(f"  {len(files)} LaTeX files, {len(cited_keys)} different sources cited, "
          f"{len(entries)} entries in the bibliography")
    if blocked is None:
        print("  Literature table not given: \"do not cite\" check skipped (use --sheet)")
    else:
        print(f"  Literature table: {len(blocked)} papers marked as not citable")

    def section(title, items, note):
        print()
        print(f"{title} ({len(items)})" + (f"  - {note}" if note else ""))
        if not items:
            print("  nothing")
            return
        groups = defaultdict(list)
        for g, text in items:
            groups[g].append(text)
        for g, texts in groups.items():
            print(f"  {g}:")
            for t in texts:
                print(f"    - {t}")

    section("MUST FIX", must, "breaks a citation rule or the reference list")
    section("PLEASE CHECK", check, "may be fine, but worth a look")
    section("FOR INFORMATION", info, "")
    print()
    print(f"Result: {len(must)} must fix, {len(check)} to check.")
    return 1 if must else 0


if __name__ == "__main__":
    sys.exit(main())
