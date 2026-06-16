#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为银层文档去重合并 references.textbooks，并补全已知经典教材的 ISBN/出版信息。

用法：
    python scripts/dedup_silver_references.py
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

KNOWN_BOOKS = {
    ("Understanding Analysis", "Stephen Abbott"): {
        "edition": "2nd",
        "publisher": "Springer",
        "year": 2015,
        "isbn": "9781493927111",
    },
    ("Principles of Mathematical Analysis", "Walter Rudin"): {
        "edition": "3rd",
        "publisher": "McGraw-Hill",
        "year": 1976,
        "isbn": "9780070542358",
        "mr_number": "MR0385023",
    },
    ("Introduction to Linear Algebra", "Gilbert Strang"): {
        "edition": "5th",
        "publisher": "Wellesley-Cambridge Press",
        "year": 2016,
        "isbn": "9780980232776",
    },
    ("Algebra", "Michael Artin"): {
        "edition": "2nd",
        "publisher": "Pearson",
        "year": 2010,
        "isbn": "9780132413770",
    },
    ("Abstract Algebra", "David S. Dummit and Richard M. Foote"): {
        "edition": "3rd",
        "publisher": "Wiley",
        "year": 2003,
        "isbn": "9780471433347",
        "mr_number": "MR2286236",
    },
    ("Algebraic Geometry", "Robin Hartshorne"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 1977,
        "isbn": "9780387902449",
        "mr_number": "MR0463157",
    },
    ("The Rising Sea: Foundations of Algebraic Geometry", "Ravi Vakil"): {
        "edition": "draft",
        "publisher": "Stanford University",
        "year": 2024,
        "isbn": "",
    },
    ("Foundations of Algebraic Geometry", "Ravi Vakil"): {
        "edition": "draft",
        "publisher": "Stanford University",
        "year": 2024,
        "isbn": "",
    },
    ("Topology", "James R. Munkres"): {
        "edition": "2nd",
        "publisher": "Pearson",
        "year": 2000,
        "isbn": "9780131816299",
        "mr_number": "MR0464128",
    },
    ("Introduction to Smooth Manifolds", "John M. Lee"): {
        "edition": "2nd",
        "publisher": "Springer",
        "year": 2012,
        "isbn": "9781441999818",
        "mr_number": "MR2954043",
    },
    ("K-Theory", "Michael Atiyah"): {
        "edition": "1st",
        "publisher": "Addison-Wesley",
        "year": 1989,
        "isbn": "9780201407518",
        "mr_number": "MR1043170",
    },
    ("K-Theory: An Introduction", "Max Karoubi"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 1978,
        "isbn": "9783540080347",
    },
    ("Partial Differential Equations", "Lawrence C. Evans"): {
        "edition": "2nd",
        "publisher": "American Mathematical Society",
        "year": 2010,
        "isbn": "9780821849743",
        "mr_number": "MR2597943",
    },
    ("Partial Differential Equations: An Introduction", "Walter A. Strauss"): {
        "edition": "2nd",
        "publisher": "Wiley",
        "year": 2008,
        "isbn": "9780470054567",
    },
    ("Multivariable Calculus", "Jerrold E. Marsden, Anthony J. Tromba"): {
        "edition": "6th",
        "publisher": "W. H. Freeman",
        "year": 2011,
        "isbn": "9781429215084",
    },
    ("Complex Analysis", "Elias M. Stein, Rami Shakarchi"): {
        "edition": "1st",
        "publisher": "Princeton University Press",
        "year": 2003,
        "isbn": "9780691113852",
    },
    ("Functions of One Complex Variable I", "John B. Conway"): {
        "edition": "2nd",
        "publisher": "Springer",
        "year": 1995,
        "isbn": "9780387944609",
        "mr_number": "MR1344449",
    },
    ("Representation Theory: A First Course", "William Fulton, Joe Harris"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 1991,
        "isbn": "9780387974958",
        "mr_number": "MR1153249",
    },
    ("Differential Geometry of Curves and Surfaces", "Manfredo P. do Carmo"): {
        "edition": "1st",
        "publisher": "Prentice-Hall",
        "year": 1976,
        "isbn": "9780132125895",
        "mr_number": "MR0394451",
    },
    ("Elementary Differential Geometry", "Barrett O'Neill"): {
        "edition": "2nd",
        "publisher": "Academic Press",
        "year": 2006,
        "isbn": "9780120887354",
        "mr_number": "MR2351345",
    },
    ("A Course in Arithmetic", "Jean-Pierre Serre"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 1973,
        "isbn": "9780387900407",
        "mr_number": "MR0344216",
    },
    ("Residues and Duality", "Robin Hartshorne"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 1966,
        "isbn": "9783540036207",
        "mr_number": "MR0222093",
    },
    ("Geometric Invariant Theory", "David Mumford"): {
        "edition": "3rd",
        "publisher": "Springer",
        "year": 1994,
        "isbn": "9783540569637",
        "mr_number": "MR1304906",
    },
    ("Representation Theory of Finite Groups", "Benjamin Steinberg"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 2012,
        "isbn": "9781461407759",
        "mr_number": "MR2883681",
    },
    ("Representations and Characters of Groups", "Gordon James & Martin Liebeck"): {
        "edition": "2nd",
        "publisher": "Cambridge University Press",
        "year": 2001,
        "isbn": "9780521003926",
        "mr_number": "MR1864147",
    },
    ("Geometry of Algebraic Curves, Vol. I", "Enrico Arbarello, Maurizio Cornalba, Phillip Griffiths, Joe Harris"): {
        "edition": "1st",
        "publisher": "Springer",
        "year": 1985,
        "isbn": "9780387909974",
        "mr_number": "MR0770932",
    },
    ("Complex Algebraic Surfaces", "Arnaud Beauville"): {
        "edition": "2nd",
        "publisher": "Cambridge University Press",
        "year": 1996,
        "isbn": "9780521498422",
        "mr_number": "MR1406314",
    },
}


def normalize_isbn(isbn: str):
    return str(isbn).replace("-", "").replace(" ", "")


def book_signature(tb: dict):
    title = tb.get("title", "").strip()
    author = tb.get("author", "").strip()
    if not author:
        author = ", ".join(a.strip() for a in tb.get("authors", []) if isinstance(a, str))
    return (title, author)


def merge_books(books: list):
    merged = []
    seen = {}
    for tb in books:
        sig = book_signature(tb)
        # 尝试用标题匹配已知书籍，补全元数据
        for (kt, ka), meta in KNOWN_BOOKS.items():
            if tb.get("title", "").strip() == kt:
                for k, v in meta.items():
                    if not tb.get(k):
                        tb[k] = v
                if not tb.get("author") and ka:
                    tb["author"] = ka
                break
        if sig in seen:
            idx = seen[sig]
            base = merged[idx]
            for k, v in tb.items():
                if k == "isbn":
                    continue
                if v and not base.get(k):
                    base[k] = v
            # ISBN 优先保留有值的
            if tb.get("isbn") and not base.get("isbn"):
                base["isbn"] = tb["isbn"]
            if base.get("isbn") and tb.get("isbn") and normalize_isbn(base["isbn"]) != normalize_isbn(tb["isbn"]):
                # 保留更长的 ISBN
                if len(normalize_isbn(tb["isbn"])) > len(normalize_isbn(base["isbn"])):
                    base["isbn"] = tb["isbn"]
        else:
            seen[sig] = len(merged)
            merged.append(tb)
    return merged


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].strip()
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None or fm.get("level") != "silver":
        return False
    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    if not textbooks:
        return False
    # 记录原始 frontmatter 文本用于判断是否有变更
    original_fm_text = yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
    new_textbooks = merge_books(textbooks)
    refs["textbooks"] = new_textbooks
    fm["references"] = refs
    new_fm_text = yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
    if new_fm_text == original_fm_text:
        return False
    new_text = (
        "---\n"
        + new_fm_text
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if process_file(p):
            changed += 1
    print(f"Deduplicated references in {changed} silver docs.")


if __name__ == "__main__":
    main()
