#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心数学概念/定理文档注入具有 DOI / arXiv ID 的经典论文/原始文献。

用法：
    python scripts/inject_landmark_papers.py
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

# term -> list of paper dicts
LANDMARK_PAPERS = {
    "费马大定理": [
        {
            "title": "Modular elliptic curves and Fermat's Last Theorem",
            "author": "Andrew Wiles",
            "journal": "Annals of Mathematics",
            "year": 1995,
            "doi": "10.2307/2118559",
        },
        {
            "title": "Ring-theoretic properties of certain Hecke algebras",
            "author": "Richard Taylor, Andrew Wiles",
            "journal": "Annals of Mathematics",
            "year": 1995,
            "doi": "10.2307/2118560",
        },
    ],
    "庞加莱猜想": [
        {
            "title": "The entropy formula for the Ricci flow and its geometric applications",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2002,
            "arxiv_id": "math/0211159",
        },
        {
            "title": "Ricci flow with surgery on three-manifolds",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2003,
            "arxiv_id": "math/0303109",
        },
        {
            "title": "Finite extinction time for the solutions to the Ricci flow on certain three-manifolds",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2003,
            "arxiv_id": "math/0307245",
        },
    ],
    "孪生素数": [
        {
            "title": "Bounded gaps between primes",
            "author": "Yitang Zhang",
            "journal": "Annals of Mathematics",
            "year": 2014,
            "doi": "10.4007/annals.2014.179.3.7",
        },
    ],
    "素数间隙": [
        {
            "title": "Small gaps between primes",
            "author": "James Maynard",
            "journal": "Annals of Mathematics",
            "year": 2015,
            "doi": "10.4007/annals.2015.181.1.7",
        },
    ],
    "Green-Tao": [
        {
            "title": "The primes contain arbitrarily long arithmetic progressions",
            "author": "Ben Green, Terence Tao",
            "journal": "Annals of Mathematics",
            "year": 2008,
            "doi": "10.4007/annals.2008.167.481",
            "arxiv_id": "math/0404188",
        },
    ],
    "Weil猜想": [
        {
            "title": "La conjecture de Weil. I",
            "author": "Pierre Deligne",
            "journal": "Publications Mathématiques de l'IHÉS",
            "year": 1974,
            "doi": "10.1007/BF02684673",
        },
    ],
    "指标定理": [
        {
            "title": "The Index of Elliptic Operators on Compact Manifolds",
            "author": "Michael F. Atiyah, Isadore M. Singer",
            "journal": "Annals of Mathematics",
            "year": 1963,
            "doi": "10.2307/1970715",
        },
    ],
    "模型范畴": [
        {
            "title": "Homotopical Algebra",
            "author": "Daniel G. Quillen",
            "journal": "Lecture Notes in Mathematics",
            "year": 1967,
            "doi": "10.1007/BFb0097438",
        },
    ],
    "范畴论": [
        {
            "title": "General Theory of Natural Equivalences",
            "author": "Samuel Eilenberg, Saunders Mac Lane",
            "journal": "Transactions of the American Mathematical Society",
            "year": 1945,
            "doi": "10.2307/2269622",
        },
    ],
    "哥德尔不完备": [
        {
            "title": "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I",
            "author": "Kurt Gödel",
            "journal": "Monatshefte für Mathematik und Physik",
            "year": 1931,
            "doi": "10.1007/BF01700692",
        },
    ],
    "图灵机": [
        {
            "title": "On Computable Numbers, with an Application to the Entscheidungsproblem",
            "author": "Alan M. Turing",
            "journal": "Proceedings of the London Mathematical Society",
            "year": 1937,
            "doi": "10.1112/plms/s2-42.1.230",
        },
    ],
    "黎曼猜想": [
        {
            "title": "Über die Anzahl der Primzahlen unter einer gegebenen Grösse",
            "author": "Bernhard Riemann",
            "journal": "Monatsberichte der Berliner Akademie",
            "year": 1859,
            "url": "https://www.claymath.org/publications/riemanns-1859-manuscript/",
        },
    ],
    "朗兰兹纲领": [
        {
            "title": "Problems in the Theory of Automorphic Forms",
            "author": "Robert P. Langlands",
            "journal": "Lecture Notes in Mathematics",
            "year": 1970,
            "doi": "10.1007/BFb0079065",
        },
    ],
    "黎曼-罗赫": [
        {
            "title": "Le théorème de Riemann-Roch",
            "author": "Armand Borel, Jean-Pierre Serre",
            "journal": "Bulletin de la Société Mathématique de France",
            "year": 1958,
            "doi": "10.24033/bsmf.1500",
        },
    ],
    "Riemann-Roch": [
        {
            "title": "Le théorème de Riemann-Roch",
            "author": "Armand Borel, Jean-Pierre Serre",
            "journal": "Bulletin de la Société Mathématique de France",
            "year": 1958,
            "doi": "10.24033/bsmf.1500",
        },
    ],
    "Serre对偶": [
        {
            "title": "Faisceaux algébriques cohérents",
            "author": "Jean-Pierre Serre",
            "journal": "Annals of Mathematics",
            "year": 1955,
            "doi": "10.2307/1970375",
        },
    ],
    "Bott周期性": [
        {
            "title": "The stable homotopy of the classical groups",
            "author": "Raoul Bott",
            "journal": "Annals of Mathematics",
            "year": 1959,
            "doi": "10.2307/1970106",
        },
    ],
    "法尔廷斯": [
        {
            "title": "Endlichkeitssätze für abelsche Varietäten über Zahlkörpern",
            "author": "Gerd Faltings",
            "journal": "Inventiones Mathematicae",
            "year": 1983,
            "doi": "10.1007/BF01388834",
        },
    ],
    "谷山-志村": [
        {
            "title": "On the modularity of elliptic curves over Q: wild 3-adic exercises",
            "author": "Christophe Breuil, Brian Conrad, Fred Diamond, Richard Taylor",
            "journal": "Journal of the American Mathematical Society",
            "year": 2001,
            "doi": "10.1090/S0894-0347-01-00370-8",
        },
    ],
    "P与NP": [
        {
            "title": "The complexity of theorem-proving procedures",
            "author": "Stephen A. Cook",
            "journal": "Proceedings of the Third Annual ACM Symposium on Theory of Computing",
            "year": 1971,
            "doi": "10.1145/800157.805047",
        },
    ],
    "连续统假设": [
        {
            "title": "The independence of the continuum hypothesis",
            "author": "Paul J. Cohen",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1963,
            "doi": "10.1073/pnas.50.6.1143",
        },
    ],
    "RSA": [
        {
            "title": "A method for obtaining digital signatures and public-key cryptosystems",
            "author": "Ronald L. Rivest, Adi Shamir, Leonard M. Adleman",
            "journal": "Communications of the ACM",
            "year": 1978,
            "doi": "10.1145/359340.359342",
        },
    ],
    "香农": [
        {
            "title": "A mathematical theory of communication",
            "author": "Claude E. Shannon",
            "journal": "Bell System Technical Journal",
            "year": 1948,
            "url": "https://doi.org/10.1002/j.1538-7305.1948.tb01338.x",
        },
    ],
    "完美胚空间": [
        {
            "title": "Perfectoid spaces",
            "author": "Peter Scholze",
            "journal": "Publications Mathématiques de l'IHÉS",
            "year": 2012,
            "doi": "10.1007/s10240-012-0042-x",
        },
    ],
    "KPZ方程": [
        {
            "title": "Dynamic scaling of growing interfaces",
            "author": "Mehran Kardar, Giorgio Parisi, Yi-Cheng Zhang",
            "journal": "Physical Review Letters",
            "year": 1986,
            "doi": "10.1103/PhysRevLett.56.889",
        },
    ],
    "费特-汤普森": [
        {
            "title": "Solvability of groups of odd order",
            "author": "Walter Feit, John G. Thompson",
            "journal": "Pacific Journal of Mathematics",
            "year": 1963,
            "doi": "10.2140/pjm.1963.13.775",
        },
    ],
    "开普勒猜想": [
        {
            "title": "A proof of the Kepler conjecture",
            "author": "Thomas C. Hales",
            "journal": "Annals of Mathematics",
            "year": 2005,
            "doi": "10.4007/annals.2005.162.1065",
        },
    ],
    "莫尔斯理论": [
        {
            "title": "Relations between the critical points of a real function of n independent variables",
            "author": "Marston Morse",
            "journal": "Transactions of the American Mathematical Society",
            "year": 1925,
            "doi": "10.2307/1989176",
        },
    ],
    "布劳威尔不动点": [
        {
            "title": "Über Abbildung von Mannigfaltigkeiten",
            "author": "L. E. J. Brouwer",
            "journal": "Mathematische Annalen",
            "year": 1912,
            "doi": "10.1007/BF01444152",
        },
    ],
    "亚当斯谱序列": [
        {
            "title": "On the structure and applications of the Steenrod algebra",
            "author": "J. Frank Adams",
            "journal": "Commentarii Mathematici Helvetici",
            "year": 1958,
            "doi": "10.1007/BF02565974",
        },
    ],
}


def is_report_like(title: str, stem: str):
    report_markers = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单"]
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in report_markers):
        return True
    return False


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


def format_paper_line(paper: dict):
    title = paper.get("title", "")
    author = paper.get("author", "")
    year = paper.get("year", "")
    journal = paper.get("journal", "")
    doi = paper.get("doi", "")
    arxiv = paper.get("arxiv_id", "")
    parts = [p for p in [author, f"*{title}*", journal, str(year) if year else ""] if p]
    line = ", ".join(parts)
    detail = []
    if doi:
        detail.append(f"DOI: {doi}")
    if arxiv:
        detail.append(f"arXiv: {arxiv}")
    if detail:
        line += " (" + "; ".join(detail) + ")"
    return f"- {line}"


def has_papers_section(body: str):
    return "## 经典论文与原始文献" in body or "### 经典论文与原始文献" in body


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False

    title = fm.get("title", "")
    stem = path.stem
    if is_report_like(title, stem):
        return False

    matched_papers = []
    for term, papers in LANDMARK_PAPERS.items():
        if term in title or term in stem:
            matched_papers.extend(papers)

    if not matched_papers:
        return False

    refs = fm.get("references") or {}
    existing_papers = refs.get("papers") or []
    existing_titles = {p.get("title") for p in existing_papers}
    added_frontmatter = 0
    for paper in matched_papers:
        if paper["title"] not in existing_titles:
            existing_papers.append(paper)
            existing_titles.add(paper["title"])
            added_frontmatter += 1

    changed = False
    if added_frontmatter:
        refs["papers"] = existing_papers
        fm["references"] = refs
        changed = True

    # 无论是否银层，都确保正文可见 DOI/arXiv
    if not has_papers_section(body):
        section_lines = ["", "---", "", "## 经典论文与原始文献", ""]
        for paper in matched_papers:
            section_lines.append(format_paper_line(paper))
        section_lines.append("")
        body = body.rstrip() + "\n" + "\n".join(section_lines)
        changed = True

    if not changed:
        return False

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
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
    print(f"Injected landmark papers into {changed} docs.")


if __name__ == "__main__":
    main()
