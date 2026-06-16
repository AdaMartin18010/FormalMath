#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心数学家文档注入 Wikidata QID 外部链接（使用高置信度手工映射）。

用法：
    python scripts/inject_wikidata_ids.py
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MATH_DIR = PROJECT_ROOT / "数学家理念体系"

# 关键词（中文或英文） -> Wikidata QID
WIKIDATA_QID = {
    "欧几里得": "Q8747",
    "阿基米德": "Q8730",
    "牛顿": "Q935",
    "莱布尼茨": "Q9047",
    "欧拉": "Q5674",
    "拉格朗日": "Q80227",
    "拉普拉斯": "Q44414",
    "傅里叶": "Q145611",
    "高斯": "Q6722",
    "勒让德": "Q164503",
    "雅可比": "Q155812",
    "阿贝尔": "Q124607",
    "伽罗瓦": "Q210401",
    "柯西": "Q12806",
    "黎曼": "Q422",
    "魏尔斯特拉斯": "Q58549",
    "康托尔": "Q60119",
    "戴德金": "Q76474",
    "克罗内克": "Q89540",
    "庞加莱": "Q81049",
    "希尔伯特": "Q82597",
    "诺特": "Q8028",
    "巴拿赫": "Q180102",
    "冯诺依曼": "Q1746",
    "哥德尔": "Q41390",
    "图灵": "Q7251",
    "香农": "Q235650",
    "维纳": "Q163415",
    "柯尔莫哥洛夫": "Q153224",
    "勒贝格": "Q133193",
    "博雷尔": "Q193660",
    "策梅洛": "Q150654",
    "罗素": "Q99585",
    "丘奇": "Q273619",
    "塔斯基": "Q207976",
    "外尔": "Q80227",
    "嘉当": "Q164014",
    "韦伊": "Q209098",
    "布尔巴基": "Q193758",
    "格罗滕迪克": "Q193803",
    "塞尔": "Q207690",
    "博特": "Q358264",
    "米尔诺": "Q381335",
    "斯梅尔": "Q358859",
    "阿蒂亚": "Q161822",
    "希策布鲁赫": "Q156246",
    "德利涅": "Q168538",
    "法尔廷斯": "Q57465",
    "森重文": "Q358283",
    "唐纳森": "Q358264",
    "威滕": "Q232639",
    "孔采维奇": "Q336102",
    "彼得·舒尔策": "Q1642065",
    "洛朗·拉福格": "Q337308",
    "怀尔斯": "Q295696",
    "佩雷尔曼": "Q41395",
    "陈省身": "Q80792",
    "丘成桐": "Q333520",
    "陶哲轩": "Q210506",
    "张益唐": "Q15730907",
    "梅纳德": "Q16946062",
    "纳什": "Q1746",
    "吴文俊": "Q520330",
    "华罗庚": "Q323283",
    "陈景润": "Q726635",
    "爱因斯坦": "Q937",
    "普朗克": "Q10289",
    "玻尔": "Q1033",
    "海森堡": "Q40904",
    "薛定谔": "Q9130",
    "狄拉克": "Q47480",
    "费曼": "Q39246",
    "霍金": "Q40806",
    "彭罗斯": "Q193605",
    "麦克斯韦": "Q3741",
    "玻尔兹曼": "Q41229",
}


REPORT_MARKERS = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单"]


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].lstrip("\n")
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def main():
    changed = 0
    skipped_report = 0
    for p in MATH_DIR.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            continue
        title = str(fm.get("title", ""))
        stem = p.stem
        if stem.startswith("00-") or any(m in title or m in stem for m in REPORT_MARKERS):
            skipped_report += 1
            continue
        matched_qid = None
        for key, qid in WIKIDATA_QID.items():
            if key in title or key in stem:
                matched_qid = qid
                break
        if not matched_qid:
            continue
        external_ids = fm.get("external_ids") or {}
        if external_ids.get("wikidata_id"):
            continue
        external_ids["wikidata_id"] = f"https://www.wikidata.org/entity/{matched_qid}"
        fm["external_ids"] = external_ids
        new_text = (
            "---\n"
            + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
            + "---\n"
            + body
        )
        p.write_text(new_text, encoding="utf-8")
        changed += 1

    print(f"Injected Wikidata IDs into {changed} mathematician docs (skipped {skipped_report} reports).")


if __name__ == "__main__":
    main()
