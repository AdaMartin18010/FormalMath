#!/usr/bin/env python3
"""
Wikipedia多语言概念对齐工具 - 演示版本
处理前10个概念作为示例
"""

import yaml
import json
import time
import urllib.request
import urllib.parse
import ssl
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass

# 禁用SSL验证警告
ssl._create_default_https_context = ssl._create_unverified_context

@dataclass
class MultilangInfo:
    """多语言信息"""
    en_title: str = ""
    en_extract: str = ""
    de_title: str = ""
    de_extract: str = ""
    fr_title: str = ""
    fr_extract: str = ""
    ja_title: str = ""
    ja_extract: str = ""
    en_url: str = ""
    de_url: str = ""
    fr_url: str = ""
    ja_url: str = ""
    alignment_confidence: str = "medium"


class DemoAligner:
    """演示版本对齐器"""
    
    COMMON_MATH_TERMS = {
        "limit": "Limit (mathematics)",
        "continuity": "Continuous function",
        "derivative": "Derivative",
        "riemann_integral": "Integral",
        "lebesgue_integral": "Lebesgue integration",
        "infinite_series": "Series (mathematics)",
        "sequence": "Sequence",
        "convergence": "Limit of a sequence",
        "uniform_convergence": "Uniform convergence",
        "power_series": "Power series",
        "fourier_series": "Fourier series",
    }
    
    def __init__(self, yaml_path: str, output_dir: str, limit: int = 10):
        self.yaml_path = Path(yaml_path)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.limit = limit
        self.results: Dict[str, MultilangInfo] = {}
        
    def fetch_wikipedia_data(self, title: str, lang: str) -> Optional[Dict]:
        """获取Wikipedia页面数据"""
        try:
            url = f"https://{lang}.wikipedia.org/w/api.php"
            params = {
                "action": "query",
                "format": "json",
                "titles": title,
                "prop": "extracts|langlinks",
                "explaintext": True,
                "exintro": True,
                "exlimit": 1,
                "lllimit": 100,
                "redirects": 1
            }
            query_string = urllib.parse.urlencode(params)
            full_url = f"{url}?{query_string}"
            
            headers = {"User-Agent": "FormalMath/1.0 (research@formalmath.org)"}
            req = urllib.request.Request(full_url, headers=headers)
            
            with urllib.request.urlopen(req, timeout=30) as response:
                data = json.loads(response.read().decode('utf-8'))
                
                if 'query' in data and 'pages' in data['query']:
                    pages = data['query']['pages']
                    page_id = list(pages.keys())[0]
                    
                    if page_id == '-1':
                        return None
                    
                    page_data = pages[page_id]
                    return {
                        'title': page_data.get('title', title),
                        'extract': page_data.get('extract', '')[:400] if page_data.get('extract') else '',
                        'langlinks': page_data.get('langlinks', [])
                    }
                return None
        except Exception as e:
            print(f"    Error: {str(e)[:40]}")
            return None
    
    def find_langlink(self, langlinks: List[Dict], target_lang: str) -> Optional[str]:
        """查找语言链接"""
        for link in langlinks:
            if link.get('lang') == target_lang:
                return link.get('*', '')
        return None
    
    def align_concept(self, concept_id: str, name: str) -> MultilangInfo:
        """对齐概念"""
        info = MultilangInfo()
        en_title = self.COMMON_MATH_TERMS.get(concept_id, name.replace(" ", "_"))
        
        print(f"  EN: {en_title}")
        en_data = self.fetch_wikipedia_data(en_title, 'en')
        
        if en_data:
            info.en_title = en_data['title']
            info.en_extract = en_data['extract'][:300] if en_data['extract'] else ""
            info.en_url = f"https://en.wikipedia.org/wiki/{en_title.replace(' ', '_')}"
            
            if en_data.get('langlinks'):
                # 德文
                de_title = self.find_langlink(en_data['langlinks'], 'de')
                if de_title:
                    print(f"  DE: {de_title}")
                    info.de_title = de_title
                    info.de_url = f"https://de.wikipedia.org/wiki/{de_title.replace(' ', '_')}"
                    de_data = self.fetch_wikipedia_data(de_title, 'de')
                    if de_data:
                        info.de_extract = de_data['extract'][:300] if de_data['extract'] else ""
                
                # 法文
                fr_title = self.find_langlink(en_data['langlinks'], 'fr')
                if fr_title:
                    print(f"  FR: {fr_title}")
                    info.fr_title = fr_title
                    info.fr_url = f"https://fr.wikipedia.org/wiki/{fr_title.replace(' ', '_')}"
                    fr_data = self.fetch_wikipedia_data(fr_title, 'fr')
                    if fr_data:
                        info.fr_extract = fr_data['extract'][:300] if fr_data['extract'] else ""
                
                # 日文
                ja_title = self.find_langlink(en_data['langlinks'], 'ja')
                if ja_title:
                    print(f"  JA: {ja_title}")
                    info.ja_title = ja_title
                    info.ja_url = f"https://ja.wikipedia.org/wiki/{urllib.parse.quote(ja_title)}"
                    ja_data = self.fetch_wikipedia_data(ja_title, 'ja')
                    if ja_data:
                        info.ja_extract = ja_data['extract'][:300] if ja_data['extract'] else ""
            
            found_langs = sum([1 if info.de_title else 0, 1 if info.fr_title else 0, 1 if info.ja_title else 0])
            info.alignment_confidence = "high" if found_langs == 3 else ("medium" if found_langs >= 1 else "low")
        else:
            info.alignment_confidence = "low"
        
        return info
    
    def run(self):
        """执行演示"""
        print("=" * 60)
        print("Wikipedia多语言对齐工具 - 演示版")
        print("=" * 60)
        
        # 加载YAML
        with open(self.yaml_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        concepts = data.get('concepts', [])[:self.limit]
        print(f"Processing first {len(concepts)} concepts...\n")
        
        for idx, concept in enumerate(concepts, 1):
            concept_id = concept.get('concept_id', '')
            name = concept.get('name', '')
            
            print(f"[{idx}/{len(concepts)}] {name} ({concept_id})")
            info = self.align_concept(concept_id, name)
            self.results[concept_id] = info
            time.sleep(0.5)
        
        # 生成输出
        self.generate_outputs()
        print("\n" + "=" * 60)
        print("Demo completed!")
        print("=" * 60)
    
    def generate_outputs(self):
        """生成输出文件"""
        # JSON
        json_data = []
        for concept_id, info in self.results.items():
            json_data.append({
                'concept_id': concept_id,
                'multilang': {
                    'en': {'title': info.en_title, 'url': info.en_url, 'extract': info.en_extract},
                    'de': {'title': info.de_title, 'url': info.de_url, 'extract': info.de_extract},
                    'fr': {'title': info.fr_title, 'url': info.fr_url, 'extract': info.fr_extract},
                    'ja': {'title': info.ja_title, 'url': info.ja_url, 'extract': info.ja_extract}
                },
                'alignment_confidence': info.alignment_confidence
            })
        
        json_path = self.output_dir / "multilang_concept_table.json"
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(json_data, f, ensure_ascii=False, indent=2)
        print(f"\nJSON saved: {json_path}")
        
        # Markdown报告
        lines = [
            "# Wikipedia多语言概念对齐报告",
            "",
            f"**生成日期**: {time.strftime('%Y年%m月%d日')}",
            f"**处理概念数**: {len(self.results)} (演示版)",
            "",
            "## 概念对照表",
            "",
            "| 概念ID | 英文 | 德文 | 法文 | 日文 | 置信度 |",
            "|--------|------|------|------|------|--------|",
        ]
        
        for concept_id, info in self.results.items():
            en = info.en_title[:20] + "..." if len(info.en_title) > 20 else info.en_title
            de = info.de_title[:20] + "..." if len(info.de_title) > 20 else info.de_title
            fr = info.fr_title[:20] + "..." if len(info.fr_title) > 20 else info.fr_title
            ja = info.ja_title[:15] + "..." if len(info.ja_title) > 15 else info.ja_title
            lines.append(f"| {concept_id} | {en} | {de} | {fr} | {ja} | {info.alignment_confidence} |")
        
        lines.extend([
            "",
            "## 术语对照示例",
            "",
            "| 英文 | 德文 | 法文 | 日文 |",
            "|------|------|------|------|",
            "| Limit | Grenzwert | Limite | 極限 |",
            "| Derivative | Ableitung | Dérivée | 導関数 |",
            "| Integral | Integral | Intégrale | 積分 |",
            "",
            "---",
            "*演示版本 - 完整版请运行 wikipedia_multilang_align.py*",
        ])
        
        md_path = self.output_dir / "00-Wikipedia多语言对齐报告.md"
        with open(md_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
        print(f"Report saved: {md_path}")


if __name__ == "__main__":
    aligner = DemoAligner(
        yaml_path="g:\\_src\\FormalMath\\project\\concept_prerequisites.yaml",
        output_dir="g:\\_src\\FormalMath",
        limit=10
    )
    aligner.run()
