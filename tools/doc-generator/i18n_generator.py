#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
国际化文档生成器
Internationalization (i18n) Document Generator

生成多语言版本的文档
"""

import re
import json
from pathlib import Path
from typing import List, Dict, Any, Optional
from datetime import datetime
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class TranslationEntry:
    """翻译条目"""
    key: str
    zh: str
    en: str
    context: str = ""


class I18nGenerator:
    """
    国际化文档生成器
    
    生成多语言版本的文档，支持中英文对照
    """
    
    def __init__(self, output_dir: Path, template_dir: Path = None, 
                 languages: List[str] = None, default_language: str = "zh"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.template_dir = template_dir
        self.languages = languages or ["zh", "en"]
        self.default_language = default_language
        
        # 翻译字典
        self.translations: Dict[str, Dict[str, str]] = {
            'zh': {},
            'en': {}
        }
        
        # 数学术语翻译
        self._load_math_translations()
    
    def _load_math_translations(self):
        """加载数学术语翻译"""
        math_terms = {
            # 基础概念
            '集合论': 'Set Theory',
            '群论': 'Group Theory',
            '环论': 'Ring Theory',
            '域论': 'Field Theory',
            '拓扑学': 'Topology',
            '实分析': 'Real Analysis',
            '复分析': 'Complex Analysis',
            '泛函分析': 'Functional Analysis',
            '微分几何': 'Differential Geometry',
            '代数几何': 'Algebraic Geometry',
            '数论': 'Number Theory',
            '概率论': 'Probability Theory',
            '数理逻辑': 'Mathematical Logic',
            
            # 术语
            '定理': 'Theorem',
            '引理': 'Lemma',
            '推论': 'Corollary',
            '定义': 'Definition',
            '命题': 'Proposition',
            '证明': 'Proof',
            '例子': 'Example',
            '注记': 'Remark',
            
            # 结构
            '群': 'Group',
            '环': 'Ring',
            '域': 'Field',
            '模': 'Module',
            '向量空间': 'Vector Space',
            '线性映射': 'Linear Map',
            '同态': 'Homomorphism',
            '同构': 'Isomorphism',
            
            # 分析
            '极限': 'Limit',
            '连续': 'Continuous',
            '可微': 'Differentiable',
            '可积': 'Integrable',
            '级数': 'Series',
            '收敛': 'Convergent',
            
            # 拓扑
            '开集': 'Open Set',
            '闭集': 'Closed Set',
            '紧致': 'Compact',
            '连通': 'Connected',
            '同胚': 'Homeomorphism',
            
            # 导航
            '目录': 'Table of Contents',
            '前言': 'Preface',
            '引言': 'Introduction',
            '总结': 'Summary',
            '参考文献': 'References',
            '索引': 'Index',
            '附录': 'Appendix',
        }
        
        for zh, en in math_terms.items():
            self.translations['zh'][zh] = zh
            self.translations['en'][zh] = en
    
    def generate_from_directory(self, source_dir: Path) -> List[str]:
        """
        从源目录生成为多语言文档
        
        Args:
            source_dir: 源文档目录
            
        Returns:
            生成的文件路径列表
        """
        generated_files = []
        source_dir = Path(source_dir)
        
        print(f"  扫描多语言文档源: {source_dir}")
        
        # 为每种语言创建输出目录
        for lang in self.languages:
            lang_dir = self.output_dir / lang
            lang_dir.mkdir(exist_ok=True)
        
        # 扫描Markdown文件
        if source_dir.exists():
            md_files = list(source_dir.rglob("*.md"))
            print(f"  找到 {len(md_files)} 个Markdown文件")
            
            for md_file in md_files[:30]:  # 限制处理数量
                try:
                    files = self._process_document(md_file, source_dir)
                    generated_files.extend(files)
                except Exception as e:
                    print(f"  警告: 处理 {md_file} 失败: {e}")
        
        # 生成翻译文件
        generated_files.append(str(self._generate_translation_file()))
        
        # 生成语言切换导航
        generated_files.append(str(self._generate_language_nav()))
        
        # 生成对照文档
        generated_files.append(str(self._generate_bilingual_docs()))
        
        return generated_files
    
    def _process_document(self, file_path: Path, base_dir: Path) -> List[str]:
        """处理单个文档"""
        generated = []
        
        content = file_path.read_text(encoding='utf-8')
        relative_path = file_path.relative_to(base_dir)
        
        # 为每种语言生成版本
        for lang in self.languages:
            lang_dir = self.output_dir / lang
            output_path = lang_dir / relative_path
            output_path.parent.mkdir(parents=True, exist_ok=True)
            
            if lang == self.default_language:
                # 默认语言保持原样
                translated = content
            else:
                # 翻译内容
                translated = self._translate_content(content, lang)
            
            # 添加语言切换链接
            header = self._generate_language_switcher(lang, relative_path)
            translated = header + translated
            
            output_path.write_text(translated, encoding='utf-8')
            generated.append(str(output_path))
        
        return generated
    
    def _translate_content(self, content: str, target_lang: str) -> str:
        """翻译内容"""
        if target_lang == self.default_language:
            return content
        
        translated = content
        
        # 翻译标题
        for zh_term, en_term in self.translations['en'].items():
            # 翻译Markdown标题
            pattern = rf'^(#+)\s*{re.escape(zh_term)}'
            replacement = rf'\1 {en_term}'
            translated = re.sub(pattern, replacement, translated, flags=re.MULTILINE)
            
            # 翻译普通文本中的术语
            if target_lang == 'en':
                # 简单的术语替换
                translated = translated.replace(zh_term, en_term)
        
        # 添加翻译提示
        translated = f"> 🌐 This document is machine-translated from Chinese. Some terms may not be accurate.\n\n" + translated
        
        return translated
    
    def _generate_language_switcher(self, current_lang: str, relative_path: Path) -> str:
        """生成语言切换链接"""
        switcher = "<div class=\"language-switcher\">\n\n"
        switcher += "**Languages**: "
        
        lang_names = {'zh': '🇨🇳 中文', 'en': '🇬🇧 English'}
        
        links = []
        for lang in self.languages:
            if lang == current_lang:
                links.append(f"**{lang_names.get(lang, lang)}**")
            else:
                # 计算相对路径
                depth = len(relative_path.parent.parts)
                prefix = '../' * depth if depth > 0 else './'
                links.append(f"[{lang_names.get(lang, lang)}]({prefix}{lang}/{relative_path})")
        
        switcher += ' | '.join(links)
        switcher += "\n\n</div>\n\n---\n\n"
        
        return switcher
    
    def _generate_translation_file(self) -> Path:
        """生成翻译对照文件"""
        output_path = self.output_dir / "translations.json"
        
        translation_data = {
            'metadata': {
                'generated_at': datetime.now().isoformat(),
                'total_terms': len(self.translations['en']),
                'languages': self.languages
            },
            'translations': []
        }
        
        for zh_term, en_term in sorted(self.translations['en'].items()):
            translation_data['translations'].append({
                'zh': zh_term,
                'en': en_term,
                'category': self._categorize_term(zh_term)
            })
        
        output_path.write_text(json.dumps(translation_data, ensure_ascii=False, indent=2), encoding='utf-8')
        return output_path
    
    def _categorize_term(self, term: str) -> str:
        """对术语进行分类"""
        categories = {
            '基础概念': ['集合论', '群论', '环论', '域论', '拓扑学'],
            '分析学': ['实分析', '复分析', '泛函分析', '极限', '连续'],
            '代数学': ['群', '环', '域', '模', '同态', '同构'],
            '导航': ['目录', '前言', '总结', '参考文献']
        }
        
        for category, terms in categories.items():
            if any(t in term for t in terms):
                return category
        
        return '其他'
    
    def _generate_language_nav(self) -> Path:
        """生成语言导航索引"""
        output_path = self.output_dir / "language_nav.md"
        
        content = f'''# 🌐 多语言文档导航

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 可用语言

| 语言 | 代码 | 状态 |
|------|------|------|
| 🇨🇳 中文 | zh | ✅ 完整 |
| 🇬🇧 English | en | ⚠️ 机器翻译 |

## 浏览文档

'''
        
        for lang in self.languages:
            lang_name = {'zh': '中文', 'en': 'English'}.get(lang, lang)
            content += f"### {lang_name}\n\n"
            content += f"- [{lang_name} 文档索引]({lang}/index.md)\n\n"
        
        content += '''
## 翻译说明

- **中文 (zh)**: 原始文档，人工编写和审核
- **English (en)**: 机器自动翻译，可能存在不准确之处

### 术语翻译对照

参见 [translations.json](translations.json) 获取完整的术语翻译对照表。

## 贡献翻译

如果您发现翻译错误或有改进建议，欢迎：

1. 提交 Issue 描述问题
2. 提交 Pull Request 修复翻译
3. 联系维护者讨论

---
*由 FormalMath 国际化生成器创建*
'''
        
        output_path.write_text(content, encoding='utf-8')
        return output_path
    
    def _generate_bilingual_docs(self) -> Path:
        """生成中英对照文档"""
        output_path = self.output_dir / "bilingual_glossary.md"
        
        content = f'''# 中英数学术语对照表

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 基础数学

| 中文 | English | 备注 |
|------|---------|------|
| 集合论 | Set Theory | |
| 数论 | Number Theory | |
| 数理逻辑 | Mathematical Logic | |

## 代数学

| 中文 | English | 备注 |
|------|---------|------|
| 群论 | Group Theory | |
| 环论 | Ring Theory | |
| 域论 | Field Theory | |
| 模论 | Module Theory | |
| 李代数 | Lie Algebra | 以Sophus Lie命名 |
| 线性代数 | Linear Algebra | |
| 表示论 | Representation Theory | |
| 同调代数 | Homological Algebra | |
| 范畴论 | Category Theory | |

## 分析学

| 中文 | English | 备注 |
|------|---------|------|
| 实分析 | Real Analysis | |
| 复分析 | Complex Analysis | |
| 泛函分析 | Functional Analysis | |
| 调和分析 | Harmonic Analysis | |
| 微分方程 | Differential Equations | |
| 偏微分方程 | Partial Differential Equations | PDE |
| 测度论 | Measure Theory | |
| 变分法 | Calculus of Variations | |

## 几何与拓扑

| 中文 | English | 备注 |
|------|---------|------|
| 拓扑学 | Topology | |
| 代数拓扑 | Algebraic Topology | |
| 微分几何 | Differential Geometry | |
| 代数几何 | Algebraic Geometry | |
| 黎曼几何 | Riemannian Geometry | |
| 辛几何 | Symplectic Geometry | |
| 微分拓扑 | Differential Topology | |

## 其他领域

| 中文 | English | 备注 |
|------|---------|------|
| 概率论 | Probability Theory | |
| 数理统计 | Mathematical Statistics | |
| 离散数学 | Discrete Mathematics | |
| 组合数学 | Combinatorics | |
| 图论 | Graph Theory | |
| 密码学 | Cryptography | |
| 优化理论 | Optimization Theory | |
| 控制论 | Control Theory | |

## 常用术语

| 中文 | English | 备注 |
|------|---------|------|
| 定理 | Theorem | 重要结果 |
| 引理 | Lemma | 辅助结果 |
| 推论 | Corollary | 直接结果 |
| 命题 | Proposition | 一般结果 |
| 定义 | Definition | |
| 证明 | Proof | |
| 例子 | Example | |
| 练习 | Exercise | |
| 注记 | Remark | |

## 人名翻译

| 原文 | 中文译名 | 领域 |
|------|----------|------|
| Euclid | 欧几里得 | 几何学 |
| Newton | 牛顿 | 微积分 |
| Leibniz | 莱布尼茨 | 微积分 |
| Euler | 欧拉 | 分析学 |
| Gauss | 高斯 | 数论、几何 |
| Riemann | 黎曼 | 几何、分析 |
| Cauchy | 柯西 | 分析学 |
| Galois | 伽罗瓦 | 代数学 |
| Hilbert | 希尔伯特 | 基础数学 |
| Poincaré | 庞加莱 | 拓扑学 |
| Noether | 诺特 | 代数学 |
| Weil | 韦伊 | 数论、几何 |
| Grothendieck | 格洛腾迪克 | 代数几何 |
| Serre | 塞尔 | 代数拓扑 |

---
*由 FormalMath 国际化生成器创建*
'''
        
        output_path.write_text(content, encoding='utf-8')
        return output_path
    
    def add_translation(self, key: str, translations: Dict[str, str]):
        """添加自定义翻译"""
        for lang, text in translations.items():
            if lang not in self.translations:
                self.translations[lang] = {}
            self.translations[lang][key] = text


def main():
    """主函数"""
    generator = I18nGenerator(
        output_dir=Path("tools/doc-generator/output/i18n"),
        languages=["zh", "en"],
        default_language="zh"
    )
    
    files = generator.generate_from_directory(Path("docs/01-基础数学"))
    print(f"\n生成文件:")
    for f in files[:10]:
        print(f"  - {f}")


if __name__ == '__main__':
    main()
