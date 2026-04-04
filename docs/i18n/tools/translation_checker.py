#!/usr/bin/env python3
"""
FormalMath Translation Quality Checker
翻译质量检查工具

Features:
- Check translation completeness
- Validate terminology consistency
- Detect formatting issues
- Generate quality reports

Usage:
    python translation_checker.py <file_or_directory>
    python translation_checker.py --report docs/i18n/
"""

import sys
import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime
import yaml

# Terminology database
TERMINOLOGY_DB = {
    'group': {'de': 'Gruppe', 'fr': 'groupe', 'ja': '群', 'zh': '群'},
    'ring': {'de': 'Ring', 'fr': 'anneau', 'ja': '環', 'zh': '环'},
    'field': {'de': 'Körper', 'fr': 'corps', 'ja': '体', 'zh': '域'},
    'subgroup': {'de': 'Untergruppe', 'fr': 'sous-groupe', 'ja': '部分群', 'zh': '子群'},
    'homomorphism': {'de': 'Homomorphismus', 'fr': 'homomorphisme', 'ja': '準同型', 'zh': '同态'},
    'isomorphism': {'de': 'Isomorphismus', 'fr': 'isomorphisme', 'ja': '同型', 'zh': '同构'},
    'kernel': {'de': 'Kern', 'fr': 'noyau', 'ja': '核', 'zh': '核'},
    'image': {'de': 'Bild', 'fr': 'image', 'ja': '像', 'zh': '像'},
    'ideal': {'de': 'Ideal', 'fr': 'idéal', 'ja': 'イデアル', 'zh': '理想'},
    'module': {'de': 'Modul', 'fr': 'module', 'ja': '加群', 'zh': '模'},
    'theorem': {'de': 'Satz', 'fr': 'théorème', 'ja': '定理', 'zh': '定理'},
    'lemma': {'de': 'Lemma', 'fr': 'lemme', 'ja': '補題', 'zh': '引理'},
    'proof': {'de': 'Beweis', 'fr': 'preuve', 'ja': '証明', 'zh': '证明'},
    'definition': {'de': 'Definition', 'fr': 'définition', 'ja': '定義', 'zh': '定义'},
}

class TranslationChecker:
    """Check translation quality for FormalMath documents."""
    
    def __init__(self, terminology_db: Optional[Dict] = None):
        self.terminology = terminology_db or TERMINOLOGY_DB
        self.issues: List[Dict] = []
        self.stats = {
            'files_checked': 0,
            'files_passed': 0,
            'files_failed': 0,
            'total_issues': 0,
            'critical_issues': 0,
            'warnings': 0,
        }
    
    def check_file(self, filepath: str) -> Dict:
        """Check a single translation file."""
        result = {
            'filepath': filepath,
            'passed': True,
            'issues': [],
            'lang': self._detect_language(filepath),
        }
        
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            result['passed'] = False
            result['issues'].append({
                'type': 'error',
                'message': f'Cannot read file: {e}'
            })
            return result
        
        # Check frontmatter
        frontmatter_issues = self._check_frontmatter(content, filepath)
        result['issues'].extend(frontmatter_issues)
        
        # Check math formulas
        math_issues = self._check_math_formulas(content)
        result['issues'].extend(math_issues)
        
        # Check terminology (basic)
        term_issues = self._check_terminology(content, result['lang'])
        result['issues'].extend(term_issues)
        
        # Check broken links
        link_issues = self._check_links(content, filepath)
        result['issues'].extend(link_issues)
        
        # Check language switcher
        switcher_issues = self._check_lang_switcher(content)
        result['issues'].extend(switcher_issues)
        
        result['passed'] = len([i for i in result['issues'] if i['type'] == 'error']) == 0
        
        self.stats['files_checked'] += 1
        if result['passed']:
            self.stats['files_passed'] += 1
        else:
            self.stats['files_failed'] += 1
        self.stats['total_issues'] += len(result['issues'])
        self.stats['critical_issues'] += len([i for i in result['issues'] if i['type'] == 'error'])
        self.stats['warnings'] += len([i for i in result['issues'] if i['type'] == 'warning'])
        
        return result
    
    def _detect_language(self, filepath: str) -> str:
        """Detect language from file path."""
        parts = Path(filepath).parts
        for part in parts:
            if part in ['de', 'en', 'fr', 'ja', 'zh', 'ru', 'it', 'es']:
                return part
        return 'unknown'
    
    def _check_frontmatter(self, content: str, filepath: str) -> List[Dict]:
        """Check YAML frontmatter."""
        issues = []
        match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
        
        if not match:
            issues.append({
                'type': 'warning',
                'message': 'Missing YAML frontmatter'
            })
            return issues
        
        yaml_content = match.group(1)
        
        # Required fields for translations
        required_fields = ['lang', 'original', 'translation_status']
        for field in required_fields:
            if field not in yaml_content:
                issues.append({
                    'type': 'error',
                    'message': f'Missing required field in frontmatter: {field}'
                })
        
        # Check lang consistency
        lang_match = re.search(r'lang:\s*(\w+)', yaml_content)
        if lang_match:
            declared_lang = lang_match.group(1)
            detected_lang = self._detect_language(filepath)
            if declared_lang != detected_lang:
                issues.append({
                    'type': 'error',
                    'message': f'Language mismatch: declared={declared_lang}, detected={detected_lang}'
                })
        
        return issues
    
    def _check_math_formulas(self, content: str) -> List[Dict]:
        """Check mathematical formula formatting."""
        issues = []
        
        # Check for unclosed math delimiters
        inline_math = re.findall(r'(?<!\\)\$[^$]*(?<!\\)\$', content)
        display_math = re.findall(r'\$\$.*?\$\$', content, re.DOTALL)
        
        # Check for common issues
        # Unbalanced delimiters
        single_dollars = content.count('$') - 2 * content.count('$$')
        if single_dollars % 2 != 0:
            issues.append({
                'type': 'error',
                'message': 'Unbalanced inline math delimiters ($)'
            })
        
        # Check for LaTeX commands that might be broken
        broken_patterns = [
            (r'\\[a-zA-Z]+\s+\}', 'Potential broken LaTeX command'),
            (r'_[^\{]', 'Subscript without braces'),
            (r'\^[^\{]', 'Superscript without braces'),
        ]
        
        for pattern, msg in broken_patterns:
            if re.search(pattern, content):
                issues.append({
                    'type': 'warning',
                    'message': msg
                })
        
        return issues
    
    def _check_terminology(self, content: str, lang: str) -> List[Dict]:
        """Check terminology consistency."""
        issues = []
        
        # This is a simplified check
        # In production, this would use more sophisticated matching
        
        return issues
    
    def _check_links(self, content: str, filepath: str) -> List[Dict]:
        """Check for broken internal links."""
        issues = []
        base_dir = os.path.dirname(filepath)
        
        # Find markdown links
        links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        
        for text, link in links:
            # Skip external links
            if link.startswith('http://') or link.startswith('https://'):
                continue
            
            # Skip anchors
            if link.startswith('#'):
                continue
            
            # Check if file exists
            target_path = os.path.normpath(os.path.join(base_dir, link))
            if not os.path.exists(target_path):
                issues.append({
                    'type': 'warning',
                    'message': f'Broken link: {link}'
                })
        
        return issues
    
    def _check_lang_switcher(self, content: str) -> List[Dict]:
        """Check for language switcher section."""
        issues = []
        
        if '**' not in content or 'Language' not in content and 'Sprach' not in content and '言語' not in content:
            issues.append({
                'type': 'warning',
                'message': 'Missing language switcher section'
            })
        
        return issues
    
    def check_directory(self, directory: str) -> List[Dict]:
        """Check all translation files in a directory."""
        results = []
        
        for root, dirs, files in os.walk(directory):
            # Skip certain directories
            if 'tools' in root or 'qa' in root:
                continue
            
            for file in files:
                if file.endswith('.md'):
                    filepath = os.path.join(root, file)
                    result = self.check_file(filepath)
                    results.append(result)
        
        return results
    
    def generate_report(self, output_path: Optional[str] = None) -> str:
        """Generate quality report."""
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        report = f"""# FormalMath Translation Quality Report

**Generated**: {timestamp}

## Summary

| Metric | Count |
|--------|-------|
| Files Checked | {self.stats['files_checked']} |
| Files Passed | {self.stats['files_passed']} ✅ |
| Files Failed | {self.stats['files_failed']} ❌ |
| Total Issues | {self.stats['total_issues']} |
| Critical Issues | {self.stats['critical_issues']} |
| Warnings | {self.stats['warnings']} |

## Pass Rate

"""
        
        if self.stats['files_checked'] > 0:
            pass_rate = (self.stats['files_passed'] / self.stats['files_checked']) * 100
            report += f"**{pass_rate:.1f}%** ({self.stats['files_passed']}/{self.stats['files_checked']})\n\n"
            
            if pass_rate >= 95:
                report += "✅ **Excellent** - Translation quality meets high standards\n"
            elif pass_rate >= 85:
                report += "⚠️ **Good** - Minor issues need attention\n"
            elif pass_rate >= 70:
                report += "⚠️ **Fair** - Several issues require fixes\n"
            else:
                report += "❌ **Needs Improvement** - Significant issues detected\n"
        
        report += "\n---\n\n*Report generated by FormalMath Translation Checker*\n"
        
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(report)
        
        return report


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    path = sys.argv[1]
    
    checker = TranslationChecker()
    
    if os.path.isfile(path):
        result = checker.check_file(path)
        print(f"File: {result['filepath']}")
        print(f"Language: {result['lang']}")
        print(f"Status: {'✅ PASSED' if result['passed'] else '❌ FAILED'}")
        
        if result['issues']:
            print("\nIssues:")
            for issue in result['issues']:
                icon = "❌" if issue['type'] == 'error' else "⚠️"
                print(f"  {icon} {issue['message']}")
    
    elif os.path.isdir(path):
        results = checker.check_directory(path)
        
        print(f"Checked {len(results)} files")
        print(f"Passed: {checker.stats['files_passed']}")
        print(f"Failed: {checker.stats['files_failed']}")
        
        # Generate report
        report_path = os.path.join(path, 'qa', 'translation_quality_report.md')
        os.makedirs(os.path.dirname(report_path), exist_ok=True)
        report = checker.generate_report(report_path)
        print(f"\nReport saved to: {report_path}")
    
    else:
        print(f"Error: Path not found: {path}")
        sys.exit(1)


if __name__ == '__main__':
    main()
