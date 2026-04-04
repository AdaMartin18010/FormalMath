#!/usr/bin/env python3
"""
FormalMath Language Switcher Tool
语言切换工具 - 支持多语言文档间的切换

Usage:
    python lang_switcher.py <document_path> [target_lang]
    
Examples:
    python lang_switcher.py docs/i18n/en/core/Group.md de
    python lang_switcher.py docs/i18n/de/core/Gruppe.md
"""

import sys
import re
import os
from pathlib import Path
from typing import Optional, Dict, List

# Language configuration
LANG_NAMES = {
    'zh': '中文',
    'en': 'English',
    'de': 'Deutsch',
    'fr': 'Français',
    'ja': '日本語',
    'ru': 'Русский',
    'it': 'Italiano',
    'es': 'Español'
}

LANG_CODES = list(LANG_NAMES.keys())

# Document name mappings
DOC_MAPPINGS = {
    'Group.md': {'de': 'Gruppe.md', 'fr': 'Groupe.md', 'ja': '群.md', 'zh': '01-群论-国际标准深度扩展版.md'},
    'Gruppe.md': {'en': 'Group.md', 'fr': 'Groupe.md', 'ja': '群.md', 'zh': '01-群论-国际标准深度扩展版.md'},
    'Groupe.md': {'en': 'Group.md', 'de': 'Gruppe.md', 'ja': '群.md', 'zh': '01-群论-国际标准深度扩展版.md'},
    '群.md': {'en': 'Group.md', 'de': 'Gruppe.md', 'fr': 'Groupe.md', 'zh': '01-群论-国际标准深度扩展版.md'},
    'Ring.md': {'de': 'Ring.md', 'fr': 'Anneau.md', 'ja': '環.md', 'zh': '01-环论-国际标准深度扩展版.md'},
    'Anneau.md': {'en': 'Ring.md', 'de': 'Ring.md', 'ja': '環.md', 'zh': '01-环论-国际标准深度扩展版.md'},
    '環.md': {'en': 'Ring.md', 'de': 'Ring.md', 'fr': 'Anneau.md', 'zh': '01-环论-国际标准深度扩展版.md'},
    'Field.md': {'de': 'Körper.md', 'fr': 'Corps.md', 'ja': '体.md', 'zh': '01-域论-国际标准深度扩展版.md'},
    'Körper.md': {'en': 'Field.md', 'fr': 'Corps.md', 'ja': '体.md', 'zh': '01-域论-国际标准深度扩展版.md'},
    'Corps.md': {'en': 'Field.md', 'de': 'Körper.md', 'ja': '体.md', 'zh': '01-域论-国际标准深度扩展版.md'},
    '体.md': {'en': 'Field.md', 'de': 'Körper.md', 'fr': 'Corps.md', 'zh': '01-域论-国际标准深度扩展版.md'},
}


def extract_frontmatter(content: str) -> Dict[str, str]:
    """Extract YAML frontmatter from markdown content."""
    frontmatter = {}
    match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
    if match:
        yaml_content = match.group(1)
        for line in yaml_content.split('\n'):
            if ':' in line:
                key, value = line.split(':', 1)
                frontmatter[key.strip()] = value.strip()
    return frontmatter


def get_current_lang(file_path: str) -> str:
    """Detect current language from file path."""
    parts = Path(file_path).parts
    for part in parts:
        if part in LANG_CODES:
            return part
    return 'zh'  # Default to Chinese for original docs


def get_target_path(current_path: str, target_lang: str) -> Optional[str]:
    """Calculate target file path for language switch."""
    path = Path(current_path)
    current_lang = get_current_lang(current_path)
    filename = path.name
    
    if current_lang == target_lang:
        return current_path
    
    # Get target filename
    target_filename = filename
    if filename in DOC_MAPPINGS:
        mappings = DOC_MAPPINGS[filename]
        if target_lang in mappings:
            target_filename = mappings[target_lang]
    
    # Build target path
    if target_lang == 'zh':
        # Map to original Chinese docs
        if 'Group' in target_filename or '群' in target_filename:
            return 'docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md'
        elif 'Ring' in target_filename or '环' in target_filename or 'Anneau' in target_filename or '環' in target_filename:
            return 'docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md'
        elif 'Field' in target_filename or '域' in target_filename or 'Körper' in target_filename or 'Corps' in target_filename or '体' in target_filename:
            return 'docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md'
        return None
    
    # For i18n paths
    parts = list(path.parts)
    if current_lang in parts:
        idx = parts.index(current_lang)
        parts[idx] = target_lang
        parts[-1] = target_filename
        return str(Path(*parts))
    
    return f'docs/i18n/{target_lang}/core/{target_filename}'


def generate_lang_links(current_path: str) -> str:
    """Generate language switcher links for a document."""
    current_lang = get_current_lang(current_path)
    links = []
    
    for lang_code, lang_name in LANG_NAMES.items():
        if lang_code == current_lang:
            continue
        target_path = get_target_path(current_path, lang_code)
        if target_path:
            rel_path = os.path.relpath(target_path, os.path.dirname(current_path))
            links.append(f'[{lang_name}]({rel_path})')
    
    return ' | '.join(links)


def switch_language(current_path: str, target_lang: str) -> Optional[str]:
    """Switch to target language version of document."""
    target_path = get_target_path(current_path, target_lang)
    
    if not target_path:
        print(f"Error: Could not determine target path for {target_lang}")
        return None
    
    if not os.path.exists(target_path):
        print(f"Warning: Target document does not exist: {target_path}")
        print(f"Consider creating the translation.")
        return target_path
    
    return target_path


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        print("\nAvailable languages:")
        for code, name in LANG_NAMES.items():
            print(f"  {code}: {name}")
        sys.exit(1)
    
    doc_path = sys.argv[1]
    
    if not os.path.exists(doc_path):
        print(f"Error: Document not found: {doc_path}")
        sys.exit(1)
    
    if len(sys.argv) >= 3:
        target_lang = sys.argv[2]
        if target_lang not in LANG_NAMES:
            print(f"Error: Unknown language code: {target_lang}")
            print(f"Available: {', '.join(LANG_CODES)}")
            sys.exit(1)
        
        result = switch_language(doc_path, target_lang)
        if result:
            print(f"Switching from {get_current_lang(doc_path)} to {target_lang}:")
            print(f"  Source: {doc_path}")
            print(f"  Target: {result}")
            
            # Generate relative link
            rel_link = os.path.relpath(result, os.path.dirname(doc_path))
            print(f"  Relative link: [{LANG_NAMES[target_lang]}]({rel_link})")
    else:
        # Show all available language versions
        current_lang = get_current_lang(doc_path)
        print(f"Current document: {doc_path}")
        print(f"Current language: {current_lang} ({LANG_NAMES.get(current_lang, 'Unknown')})")
        print("\nAvailable language versions:")
        
        for lang_code, lang_name in LANG_NAMES.items():
            if lang_code == current_lang:
                continue
            target_path = get_target_path(doc_path, lang_code)
            if target_path:
                exists = "✓" if os.path.exists(target_path) else "✗"
                print(f"  [{exists}] {lang_code} ({lang_name}): {target_path}")


if __name__ == '__main__':
    main()
