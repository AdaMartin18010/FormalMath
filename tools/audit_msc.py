import os
import re
from collections import Counter

def extract_frontmatter(path):
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        content = f.read()
    if not content.strip().startswith('---'):
        return None
    end = content.find('---', 3)
    if end == -1:
        return None
    return content[3:end].strip()

def parse_frontmatter(text):
    data = {}
    if not text:
        return data
    # Simple YAML-like parsing
    for line in text.split('\n'):
        line = line.strip()
        if ':' in line and not line.startswith('#'):
            key, val = line.split(':', 1)
            key = key.strip()
            val = val.strip().strip('"\'')
            if val.startswith('['):
                # list
                val = [v.strip().strip('"\'') for v in val.strip('[]').split(',') if v.strip()]
            data[key] = val
    return data

# Valid MSC primary pattern: 2 digits, optionally followed by letter + digits
VALID_MSC = re.compile(r'^(\d{2})([A-Z]\d{2,})?$')

def is_valid_msc(code):
    if not code or not isinstance(code, str):
        return False
    code = code.strip()
    return bool(VALID_MSC.match(code))

def main():
    base = r'G:\_src\FormalMath\docs'
    total = 0
    has_fm = 0
    has_primary = 0
    valid_primary = 0
    invalid_primary = []
    missing_primary = 0
    has_secondary = 0
    invalid_secondary = []
    
    for root, dirs, files in os.walk(base):
        for f in files:
            if not f.endswith('.md'):
                continue
            path = os.path.join(root, f)
            total += 1
            fm_text = extract_frontmatter(path)
            if fm_text is None:
                continue
            has_fm += 1
            fm = parse_frontmatter(fm_text)
            
            primary = fm.get('msc_primary', '')
            if primary:
                has_primary += 1
                if is_valid_msc(primary):
                    valid_primary += 1
                else:
                    invalid_primary.append((os.path.relpath(path, base), primary))
            else:
                missing_primary += 1
            
            secondary = fm.get('msc_secondary', [])
            if secondary:
                has_secondary += 1
                if isinstance(secondary, str):
                    secondary = [secondary]
                for s in secondary:
                    s = s.strip().rstrip(',')
                    if s and not (is_valid_msc(s) or re.match(r'^\d{2}-\d{2}$', s) or re.match(r'^\d{2}-\d{2}[A-Z]$', s)):
                        invalid_secondary.append((os.path.relpath(path, base), s))
    
    print(f"=== MSC Audit Report ===")
    print(f"Total .md files: {total}")
    print(f"Has front matter: {has_fm} ({has_fm/total*100:.1f}%)")
    print(f"Has msc_primary: {has_primary}")
    print(f"Valid primary: {valid_primary} ({valid_primary/total*100:.1f}% of total, {valid_primary/has_primary*100:.1f}% of those with primary)")
    print(f"Invalid primary ({len(invalid_primary)}):")
    for p, c in invalid_primary[:10]:
        print(f"  {p}: {c}")
    print(f"Missing primary: {missing_primary}")
    print(f"Has secondary: {has_secondary}")
    print(f"Invalid secondary entries ({len(invalid_secondary)}):")
    counts = Counter([c for _, c in invalid_secondary])
    for c, n in counts.most_common(15):
        print(f"  {c!r}: {n}")
    # Show first 10 file paths
    print("Sample files:")
    for p, c in invalid_secondary[:10]:
        print(f"  {p}: {c!r}")

if __name__ == '__main__':
    main()
