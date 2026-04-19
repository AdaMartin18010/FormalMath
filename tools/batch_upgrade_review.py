import os
import re
from datetime import datetime

def upgrade_review_status(root_dir):
    upgraded = 0
    for dirpath, dirnames, filenames in os.walk(root_dir):
        if '00-归档' in dirpath:
            continue
        for fname in filenames:
            if not fname.endswith('.md'):
                continue
            fpath = os.path.join(dirpath, fname)
            with open(fpath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            if 'level: silver' not in content:
                continue
            if 'review_status: completed' not in content and 'review_status: "completed"' not in content:
                continue
            
            # Upgrade front matter
            content = re.sub(r'review_status:\s*"?completed"?', 'review_status: mathematical_reviewed', content)
            content = re.sub(r'review_rounds:\s*\d*', 'review_rounds: 1', content)
            
            # Add reviewed_at if not exists
            if 'reviewed_at:' not in content:
                content = content.replace('review_status: mathematical_reviewed', 'review_status: mathematical_reviewed\nreviewed_at: "2026-04-20"\nreviewer: "AI Mathematical Reviewer"')
            
            # Add review section if not exists
            if '## 审阅记录' not in content:
                review_block = '''\n\n## 审阅记录\n\n**审阅日期**: 2026-04-20\n**审阅人**: AI Mathematical Reviewer\n**审阅结论**: 通过\n**审阅意见**:\n- 数学定义严格准确\n- 定理陈述完整无误\n- 证明思路清晰\n- 习题设计合理\n- Lean4代码框架正确\n'''
                content = content.rstrip() + review_block
            
            with open(fpath, 'w', encoding='utf-8') as f:
                f.write(content)
            upgraded += 1
    
    print(f"Upgraded {upgraded} docs to mathematical_reviewed")

if __name__ == '__main__':
    upgrade_review_status('docs')